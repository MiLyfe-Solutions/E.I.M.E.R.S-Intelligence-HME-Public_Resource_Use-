import V185TrunkScan21Chunk068

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_835441 : List Nat := [1, 2, 2, 2, 1, 3, 5, 1, 4]
def baseStart_835441 : Nat := 118140960795 + 835441 * 2 ^ 59
def prefixEnd_835441 : Nat := 4983230072969 + 3 ^ 40 * 835441 * 2
def baseEnd_835441 : Nat := 190659018432431585309059

theorem tailTrace_835441 : CollatzResearch.WordTrace tailWord_835441 prefixEnd_835441 190659018432431585309059 := by
  unfold tailWord_835441
  simp only [CollatzResearch.WordTrace]
  refine ⟨30471036566347413808418177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20314024377564942538945451 30471036566347413808418177)
  ·
    refine ⟨22853277424760560356313633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30471036566347413808418177 22853277424760560356313633)
    ·
      refine ⟨17139958068570420267235225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22853277424760560356313633 17139958068570420267235225)
      ·
        refine ⟨12854968551427815200426419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17139958068570420267235225 12854968551427815200426419)
        ·
          refine ⟨19282452827141722800639629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12854968551427815200426419 19282452827141722800639629)
          ·
            refine ⟨7230919810178146050239861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19282452827141722800639629 7230919810178146050239861)
            ·
              refine ⟨677898732204201192209987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7230919810178146050239861 677898732204201192209987)
              ·
                refine ⟨1016848098306301788314981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677898732204201192209987 1016848098306301788314981)
                ·
                  refine ⟨190659018432431585309059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1016848098306301788314981 190659018432431585309059)
                  ·
                    rfl

theorem cell21_835441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_835441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835441 prefixEnd_835441 := by exact prefixLift 835441
  have htrace : WordTrace (prefixWord ++ tailWord_835441) baseStart_835441 baseEnd_835441 := by
    simpa [prefixWord, tailWord_835441, baseEnd_835441] using wordTrace_append hprefix tailTrace_835441
  have hstable : (prefixWord ++ tailWord_835441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835441).length < 2 ^ (prefixWord ++ tailWord_835441).sum := by decide
  have hdescent : baseEnd_835441 < baseStart_835441 := by decide
  rcases family_descends (prefixWord ++ tailWord_835441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835478 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_835478 : Nat := 118140960795 + 835478 * 2 ^ 59
def prefixEnd_835478 : Nat := 4983230072969 + 3 ^ 40 * 835478 * 2
def baseEnd_835478 : Nat := 190667462336527743192317

theorem tailTrace_835478 : CollatzResearch.WordTrace tailWord_835478 prefixEnd_835478 190667462336527743192317 := by
  unfold tailWord_835478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1904524129200835570469693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20314924044808912751676725 1904524129200835570469693)
  ·
    refine ⟨714196548450313338926135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1904524129200835570469693 714196548450313338926135)
    ·
      refine ⟨1071294822675470008389203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 714196548450313338926135 1071294822675470008389203)
      ·
        refine ⟨1606942234013205012583805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1071294822675470008389203 1606942234013205012583805)
        ·
          refine ⟨602603337754951879718927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1606942234013205012583805 602603337754951879718927)
          ·
            refine ⟨903905006632427819578391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602603337754951879718927 903905006632427819578391)
            ·
              refine ⟨1355857509948641729367587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903905006632427819578391 1355857509948641729367587)
              ·
                refine ⟨2033786264922962594051381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355857509948641729367587 2033786264922962594051381)
                ·
                  refine ⟨190667462336527743192317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2033786264922962594051381 190667462336527743192317)
                  ·
                    rfl

theorem cell21_835478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_835478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835478 prefixEnd_835478 := by exact prefixLift 835478
  have htrace : WordTrace (prefixWord ++ tailWord_835478) baseStart_835478 baseEnd_835478 := by
    simpa [prefixWord, tailWord_835478, baseEnd_835478] using wordTrace_append hprefix tailTrace_835478
  have hstable : (prefixWord ++ tailWord_835478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835478).length < 2 ^ (prefixWord ++ tailWord_835478).sum := by decide
  have hdescent : baseEnd_835478 < baseStart_835478 := by decide
  rcases family_descends (prefixWord ++ tailWord_835478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835565 : List Nat := [1, 5, 1, 4, 1, 1, 3, 5]
def baseStart_835565 : Nat := 118140960795 + 835565 * 2 ^ 59
def prefixEnd_835565 : Nat := 4983230072969 + 3 ^ 40 * 835565 * 2
def baseEnd_835565 : Nat := 63562438973944975080713

theorem tailTrace_835565 : CollatzResearch.WordTrace tailWord_835565 prefixEnd_835565 63562438973944975080713 := by
  unfold tailWord_835565
  simp only [CollatzResearch.WordTrace]
  refine ⟨30475559217898182985932149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20317039478598788657288099 30475559217898182985932149)
  ·
    refine ⟨2857083676677954654931139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30475559217898182985932149 2857083676677954654931139)
    ·
      refine ⟨4285625515016931982396709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2857083676677954654931139 4285625515016931982396709)
      ·
        refine ⟨803554784065674746699383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4285625515016931982396709 803554784065674746699383)
        ·
          refine ⟨1205332176098512120049075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803554784065674746699383 1205332176098512120049075)
          ·
            refine ⟨1807998264147768180073613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205332176098512120049075 1807998264147768180073613)
            ·
              refine ⟨677999349055413067527605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1807998264147768180073613 677999349055413067527605)
              ·
                refine ⟨63562438973944975080713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 677999349055413067527605 63562438973944975080713)
                ·
                  rfl

theorem cell21_835565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 5].length) (baseStart_835565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835565 prefixEnd_835565 := by exact prefixLift 835565
  have htrace : WordTrace (prefixWord ++ tailWord_835565) baseStart_835565 baseEnd_835565 := by
    simpa [prefixWord, tailWord_835565, baseEnd_835565] using wordTrace_append hprefix tailTrace_835565
  have hstable : (prefixWord ++ tailWord_835565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835565).length < 2 ^ (prefixWord ++ tailWord_835565).sum := by decide
  have hdescent : baseEnd_835565 < baseStart_835565 := by decide
  rcases family_descends (prefixWord ++ tailWord_835565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835621 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 5]
def baseStart_835621 : Nat := 118140960795 + 835621 * 2 ^ 59
def prefixEnd_835621 : Nat := 4983230072969 + 3 ^ 40 * 835621 * 2
def baseEnd_835621 : Nat := 190700096884791272308691

theorem tailTrace_835621 : CollatzResearch.WordTrace tailWord_835621 prefixEnd_835621 190700096884791272308691 := by
  unfold tailWord_835621
  simp only [CollatzResearch.WordTrace]
  refine ⟨30477601705695304549970717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20318401137130203033313811 30477601705695304549970717)
  ·
    refine ⟨11429100639635739206239019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30477601705695304549970717 11429100639635739206239019)
    ·
      refine ⟨17143650959453608809358529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11429100639635739206239019 17143650959453608809358529)
      ·
        refine ⟨12857738219590206607018897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17143650959453608809358529 12857738219590206607018897)
        ·
          refine ⟨9643303664692654955264173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12857738219590206607018897 9643303664692654955264173)
          ·
            refine ⟨3616238874259745608224065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9643303664692654955264173 3616238874259745608224065)
            ·
              refine ⟨2712179155694809206168049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3616238874259745608224065 2712179155694809206168049)
              ·
                refine ⟨2034134366771106904626037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2712179155694809206168049 2034134366771106904626037)
                ·
                  refine ⟨190700096884791272308691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2034134366771106904626037 190700096884791272308691)
                  ·
                    rfl

theorem cell21_835621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_835621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835621 prefixEnd_835621 := by exact prefixLift 835621
  have htrace : WordTrace (prefixWord ++ tailWord_835621) baseStart_835621 baseEnd_835621 := by
    simpa [prefixWord, tailWord_835621, baseEnd_835621] using wordTrace_append hprefix tailTrace_835621
  have hstable : (prefixWord ++ tailWord_835621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835621).length < 2 ^ (prefixWord ++ tailWord_835621).sum := by decide
  have hdescent : baseEnd_835621 < baseStart_835621 := by decide
  rcases family_descends (prefixWord ++ tailWord_835621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835624 : List Nat := [2, 1, 5, 3, 1, 1, 1, 7]
def baseStart_835624 : Nat := 118140960795 + 835624 * 2 ^ 59
def prefixEnd_835624 : Nat := 4983230072969 + 3 ^ 40 * 835624 * 2
def baseEnd_835624 : Nat := 63566927175221311252895

theorem tailTrace_835624 : CollatzResearch.WordTrace tailWord_835624 prefixEnd_835624 63566927175221311252895 := by
  unfold tailWord_835624
  simp only [CollatzResearch.WordTrace]
  refine ⟨15238855562342218031164963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20318474083122957374886617 15238855562342218031164963)
  ·
    refine ⟨22858283343513327046747445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15238855562342218031164963 22858283343513327046747445)
    ·
      refine ⟨2142964063454374410632573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22858283343513327046747445 2142964063454374410632573)
      ·
        refine ⟨803611523795390403987215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2142964063454374410632573 803611523795390403987215)
        ·
          refine ⟨1205417285693085605980823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803611523795390403987215 1205417285693085605980823)
          ·
            refine ⟨1808125928539628408971235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205417285693085605980823 1808125928539628408971235)
            ·
              refine ⟨2712188892809442613456853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1808125928539628408971235 2712188892809442613456853)
              ·
                refine ⟨63566927175221311252895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2712188892809442613456853 63566927175221311252895)
                ·
                  rfl

theorem cell21_835624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 7].length) (baseStart_835624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835624 prefixEnd_835624 := by exact prefixLift 835624
  have htrace : WordTrace (prefixWord ++ tailWord_835624) baseStart_835624 baseEnd_835624 := by
    simpa [prefixWord, tailWord_835624, baseEnd_835624] using wordTrace_append hprefix tailTrace_835624
  have hstable : (prefixWord ++ tailWord_835624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835624).length < 2 ^ (prefixWord ++ tailWord_835624).sum := by decide
  have hdescent : baseEnd_835624 < baseStart_835624 := by decide
  rcases family_descends (prefixWord ++ tailWord_835624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835635 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 6]
def baseStart_835635 : Nat := 118140960795 + 835635 * 2 ^ 59
def prefixEnd_835635 : Nat := 4983230072969 + 3 ^ 40 * 835635 * 2
def baseEnd_835635 : Nat := 190703291875530359075329

theorem tailTrace_835635 : CollatzResearch.WordTrace tailWord_835635 prefixEnd_835635 190703291875530359075329 := by
  unfold tailWord_835635
  simp only [CollatzResearch.WordTrace]
  refine ⟨30478112327644584940980359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20318741551763056627320239 30478112327644584940980359)
  ·
    refine ⟨45717168491466877411470539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30478112327644584940980359 45717168491466877411470539)
    ·
      refine ⟨68575752737200316117205809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45717168491466877411470539 68575752737200316117205809)
      ·
        refine ⟨51431814552900237087904357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68575752737200316117205809 51431814552900237087904357)
        ·
          refine ⟨9643465228668794453982067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51431814552900237087904357 9643465228668794453982067)
          ·
            refine ⟨14465197843003191680973101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9643465228668794453982067 14465197843003191680973101)
            ·
              refine ⟨5424449191126196880364913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14465197843003191680973101 5424449191126196880364913)
              ·
                refine ⟨4068336893344647660273685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5424449191126196880364913 4068336893344647660273685)
                ·
                  refine ⟨190703291875530359075329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4068336893344647660273685 190703291875530359075329)
                  ·
                    rfl

theorem cell21_835635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_835635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835635 prefixEnd_835635 := by exact prefixLift 835635
  have htrace : WordTrace (prefixWord ++ tailWord_835635) baseStart_835635 baseEnd_835635 := by
    simpa [prefixWord, tailWord_835635, baseEnd_835635] using wordTrace_append hprefix tailTrace_835635
  have hstable : (prefixWord ++ tailWord_835635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835635).length < 2 ^ (prefixWord ++ tailWord_835635).sum := by decide
  have hdescent : baseEnd_835635 < baseStart_835635 := by decide
  rcases family_descends (prefixWord ++ tailWord_835635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835655 : List Nat := [1, 1, 4, 1, 3, 1, 5, 2, 3]
def baseStart_835655 : Nat := 118140960795 + 835655 * 2 ^ 59
def prefixEnd_835655 : Nat := 4983230072969 + 3 ^ 40 * 835655 * 2
def baseEnd_835655 : Nat := 190707856148014768741955

theorem tailTrace_835655 : CollatzResearch.WordTrace tailWord_835655 prefixEnd_835655 190707856148014768741955 := by
  unfold tailWord_835655
  simp only [CollatzResearch.WordTrace]
  refine ⟨30478841787572128356708419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20319227858381418904472279 30478841787572128356708419)
  ·
    refine ⟨45718262681358192535062629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30478841787572128356708419 45718262681358192535062629)
    ·
      refine ⟨8572174252754661100324243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45718262681358192535062629 8572174252754661100324243)
      ·
        refine ⟨12858261379131991650486365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8572174252754661100324243 12858261379131991650486365)
        ·
          refine ⟨4821848017174496868932387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12858261379131991650486365 4821848017174496868932387)
          ·
            refine ⟨7232772025761745303398581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4821848017174496868932387 7232772025761745303398581)
            ·
              refine ⟨678072377415163622193617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7232772025761745303398581 678072377415163622193617)
              ·
                refine ⟨508554283061372716645213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678072377415163622193617 508554283061372716645213)
                ·
                  refine ⟨190707856148014768741955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508554283061372716645213 190707856148014768741955)
                  ·
                    rfl

theorem cell21_835655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 3].length) (baseStart_835655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835655 prefixEnd_835655 := by exact prefixLift 835655
  have htrace : WordTrace (prefixWord ++ tailWord_835655) baseStart_835655 baseEnd_835655 := by
    simpa [prefixWord, tailWord_835655, baseEnd_835655] using wordTrace_append hprefix tailTrace_835655
  have hstable : (prefixWord ++ tailWord_835655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835655).length < 2 ^ (prefixWord ++ tailWord_835655).sum := by decide
  have hdescent : baseEnd_835655 < baseStart_835655 := by decide
  rcases family_descends (prefixWord ++ tailWord_835655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835669 : List Nat := [1, 3, 2, 2, 1, 3, 4, 1, 4]
def baseStart_835669 : Nat := 118140960795 + 835669 * 2 ^ 59
def prefixEnd_835669 : Nat := 4983230072969 + 3 ^ 40 * 835669 * 2
def baseEnd_835669 : Nat := 190711051138753855508593

theorem tailTrace_835669 : CollatzResearch.WordTrace tailWord_835669 prefixEnd_835669 190711051138753855508593 := by
  unfold tailWord_835669
  simp only [CollatzResearch.WordTrace]
  refine ⟨30479352409521408747718061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20319568273014272498478707 30479352409521408747718061)
  ·
    refine ⟨11429757153570528280394273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30479352409521408747718061 11429757153570528280394273)
    ·
      refine ⟨8572317865177896210295705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11429757153570528280394273 8572317865177896210295705)
      ·
        refine ⟨6429238398883422157721779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8572317865177896210295705 6429238398883422157721779)
        ·
          refine ⟨9643857598325133236582669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6429238398883422157721779 9643857598325133236582669)
          ·
            refine ⟨3616446599371924963718501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9643857598325133236582669 3616446599371924963718501)
            ·
              refine ⟨678083737382235930697219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3616446599371924963718501 678083737382235930697219)
              ·
                refine ⟨1017125606073353896045829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678083737382235930697219 1017125606073353896045829)
                ·
                  refine ⟨190711051138753855508593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1017125606073353896045829 190711051138753855508593)
                  ·
                    rfl

theorem cell21_835669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_835669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835669 prefixEnd_835669 := by exact prefixLift 835669
  have htrace : WordTrace (prefixWord ++ tailWord_835669) baseStart_835669 baseEnd_835669 := by
    simpa [prefixWord, tailWord_835669, baseEnd_835669] using wordTrace_append hprefix tailTrace_835669
  have hstable : (prefixWord ++ tailWord_835669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835669).length < 2 ^ (prefixWord ++ tailWord_835669).sum := by decide
  have hdescent : baseEnd_835669 < baseStart_835669 := by decide
  rcases family_descends (prefixWord ++ tailWord_835669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835810 : List Nat := [3, 3, 4, 1, 2, 1, 7]
def baseStart_835810 : Nat := 118140960795 + 835810 * 2 ^ 59
def prefixEnd_835810 : Nat := 4983230072969 + 3 ^ 40 * 835810 * 2
def baseEnd_835810 : Nat := 21193692139974327073145

theorem tailTrace_835810 : CollatzResearch.WordTrace tailWord_835810 prefixEnd_835810 21193692139974327073145 := by
  unfold tailWord_835810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7621123775502647457150221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20322996734673726552400589 7621123775502647457150221)
  ·
    refine ⟨2857921415813492796431333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7621123775502647457150221 2857921415813492796431333)
    ·
      refine ⟨535860265465029899330875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2857921415813492796431333 535860265465029899330875)
      ·
        refine ⟨803790398197544848996313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535860265465029899330875 803790398197544848996313)
        ·
          refine ⟨602842798648158636747235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803790398197544848996313 602842798648158636747235)
          ·
            refine ⟨904264197972237955120853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602842798648158636747235 904264197972237955120853)
            ·
              refine ⟨21193692139974327073145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 904264197972237955120853 21193692139974327073145)
              ·
                rfl

theorem cell21_835810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 7].length) (baseStart_835810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835810 prefixEnd_835810 := by exact prefixLift 835810
  have htrace : WordTrace (prefixWord ++ tailWord_835810) baseStart_835810 baseEnd_835810 := by
    simpa [prefixWord, tailWord_835810, baseEnd_835810] using wordTrace_append hprefix tailTrace_835810
  have hstable : (prefixWord ++ tailWord_835810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835810).length < 2 ^ (prefixWord ++ tailWord_835810).sum := by decide
  have hdescent : baseEnd_835810 < baseStart_835810 := by decide
  rcases family_descends (prefixWord ++ tailWord_835810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835877 : List Nat := [1, 3, 1, 2, 14]
def baseStart_835877 : Nat := 118140960795 + 835877 * 2 ^ 59
def prefixEnd_835877 : Nat := 4983230072969 + 3 ^ 40 * 835877 * 2
def baseEnd_835877 : Nat := 2355043451513477975821

theorem tailTrace_835877 : CollatzResearch.WordTrace tailWord_835877 prefixEnd_835877 2355043451513477975821 := by
  unfold tailWord_835877
  simp only [CollatzResearch.WordTrace]
  refine ⟨30486938792767860271289885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20324625861845240180859923 30486938792767860271289885)
  ·
    refine ⟨11432602047287947601733707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30486938792767860271289885 11432602047287947601733707)
    ·
      refine ⟨17148903070931921402600561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11432602047287947601733707 17148903070931921402600561)
      ·
        refine ⟨12861677303198941051950421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17148903070931921402600561 12861677303198941051950421)
        ·
          refine ⟨2355043451513477975821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 12861677303198941051950421 2355043451513477975821)
          ·
            rfl

theorem cell21_835877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 14].length) (baseStart_835877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835877 prefixEnd_835877 := by exact prefixLift 835877
  have htrace : WordTrace (prefixWord ++ tailWord_835877) baseStart_835877 baseEnd_835877 := by
    simpa [prefixWord, tailWord_835877, baseEnd_835877] using wordTrace_append hprefix tailTrace_835877
  have hstable : (prefixWord ++ tailWord_835877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835877).length < 2 ^ (prefixWord ++ tailWord_835877).sum := by decide
  have hdescent : baseEnd_835877 < baseStart_835877 := by decide
  rcases family_descends (prefixWord ++ tailWord_835877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835939 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 6]
def baseStart_835939 : Nat := 118140960795 + 835939 * 2 ^ 59
def prefixEnd_835939 : Nat := 4983230072969 + 3 ^ 40 * 835939 * 2
def baseEnd_835939 : Nat := 190772668817293386008041

theorem tailTrace_835939 : CollatzResearch.WordTrace tailWord_835939 prefixEnd_835939 190772668817293386008041 := by
  unfold tailWord_835939
  simp only [CollatzResearch.WordTrace]
  refine ⟨30489200118543244860046871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20326133412362163240031247 30489200118543244860046871)
  ·
    refine ⟨45733800177814867290070307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30489200118543244860046871 45733800177814867290070307)
    ·
      refine ⟨68600700266722300935105461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45733800177814867290070307 68600700266722300935105461)
      ·
        refine ⟨6431315650005215712666137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68600700266722300935105461 6431315650005215712666137)
        ·
          refine ⟨4823486737503911784499603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6431315650005215712666137 4823486737503911784499603)
          ·
            refine ⟨7235230106255867676749405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4823486737503911784499603 7235230106255867676749405)
            ·
              refine ⟨2713211289845950378781027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7235230106255867676749405 2713211289845950378781027)
              ·
                refine ⟨4069816934768925568171541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713211289845950378781027 4069816934768925568171541)
                ·
                  refine ⟨190772668817293386008041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4069816934768925568171541 190772668817293386008041)
                  ·
                    rfl

theorem cell21_835939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 6].length) (baseStart_835939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835939 prefixEnd_835939 := by exact prefixLift 835939
  have htrace : WordTrace (prefixWord ++ tailWord_835939) baseStart_835939 baseEnd_835939 := by
    simpa [prefixWord, tailWord_835939, baseEnd_835939] using wordTrace_append hprefix tailTrace_835939
  have hstable : (prefixWord ++ tailWord_835939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835939).length < 2 ^ (prefixWord ++ tailWord_835939).sum := by decide
  have hdescent : baseEnd_835939 < baseStart_835939 := by decide
  rcases family_descends (prefixWord ++ tailWord_835939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835953 : List Nat := [1, 2, 2, 2, 1, 2, 1, 10]
def baseStart_835953 : Nat := 118140960795 + 835953 * 2 ^ 59
def prefixEnd_835953 : Nat := 4983230072969 + 3 ^ 40 * 835953 * 2
def baseEnd_835953 : Nat := 63591954602677490924893

theorem tailTrace_835953 : CollatzResearch.WordTrace tailWord_835953 prefixEnd_835953 63591954602677490924893 := by
  unfold tailWord_835953
  simp only [CollatzResearch.WordTrace]
  refine ⟨30489710740492525251056513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20326473826995016834037675 30489710740492525251056513)
  ·
    refine ⟨22867283055369393938292385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30489710740492525251056513 22867283055369393938292385)
    ·
      refine ⟨17150462291527045453719289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22867283055369393938292385 17150462291527045453719289)
      ·
        refine ⟨12862846718645284090289467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17150462291527045453719289 12862846718645284090289467)
        ·
          refine ⟨19294270077967926135434201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12862846718645284090289467 19294270077967926135434201)
          ·
            refine ⟨14470702558475944601575651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19294270077967926135434201 14470702558475944601575651)
            ·
              refine ⟨21706053837713916902363477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14470702558475944601575651 21706053837713916902363477)
              ·
                refine ⟨63591954602677490924893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21706053837713916902363477 63591954602677490924893)
                ·
                  rfl

theorem cell21_835953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 10].length) (baseStart_835953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835953 prefixEnd_835953 := by exact prefixLift 835953
  have htrace : WordTrace (prefixWord ++ tailWord_835953) baseStart_835953 baseEnd_835953 := by
    simpa [prefixWord, tailWord_835953, baseEnd_835953] using wordTrace_append hprefix tailTrace_835953
  have hstable : (prefixWord ++ tailWord_835953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835953).length < 2 ^ (prefixWord ++ tailWord_835953).sum := by decide
  have hdescent : baseEnd_835953 < baseStart_835953 := by decide
  rcases family_descends (prefixWord ++ tailWord_835953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836052 : List Nat := [2, 4, 1, 2, 2, 3, 2, 2, 3]
def baseStart_836052 : Nat := 118140960795 + 836052 * 2 ^ 59
def prefixEnd_836052 : Nat := 4983230072969 + 3 ^ 40 * 836052 * 2
def baseEnd_836052 : Nat := 190798456956830300624477

theorem tailTrace_836052 : CollatzResearch.WordTrace tailWord_836052 prefixEnd_836052 190798456956830300624477 := by
  unfold tailWord_836052
  simp only [CollatzResearch.WordTrace]
  refine ⟨15246660783566932579455205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20328881044755910105940273 15246660783566932579455205)
  ·
    refine ⟨2858748896918799858647851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15246660783566932579455205 2858748896918799858647851)
    ·
      refine ⟨4288123345378199787971777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2858748896918799858647851 4288123345378199787971777)
      ·
        refine ⟨3216092509033649840978833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4288123345378199787971777 3216092509033649840978833)
        ·
          refine ⟨2412069381775237380734125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3216092509033649840978833 2412069381775237380734125)
          ·
            refine ⟨904526018165714017775297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2412069381775237380734125 904526018165714017775297)
            ·
              refine ⟨678394513624285513331473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 904526018165714017775297 678394513624285513331473)
              ·
                refine ⟨508795885218214134998605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678394513624285513331473 508795885218214134998605)
                ·
                  refine ⟨190798456956830300624477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508795885218214134998605 190798456956830300624477)
                  ·
                    rfl

theorem cell21_836052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_836052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836052 prefixEnd_836052 := by exact prefixLift 836052
  have htrace : WordTrace (prefixWord ++ tailWord_836052) baseStart_836052 baseEnd_836052 := by
    simpa [prefixWord, tailWord_836052, baseEnd_836052] using wordTrace_append hprefix tailTrace_836052
  have hstable : (prefixWord ++ tailWord_836052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836052).length < 2 ^ (prefixWord ++ tailWord_836052).sum := by decide
  have hdescent : baseEnd_836052 < baseStart_836052 := by decide
  rcases family_descends (prefixWord ++ tailWord_836052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836077 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 7]
def baseStart_836077 : Nat := 118140960795 + 836077 * 2 ^ 59
def prefixEnd_836077 : Nat := 4983230072969 + 3 ^ 40 * 836077 * 2
def baseEnd_836077 : Nat := 190804162297435812707759

theorem tailTrace_836077 : CollatzResearch.WordTrace tailWord_836077 prefixEnd_836077 190804162297435812707759 := by
  unfold tailWord_836077
  simp only [CollatzResearch.WordTrace]
  refine ⟨30494233392043294428570485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20329488928028862952380323 30494233392043294428570485)
  ·
    refine ⟨2858834380504058852678483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30494233392043294428570485 2858834380504058852678483)
    ·
      refine ⟨4288251570756088279017725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2858834380504058852678483 4288251570756088279017725)
      ·
        refine ⟨1608094339033533104631647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4288251570756088279017725 1608094339033533104631647)
        ·
          refine ⟨2412141508550299656947471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1608094339033533104631647 2412141508550299656947471)
          ·
            refine ⟨3618212262825449485421207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412141508550299656947471 3618212262825449485421207)
            ·
              refine ⟨5427318394238174228131811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3618212262825449485421207 5427318394238174228131811)
              ·
                refine ⟨8140977591357261342197717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5427318394238174228131811 8140977591357261342197717)
                ·
                  refine ⟨190804162297435812707759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8140977591357261342197717 190804162297435812707759)
                  ·
                    rfl

theorem cell21_836077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_836077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836077 prefixEnd_836077 := by exact prefixLift 836077
  have htrace : WordTrace (prefixWord ++ tailWord_836077) baseStart_836077 baseEnd_836077 := by
    simpa [prefixWord, tailWord_836077, baseEnd_836077] using wordTrace_append hprefix tailTrace_836077
  have hstable : (prefixWord ++ tailWord_836077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836077).length < 2 ^ (prefixWord ++ tailWord_836077).sum := by decide
  have hdescent : baseEnd_836077 < baseStart_836077 := by decide
  rcases family_descends (prefixWord ++ tailWord_836077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836108 : List Nat := [2, 2, 1, 2, 4, 1, 3, 2, 4]
def baseStart_836108 : Nat := 118140960795 + 836108 * 2 ^ 59
def prefixEnd_836108 : Nat := 4983230072969 + 3 ^ 40 * 836108 * 2
def baseEnd_836108 : Nat := 190811236919786647691029

theorem tailTrace_836108 : CollatzResearch.WordTrace tailWord_836108 prefixEnd_836108 190811236919786647691029 := by
  unfold tailWord_836108
  simp only [CollatzResearch.WordTrace]
  refine ⟨15247682027465493361474489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20330242703287324481965985 15247682027465493361474489)
  ·
    refine ⟨11435761520599120021105867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15247682027465493361474489 11435761520599120021105867)
    ·
      refine ⟨17153642280898680031658801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11435761520599120021105867 17153642280898680031658801)
      ·
        refine ⟨12865231710674010023744101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17153642280898680031658801 12865231710674010023744101)
        ·
          refine ⟨2412230945751376879452019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12865231710674010023744101 2412230945751376879452019)
          ·
            refine ⟨3618346418627065319178029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412230945751376879452019 3618346418627065319178029)
            ·
              refine ⟨1356879906985149494691761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3618346418627065319178029 1356879906985149494691761)
              ·
                refine ⟨1017659930238862121018821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356879906985149494691761 1017659930238862121018821)
                ·
                  refine ⟨190811236919786647691029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1017659930238862121018821 190811236919786647691029)
                  ·
                    rfl

theorem cell21_836108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_836108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836108 prefixEnd_836108 := by exact prefixLift 836108
  have htrace : WordTrace (prefixWord ++ tailWord_836108) baseStart_836108 baseEnd_836108 := by
    simpa [prefixWord, tailWord_836108, baseEnd_836108] using wordTrace_append hprefix tailTrace_836108
  have hstable : (prefixWord ++ tailWord_836108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836108).length < 2 ^ (prefixWord ++ tailWord_836108).sum := by decide
  have hdescent : baseEnd_836108 < baseStart_836108 := by decide
  rcases family_descends (prefixWord ++ tailWord_836108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836125 : List Nat := [1, 4, 2, 2, 1, 3, 3, 1, 4]
def baseStart_836125 : Nat := 118140960795 + 836125 * 2 ^ 59
def prefixEnd_836125 : Nat := 4983230072969 + 3 ^ 40 * 836125 * 2
def baseEnd_836125 : Nat := 190815116551398395907661

theorem tailTrace_836125 : CollatzResearch.WordTrace tailWord_836125 prefixEnd_836125 190815116551398395907661 := by
  unfold tailWord_836125
  simp only [CollatzResearch.WordTrace]
  refine ⟨30495984095869398626317829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20330656063912932417545219 30495984095869398626317829)
  ·
    refine ⟨5717997017975512242434593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30495984095869398626317829 5717997017975512242434593)
    ·
      refine ⟨4288497763481634181825945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5717997017975512242434593 4288497763481634181825945)
      ·
        refine ⟨3216373322611225636369459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4288497763481634181825945 3216373322611225636369459)
        ·
          refine ⟨4824559983916838454554189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3216373322611225636369459 4824559983916838454554189)
          ·
            refine ⟨1809209993968814420457821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4824559983916838454554189 1809209993968814420457821)
            ·
              refine ⟨678453747738305407671683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1809209993968814420457821 678453747738305407671683)
              ·
                refine ⟨1017680621607458111507525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678453747738305407671683 1017680621607458111507525)
                ·
                  refine ⟨190815116551398395907661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1017680621607458111507525 190815116551398395907661)
                  ·
                    rfl

theorem cell21_836125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_836125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836125 prefixEnd_836125 := by exact prefixLift 836125
  have htrace : WordTrace (prefixWord ++ tailWord_836125) baseStart_836125 baseEnd_836125 := by
    simpa [prefixWord, tailWord_836125, baseEnd_836125] using wordTrace_append hprefix tailTrace_836125
  have hstable : (prefixWord ++ tailWord_836125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836125).length < 2 ^ (prefixWord ++ tailWord_836125).sum := by decide
  have hdescent : baseEnd_836125 < baseStart_836125 := by decide
  rcases family_descends (prefixWord ++ tailWord_836125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836167 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 6]
def baseStart_836167 : Nat := 118140960795 + 836167 * 2 ^ 59
def prefixEnd_836167 : Nat := 4983230072969 + 3 ^ 40 * 836167 * 2
def baseEnd_836167 : Nat := 190824701523615656207575

theorem tailTrace_836167 : CollatzResearch.WordTrace tailWord_836167 prefixEnd_836167 190824701523615656207575 := by
  unfold tailWord_836167
  simp only [CollatzResearch.WordTrace]
  refine ⟨30497515961717239799346755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20331677307811493199564503 30497515961717239799346755)
  ·
    refine ⟨45746273942575859699020133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30497515961717239799346755 45746273942575859699020133)
    ·
      refine ⟨8577426364232973693566275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45746273942575859699020133 8577426364232973693566275)
      ·
        refine ⟨12866139546349460540349413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8577426364232973693566275 12866139546349460540349413)
        ·
          refine ⟨2412401164940523851315515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12866139546349460540349413 2412401164940523851315515)
          ·
            refine ⟨3618601747410785776973273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412401164940523851315515 3618601747410785776973273)
            ·
              refine ⟨2713951310558089332729955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3618601747410785776973273 2713951310558089332729955)
              ·
                refine ⟨4070926965837133999094933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713951310558089332729955 4070926965837133999094933)
                ·
                  refine ⟨190824701523615656207575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4070926965837133999094933 190824701523615656207575)
                  ·
                    rfl

theorem cell21_836167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 6].length) (baseStart_836167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836167 prefixEnd_836167 := by exact prefixLift 836167
  have htrace : WordTrace (prefixWord ++ tailWord_836167) baseStart_836167 baseEnd_836167 := by
    simpa [prefixWord, tailWord_836167, baseEnd_836167] using wordTrace_append hprefix tailTrace_836167
  have hstable : (prefixWord ++ tailWord_836167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836167).length < 2 ^ (prefixWord ++ tailWord_836167).sum := by decide
  have hdescent : baseEnd_836167 < baseStart_836167 := by decide
  rcases family_descends (prefixWord ++ tailWord_836167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836181 : List Nat := [1, 3, 2, 2, 1, 1, 3, 8]
def baseStart_836181 : Nat := 118140960795 + 836181 * 2 ^ 59
def prefixEnd_836181 : Nat := 4983230072969 + 3 ^ 40 * 836181 * 2
def baseEnd_836181 : Nat := 63609298838118247658071

theorem tailTrace_836181 : CollatzResearch.WordTrace tailWord_836181 prefixEnd_836181 63609298838118247658071 := by
  unfold tailWord_836181
  simp only [CollatzResearch.WordTrace]
  refine ⟨30498026583666520190356397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20332017722444346793570931 30498026583666520190356397)
  ·
    refine ⟨11436759968874945071383649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30498026583666520190356397 11436759968874945071383649)
    ·
      refine ⟨8577569976656208803537737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11436759968874945071383649 8577569976656208803537737)
      ·
        refine ⟨6433177482492156602653303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8577569976656208803537737 6433177482492156602653303)
        ·
          refine ⟨9649766223738234903979955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6433177482492156602653303 9649766223738234903979955)
          ·
            refine ⟨14474649335607352355969933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9649766223738234903979955 14474649335607352355969933)
            ·
              refine ⟨5427993500852757133488725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14474649335607352355969933 5427993500852757133488725)
              ·
                refine ⟨63609298838118247658071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5427993500852757133488725 63609298838118247658071)
                ·
                  rfl

theorem cell21_836181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 8].length) (baseStart_836181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836181 prefixEnd_836181 := by exact prefixLift 836181
  have htrace : WordTrace (prefixWord ++ tailWord_836181) baseStart_836181 baseEnd_836181 := by
    simpa [prefixWord, tailWord_836181, baseEnd_836181] using wordTrace_append hprefix tailTrace_836181
  have hstable : (prefixWord ++ tailWord_836181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836181).length < 2 ^ (prefixWord ++ tailWord_836181).sum := by decide
  have hdescent : baseEnd_836181 < baseStart_836181 := by decide
  rcases family_descends (prefixWord ++ tailWord_836181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836184 : List Nat := [2, 1, 2, 2, 1, 2, 6, 1, 4]
def baseStart_836184 : Nat := 118140960795 + 836184 * 2 ^ 59
def prefixEnd_836184 : Nat := 4983230072969 + 3 ^ 40 * 836184 * 2
def baseEnd_836184 : Nat := 190828581155227404424207

theorem tailTrace_836184 : CollatzResearch.WordTrace tailWord_836184 prefixEnd_836184 190828581155227404424207 := by
  unfold tailWord_836184
  simp only [CollatzResearch.WordTrace]
  refine ⟨15249068001327825851357803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20332090668437101135143737 15249068001327825851357803)
  ·
    refine ⟨22873602001991738777036705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15249068001327825851357803 22873602001991738777036705)
    ·
      refine ⟨17155201501493804082777529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22873602001991738777036705 17155201501493804082777529)
      ·
        refine ⟨12866401126120353062083147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17155201501493804082777529 12866401126120353062083147)
        ·
          refine ⟨19299601689180529593124721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12866401126120353062083147 19299601689180529593124721)
          ·
            refine ⟨14474701266885397194843541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19299601689180529593124721 14474701266885397194843541)
            ·
              refine ⟨678501621885252993508291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14474701266885397194843541 678501621885252993508291)
              ·
                refine ⟨1017752432827879490262437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678501621885252993508291 1017752432827879490262437)
                ·
                  refine ⟨190828581155227404424207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1017752432827879490262437 190828581155227404424207)
                  ·
                    rfl

theorem cell21_836184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_836184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836184 prefixEnd_836184 := by exact prefixLift 836184
  have htrace : WordTrace (prefixWord ++ tailWord_836184) baseStart_836184 baseEnd_836184 := by
    simpa [prefixWord, tailWord_836184, baseEnd_836184] using wordTrace_append hprefix tailTrace_836184
  have hstable : (prefixWord ++ tailWord_836184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836184).length < 2 ^ (prefixWord ++ tailWord_836184).sum := by decide
  have hdescent : baseEnd_836184 < baseStart_836184 := by decide
  rcases family_descends (prefixWord ++ tailWord_836184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836277 : List Nat := [1, 3, 3, 3, 1, 3, 1, 2, 4]
def baseStart_836277 : Nat := 118140960795 + 836277 * 2 ^ 59
def prefixEnd_836277 : Nat := 4983230072969 + 3 ^ 40 * 836277 * 2
def baseEnd_836277 : Nat := 190849805022279909374017

theorem tailTrace_836277 : CollatzResearch.WordTrace tailWord_836277 prefixEnd_836277 190849805022279909374017 := by
  unfold tailWord_836277
  simp only [CollatzResearch.WordTrace]
  refine ⟨30501527991318728585851085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20334351994212485723900723 30501527991318728585851085)
  ·
    refine ⟨11438072996744523219694157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30501527991318728585851085 11438072996744523219694157)
    ·
      refine ⟨4289277373779196207385309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11438072996744523219694157 4289277373779196207385309)
      ·
        refine ⟨1608479015167198577769491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4289277373779196207385309 1608479015167198577769491)
        ·
          refine ⟨2412718522750797866654237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1608479015167198577769491 2412718522750797866654237)
          ·
            refine ⟨904769446031549199995339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2412718522750797866654237 904769446031549199995339)
            ·
              refine ⟨1357154169047323799993009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904769446031549199995339 1357154169047323799993009)
              ·
                refine ⟨1017865626785492849994757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1357154169047323799993009 1017865626785492849994757)
                ·
                  refine ⟨190849805022279909374017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1017865626785492849994757 190849805022279909374017)
                  ·
                    rfl

theorem cell21_836277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_836277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836277 prefixEnd_836277 := by exact prefixLift 836277
  have htrace : WordTrace (prefixWord ++ tailWord_836277) baseStart_836277 baseEnd_836277 := by
    simpa [prefixWord, tailWord_836277, baseEnd_836277] using wordTrace_append hprefix tailTrace_836277
  have hstable : (prefixWord ++ tailWord_836277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836277).length < 2 ^ (prefixWord ++ tailWord_836277).sum := by decide
  have hdescent : baseEnd_836277 < baseStart_836277 := by decide
  rcases family_descends (prefixWord ++ tailWord_836277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836288 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 5]
def baseStart_836288 : Nat := 118140960795 + 836288 * 2 ^ 59
def prefixEnd_836288 : Nat := 4983230072969 + 3 ^ 40 * 836288 * 2
def baseEnd_836288 : Nat := 190852315372146334690661

theorem tailTrace_836288 : CollatzResearch.WordTrace tailWord_836288 prefixEnd_836288 190852315372146334690661 := by
  unfold tailWord_836288
  simp only [CollatzResearch.WordTrace]
  refine ⟨15250964597139438732250759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20334619462852584976334345 15250964597139438732250759)
  ·
    refine ⟨22876446895709158098376139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15250964597139438732250759 22876446895709158098376139)
    ·
      refine ⟨34314670343563737147564209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22876446895709158098376139 34314670343563737147564209)
      ·
        refine ⟨25736002757672802860673157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34314670343563737147564209 25736002757672802860673157)
        ·
          refine ⟨4825500517063650536376217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25736002757672802860673157 4825500517063650536376217)
          ·
            refine ⟨3619125387797737902282163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4825500517063650536376217 3619125387797737902282163)
            ·
              refine ⟨5428688081696606853423245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619125387797737902282163 5428688081696606853423245)
              ·
                refine ⟨2035758030636227570033717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5428688081696606853423245 2035758030636227570033717)
                ·
                  refine ⟨190852315372146334690661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2035758030636227570033717 190852315372146334690661)
                  ·
                    rfl

theorem cell21_836288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_836288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836288 prefixEnd_836288 := by exact prefixLift 836288
  have htrace : WordTrace (prefixWord ++ tailWord_836288) baseStart_836288 baseEnd_836288 := by
    simpa [prefixWord, tailWord_836288, baseEnd_836288] using wordTrace_append hprefix tailTrace_836288
  have hstable : (prefixWord ++ tailWord_836288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836288).length < 2 ^ (prefixWord ++ tailWord_836288).sum := by decide
  have hdescent : baseEnd_836288 < baseStart_836288 := by decide
  rcases family_descends (prefixWord ++ tailWord_836288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836308 : List Nat := [2, 4, 1, 3, 2, 2, 2, 5]
def baseStart_836308 : Nat := 118140960795 + 836308 * 2 ^ 59
def prefixEnd_836308 : Nat := 4983230072969 + 3 ^ 40 * 836308 * 2
def baseEnd_836308 : Nat := 63618959881543581452429

theorem tailTrace_836308 : CollatzResearch.WordTrace tailWord_836308 prefixEnd_836308 63618959881543581452429 := by
  unfold tailWord_836308
  simp only [CollatzResearch.WordTrace]
  refine ⟨15251329327103210440114789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20335105769470947253486385 15251329327103210440114789)
  ·
    refine ⟨2859624248831851957521523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15251329327103210440114789 2859624248831851957521523)
    ·
      refine ⟨4289436373247777936282285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2859624248831851957521523 4289436373247777936282285)
      ·
        refine ⟨1608538639967916726105857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4289436373247777936282285 1608538639967916726105857)
        ·
          refine ⟨1206403979975937544579393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1608538639967916726105857 1206403979975937544579393)
          ·
            refine ⟨904802984981953158434545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206403979975937544579393 904802984981953158434545)
            ·
              refine ⟨678602238736464868825909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 904802984981953158434545 678602238736464868825909)
              ·
                refine ⟨63618959881543581452429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 678602238736464868825909 63618959881543581452429)
                ·
                  rfl

theorem cell21_836308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 5].length) (baseStart_836308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836308 prefixEnd_836308 := by exact prefixLift 836308
  have htrace : WordTrace (prefixWord ++ tailWord_836308) baseStart_836308 baseEnd_836308 := by
    simpa [prefixWord, tailWord_836308, baseEnd_836308] using wordTrace_append hprefix tailTrace_836308
  have hstable : (prefixWord ++ tailWord_836308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836308).length < 2 ^ (prefixWord ++ tailWord_836308).sum := by decide
  have hdescent : baseEnd_836308 < baseStart_836308 := by decide
  rcases family_descends (prefixWord ++ tailWord_836308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836350 : List Nat := [4, 2, 2, 1, 2, 1, 1, 8]
def baseStart_836350 : Nat := 118140960795 + 836350 * 2 ^ 59
def prefixEnd_836350 : Nat := 4983230072969 + 3 ^ 40 * 836350 * 2
def baseEnd_836350 : Nat := 63622154872282668219067

theorem tailTrace_836350 : CollatzResearch.WordTrace tailWord_836350 prefixEnd_836350 63622154872282668219067 := by
  unfold tailWord_836350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3813023815006782756657313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20336127013369508035505669 3813023815006782756657313)
  ·
    refine ⟨2859767861255087067492985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3813023815006782756657313 2859767861255087067492985)
    ·
      refine ⟨2144825895941315300619739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2859767861255087067492985 2144825895941315300619739)
      ·
        refine ⟨3217238843911972950929609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2144825895941315300619739 3217238843911972950929609)
        ·
          refine ⟨2412929132933979713197207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3217238843911972950929609 2412929132933979713197207)
          ·
            refine ⟨3619393699400969569795811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412929132933979713197207 3619393699400969569795811)
            ·
              refine ⟨5429090549101454354693717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619393699400969569795811 5429090549101454354693717)
              ·
                refine ⟨63622154872282668219067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5429090549101454354693717 63622154872282668219067)
                ·
                  rfl

theorem cell21_836350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_836350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836350 prefixEnd_836350 := by exact prefixLift 836350
  have htrace : WordTrace (prefixWord ++ tailWord_836350) baseStart_836350 baseEnd_836350 := by
    simpa [prefixWord, tailWord_836350, baseEnd_836350] using wordTrace_append hprefix tailTrace_836350
  have hstable : (prefixWord ++ tailWord_836350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836350).length < 2 ^ (prefixWord ++ tailWord_836350).sum := by decide
  have hdescent : baseEnd_836350 < baseStart_836350 := by decide
  rcases family_descends (prefixWord ++ tailWord_836350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836485 : List Nat := [1, 3, 1, 1, 3, 4, 1, 7]
def baseStart_836485 : Nat := 118140960795 + 836485 * 2 ^ 59
def prefixEnd_836485 : Nat := 4983230072969 + 3 ^ 40 * 836485 * 2
def baseEnd_836485 : Nat := 63632424485372589968975

theorem tailTrace_836485 : CollatzResearch.WordTrace tailWord_836485 prefixEnd_836485 63632424485372589968975 := by
  unfold tailWord_836485
  simp only [CollatzResearch.WordTrace]
  refine ⟨30509114374565180109422909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20339409583043453406281939 30509114374565180109422909)
  ·
    refine ⟨11440917890461942541033591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30509114374565180109422909 11440917890461942541033591)
    ·
      refine ⟨17161376835692913811550387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11440917890461942541033591 17161376835692913811550387)
      ·
        refine ⟨25742065253539370717325581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17161376835692913811550387 25742065253539370717325581)
        ·
          refine ⟨9653274470077264018997093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25742065253539370717325581 9653274470077264018997093)
          ·
            refine ⟨1809988963139487003561955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9653274470077264018997093 1809988963139487003561955)
            ·
              refine ⟨2714983444709230505342933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809988963139487003561955 2714983444709230505342933)
              ·
                refine ⟨63632424485372589968975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2714983444709230505342933 63632424485372589968975)
                ·
                  rfl

theorem cell21_836485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 7].length) (baseStart_836485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836485 prefixEnd_836485 := by exact prefixLift 836485
  have htrace : WordTrace (prefixWord ++ tailWord_836485) baseStart_836485 baseEnd_836485 := by
    simpa [prefixWord, tailWord_836485, baseEnd_836485] using wordTrace_append hprefix tailTrace_836485
  have hstable : (prefixWord ++ tailWord_836485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836485).length < 2 ^ (prefixWord ++ tailWord_836485).sum := by decide
  have hdescent : baseEnd_836485 < baseStart_836485 := by decide
  rcases family_descends (prefixWord ++ tailWord_836485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836564 : List Nat := [2, 4, 1, 2, 1, 3, 2, 2, 4]
def baseStart_836564 : Nat := 118140960795 + 836564 * 2 ^ 59
def prefixEnd_836564 : Nat := 4983230072969 + 3 ^ 40 * 836564 * 2
def baseEnd_836564 : Nat := 190915302332431188090097

theorem tailTrace_836564 : CollatzResearch.WordTrace tailWord_836564 prefixEnd_836564 190915302332431188090097 := by
  unfold tailWord_836564
  simp only [CollatzResearch.WordTrace]
  refine ⟨15255997870639488300774373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20341330494185984401032497 15255997870639488300774373)
  ·
    refine ⟨2860499600744904056395195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15255997870639488300774373 2860499600744904056395195)
    ·
      refine ⟨4290749401117356084592793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2860499600744904056395195 4290749401117356084592793)
      ·
        refine ⟨3218062050838017063444595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4290749401117356084592793 3218062050838017063444595)
        ·
          refine ⟨4827093076257025595166893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3218062050838017063444595 4827093076257025595166893)
          ·
            refine ⟨1810159903596384598187585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4827093076257025595166893 1810159903596384598187585)
            ·
              refine ⟨1357619927697288448640689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1810159903596384598187585 1357619927697288448640689)
              ·
                refine ⟨1018214945772966336480517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1357619927697288448640689 1018214945772966336480517)
                ·
                  refine ⟨190915302332431188090097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1018214945772966336480517 190915302332431188090097)
                  ·
                    rfl

theorem cell21_836564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_836564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836564 prefixEnd_836564 := by exact prefixLift 836564
  have htrace : WordTrace (prefixWord ++ tailWord_836564) baseStart_836564 baseEnd_836564 := by
    simpa [prefixWord, tailWord_836564, baseEnd_836564] using wordTrace_append hprefix tailTrace_836564
  have hstable : (prefixWord ++ tailWord_836564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836564).length < 2 ^ (prefixWord ++ tailWord_836564).sum := by decide
  have hdescent : baseEnd_836564 < baseStart_836564 := by decide
  rcases family_descends (prefixWord ++ tailWord_836564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836609 : List Nat := [1, 2, 4, 1, 2, 2, 1, 5, 3]
def baseStart_836609 : Nat := 118140960795 + 836609 * 2 ^ 59
def prefixEnd_836609 : Nat := 4983230072969 + 3 ^ 40 * 836609 * 2
def baseEnd_836609 : Nat := 190925571945521109840005

theorem tailTrace_836609 : CollatzResearch.WordTrace tailWord_836609 prefixEnd_836609 190925571945521109840005 := by
  unfold tailWord_836609
  simp only [CollatzResearch.WordTrace]
  refine ⟨30513637026115949286936881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20342424684077299524624587 30513637026115949286936881)
  ·
    refine ⟨22885227769586961965202661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30513637026115949286936881 22885227769586961965202661)
    ·
      refine ⟨4290980206797555368475499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22885227769586961965202661 4290980206797555368475499)
      ·
        refine ⟨6436470310196333052713249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4290980206797555368475499 6436470310196333052713249)
        ·
          refine ⟨4827352732647249789534937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6436470310196333052713249 4827352732647249789534937)
          ·
            refine ⟨3620514549485437342151203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4827352732647249789534937 3620514549485437342151203)
            ·
              refine ⟨5430771824228156013226805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3620514549485437342151203 5430771824228156013226805)
              ·
                refine ⟨509134858521389626240013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5430771824228156013226805 509134858521389626240013)
                ·
                  refine ⟨190925571945521109840005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 509134858521389626240013 190925571945521109840005)
                  ·
                    rfl

theorem cell21_836609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 3].length) (baseStart_836609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836609 prefixEnd_836609 := by exact prefixLift 836609
  have htrace : WordTrace (prefixWord ++ tailWord_836609) baseStart_836609 baseEnd_836609 := by
    simpa [prefixWord, tailWord_836609, baseEnd_836609] using wordTrace_append hprefix tailTrace_836609
  have hstable : (prefixWord ++ tailWord_836609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836609).length < 2 ^ (prefixWord ++ tailWord_836609).sum := by decide
  have hdescent : baseEnd_836609 < baseStart_836609 := by decide
  rcases family_descends (prefixWord ++ tailWord_836609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836651 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 5]
def baseStart_836651 : Nat := 118140960795 + 836651 * 2 ^ 59
def prefixEnd_836651 : Nat := 4983230072969 + 3 ^ 40 * 836651 * 2
def baseEnd_836651 : Nat := 190935156917738370139919

theorem tailTrace_836651 : CollatzResearch.WordTrace tailWord_836651 prefixEnd_836651 190935156917738370139919 := by
  unfold tailWord_836651
  simp only [CollatzResearch.WordTrace]
  refine ⟨30515168891963790459965807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20343445927975860306643871 30515168891963790459965807)
  ·
    refine ⟨45772753337945685689948711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30515168891963790459965807 45772753337945685689948711)
    ·
      refine ⟨68659130006918528534923067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45772753337945685689948711 68659130006918528534923067)
      ·
        refine ⟨102988695010377792802384601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68659130006918528534923067 102988695010377792802384601)
        ·
          refine ⟨77241521257783344601788451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102988695010377792802384601 77241521257783344601788451)
          ·
            refine ⟨115862281886675016902682677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77241521257783344601788451 115862281886675016902682677)
            ·
              refine ⟨10862088926875782834626501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115862281886675016902682677 10862088926875782834626501)
              ·
                refine ⟨2036641673789209281492469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10862088926875782834626501 2036641673789209281492469)
                ·
                  refine ⟨190935156917738370139919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2036641673789209281492469 190935156917738370139919)
                  ·
                    rfl

theorem cell21_836651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 5].length) (baseStart_836651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836651 prefixEnd_836651 := by exact prefixLift 836651
  have htrace : WordTrace (prefixWord ++ tailWord_836651) baseStart_836651 baseEnd_836651 := by
    simpa [prefixWord, tailWord_836651, baseEnd_836651] using wordTrace_append hprefix tailTrace_836651
  have hstable : (prefixWord ++ tailWord_836651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836651).length < 2 ^ (prefixWord ++ tailWord_836651).sum := by decide
  have hdescent : baseEnd_836651 < baseStart_836651 := by decide
  rcases family_descends (prefixWord ++ tailWord_836651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836682 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_836682 : Nat := 118140960795 + 836682 * 2 ^ 59
def prefixEnd_836682 : Nat := 4983230072969 + 3 ^ 40 * 836682 * 2
def baseEnd_836682 : Nat := 190942231540089205123189

theorem tailTrace_836682 : CollatzResearch.WordTrace tailWord_836682 prefixEnd_836682 190942231540089205123189 := by
  unfold tailWord_836682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7629074888712870688586075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20344199703234321836229533 7629074888712870688586075)
  ·
    refine ⟨11443612333069306032879113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7629074888712870688586075 11443612333069306032879113)
    ·
      refine ⟨8582709249801979524659335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11443612333069306032879113 8582709249801979524659335)
      ·
        refine ⟨12874063874702969286989003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8582709249801979524659335 12874063874702969286989003)
        ·
          refine ⟨19311095812054453930483505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12874063874702969286989003 19311095812054453930483505)
          ·
            refine ⟨14483321859040840447862629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19311095812054453930483505 14483321859040840447862629)
            ·
              refine ⟨2715622848570157583974243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14483321859040840447862629 2715622848570157583974243)
              ·
                refine ⟨4073434272855236375961365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2715622848570157583974243 4073434272855236375961365)
                ·
                  refine ⟨190942231540089205123189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4073434272855236375961365 190942231540089205123189)
                  ·
                    rfl

theorem cell21_836682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_836682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836682 prefixEnd_836682 := by exact prefixLift 836682
  have htrace : WordTrace (prefixWord ++ tailWord_836682) baseStart_836682 baseEnd_836682 := by
    simpa [prefixWord, tailWord_836682, baseEnd_836682] using wordTrace_append hprefix tailTrace_836682
  have hstable : (prefixWord ++ tailWord_836682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836682).length < 2 ^ (prefixWord ++ tailWord_836682).sum := by decide
  have hdescent : baseEnd_836682 < baseStart_836682 := by decide
  rcases family_descends (prefixWord ++ tailWord_836682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836685 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 5]
def baseStart_836685 : Nat := 118140960795 + 836685 * 2 ^ 59
def prefixEnd_836685 : Nat := 4983230072969 + 3 ^ 40 * 836685 * 2
def baseEnd_836685 : Nat := 190942916180961866573183

theorem tailTrace_836685 : CollatzResearch.WordTrace tailWord_836685 prefixEnd_836685 190942916180961866573183 := by
  unfold tailWord_836685
  simp only [CollatzResearch.WordTrace]
  refine ⟨30516408973840614266703509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20344272649227076177802339 30516408973840614266703509)
  ·
    refine ⟨1430456670648778793751727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30516408973840614266703509 1430456670648778793751727)
    ·
      refine ⟨2145685005973168190627591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1430456670648778793751727 2145685005973168190627591)
      ·
        refine ⟨3218527508959752285941387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145685005973168190627591 3218527508959752285941387)
        ·
          refine ⟨4827791263439628428912081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3218527508959752285941387 4827791263439628428912081)
          ·
            refine ⟨3620843447579721321684061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4827791263439628428912081 3620843447579721321684061)
            ·
              refine ⟨1357816292842395495631523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3620843447579721321684061 1357816292842395495631523)
              ·
                refine ⟨2036724439263593243447285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357816292842395495631523 2036724439263593243447285)
                ·
                  refine ⟨190942916180961866573183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2036724439263593243447285 190942916180961866573183)
                  ·
                    rfl

theorem cell21_836685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_836685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836685 prefixEnd_836685 := by exact prefixLift 836685
  have htrace : WordTrace (prefixWord ++ tailWord_836685) baseStart_836685 baseEnd_836685 := by
    simpa [prefixWord, tailWord_836685, baseEnd_836685] using wordTrace_append hprefix tailTrace_836685
  have hstable : (prefixWord ++ tailWord_836685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836685).length < 2 ^ (prefixWord ++ tailWord_836685).sum := by decide
  have hdescent : baseEnd_836685 < baseStart_836685 := by decide
  rcases family_descends (prefixWord ++ tailWord_836685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836778 : List Nat := [3, 1, 5, 1, 1, 1, 1, 5, 3]
def baseStart_836778 : Nat := 118140960795 + 836778 * 2 ^ 59
def prefixEnd_836778 : Nat := 4983230072969 + 3 ^ 40 * 836778 * 2
def baseEnd_836778 : Nat := 190964140048014371522993

theorem tailTrace_836778 : CollatzResearch.WordTrace tailWord_836778 prefixEnd_836778 190964140048014371522993 := by
  unfold tailWord_836778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7629950240625922787459747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20346533975002460766559325 7629950240625922787459747)
  ·
    refine ⟨11444925360938884181189621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7629950240625922787459747 11444925360938884181189621)
    ·
      refine ⟨1072961752588020391986527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11444925360938884181189621 1072961752588020391986527)
      ·
        refine ⟨1609442628882030587979791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072961752588020391986527 1609442628882030587979791)
        ·
          refine ⟨2414163943323045881969687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609442628882030587979791 2414163943323045881969687)
          ·
            refine ⟨3621245914984568822954531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2414163943323045881969687 3621245914984568822954531)
            ·
              refine ⟨5431868872476853234431797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3621245914984568822954531 5431868872476853234431797)
              ·
                refine ⟨509237706794704990727981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5431868872476853234431797 509237706794704990727981)
                ·
                  refine ⟨190964140048014371522993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 509237706794704990727981 190964140048014371522993)
                  ·
                    rfl

theorem cell21_836778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_836778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836778 prefixEnd_836778 := by exact prefixLift 836778
  have htrace : WordTrace (prefixWord ++ tailWord_836778) baseStart_836778 baseEnd_836778 := by
    simpa [prefixWord, tailWord_836778, baseEnd_836778] using wordTrace_append hprefix tailTrace_836778
  have hstable : (prefixWord ++ tailWord_836778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836778).length < 2 ^ (prefixWord ++ tailWord_836778).sum := by decide
  have hdescent : baseEnd_836778 < baseStart_836778 := by decide
  rcases family_descends (prefixWord ++ tailWord_836778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836865 : List Nat := [1, 2, 4, 1, 1, 4, 2, 6]
def baseStart_836865 : Nat := 118140960795 + 836865 * 2 ^ 59
def prefixEnd_836865 : Nat := 4983230072969 + 3 ^ 40 * 836865 * 2
def baseEnd_836865 : Nat := 63661331544440517857605

theorem tailTrace_836865 : CollatzResearch.WordTrace tailWord_836865 prefixEnd_836865 63661331544440517857605 := by
  unfold tailWord_836865
  simp only [CollatzResearch.WordTrace]
  refine ⟨30522974113188505008256049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20348649408792336672170699 30522974113188505008256049)
  ·
    refine ⟨22892230584891378756192037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30522974113188505008256049 22892230584891378756192037)
    ·
      refine ⟨4292293234667133516786007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22892230584891378756192037 4292293234667133516786007)
      ·
        refine ⟨6438439852000700275179011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4292293234667133516786007 6438439852000700275179011)
        ·
          refine ⟨9657659778001050412768517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6438439852000700275179011 9657659778001050412768517)
          ·
            refine ⟨1810811208375196952394097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9657659778001050412768517 1810811208375196952394097)
            ·
              refine ⟨1358108406281397714295573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1810811208375196952394097 1358108406281397714295573)
              ·
                refine ⟨63661331544440517857605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1358108406281397714295573 63661331544440517857605)
                ·
                  rfl

theorem cell21_836865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 6].length) (baseStart_836865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836865 prefixEnd_836865 := by exact prefixLift 836865
  have htrace : WordTrace (prefixWord ++ tailWord_836865) baseStart_836865 baseEnd_836865 := by
    simpa [prefixWord, tailWord_836865, baseEnd_836865] using wordTrace_append hprefix tailTrace_836865
  have hstable : (prefixWord ++ tailWord_836865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836865).length < 2 ^ (prefixWord ++ tailWord_836865).sum := by decide
  have hdescent : baseEnd_836865 < baseStart_836865 := by decide
  rcases family_descends (prefixWord ++ tailWord_836865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836868 : List Nat := [2, 3, 2, 2, 2, 1, 4, 1, 4]
def baseStart_836868 : Nat := 118140960795 + 836868 * 2 ^ 59
def prefixEnd_836868 : Nat := 4983230072969 + 3 ^ 40 * 836868 * 2
def baseEnd_836868 : Nat := 190984679274194215022809

theorem tailTrace_836868 : CollatzResearch.WordTrace tailWord_836868 prefixEnd_836868 190984679274194215022809 := by
  unfold tailWord_836868
  simp only [CollatzResearch.WordTrace]
  refine ⟨15261541766088818260307629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20348722354785091013743505 15261541766088818260307629)
  ·
    refine ⟨5723078162283306847615361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15261541766088818260307629 5723078162283306847615361)
    ·
      refine ⟨4292308621712480135711521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5723078162283306847615361 4292308621712480135711521)
      ·
        refine ⟨3219231466284360101783641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4292308621712480135711521 3219231466284360101783641)
        ·
          refine ⟨2414423599713270076337731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3219231466284360101783641 2414423599713270076337731)
          ·
            refine ⟨3621635399569905114506597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2414423599713270076337731 3621635399569905114506597)
            ·
              refine ⟨679056637419357208969987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3621635399569905114506597 679056637419357208969987)
              ·
                refine ⟨1018584956129035813454981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679056637419357208969987 1018584956129035813454981)
                ·
                  refine ⟨190984679274194215022809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1018584956129035813454981 190984679274194215022809)
                  ·
                    rfl

theorem cell21_836868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_836868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836868 prefixEnd_836868 := by exact prefixLift 836868
  have htrace : WordTrace (prefixWord ++ tailWord_836868) baseStart_836868 baseEnd_836868 := by
    simpa [prefixWord, tailWord_836868, baseEnd_836868] using wordTrace_append hprefix tailTrace_836868
  have hstable : (prefixWord ++ tailWord_836868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836868).length < 2 ^ (prefixWord ++ tailWord_836868).sum := by decide
  have hdescent : baseEnd_836868 < baseStart_836868 := by decide
  rcases family_descends (prefixWord ++ tailWord_836868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836913 : List Nat := [1, 2, 2, 3, 3, 2, 1, 4, 3]
def baseStart_836913 : Nat := 118140960795 + 836913 * 2 ^ 59
def prefixEnd_836913 : Nat := 4983230072969 + 3 ^ 40 * 836913 * 2
def baseEnd_836913 : Nat := 190994948887284136772717

theorem tailTrace_836913 : CollatzResearch.WordTrace tailWord_836913 prefixEnd_836913 190994948887284136772717 := by
  unfold tailWord_836913
  simp only [CollatzResearch.WordTrace]
  refine ⟨30524724817014609206003393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20349816544676406137335595 30524724817014609206003393)
  ·
    refine ⟨22893543612760956904502545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30524724817014609206003393 22893543612760956904502545)
    ·
      refine ⟨17170157709570717678376909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22893543612760956904502545 17170157709570717678376909)
      ·
        refine ⟨6438809141089019129391341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17170157709570717678376909 6438809141089019129391341)
        ·
          refine ⟨2414553427908382173521753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6438809141089019129391341 2414553427908382173521753)
          ·
            refine ⟨1810915070931286630141315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2414553427908382173521753 1810915070931286630141315)
            ·
              refine ⟨2716372606396929945211973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810915070931286630141315 2716372606396929945211973)
              ·
                refine ⟨509319863699424364727245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2716372606396929945211973 509319863699424364727245)
                ·
                  refine ⟨190994948887284136772717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 509319863699424364727245 190994948887284136772717)
                  ·
                    rfl

theorem cell21_836913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 3].length) (baseStart_836913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836913 prefixEnd_836913 := by exact prefixLift 836913
  have htrace : WordTrace (prefixWord ++ tailWord_836913) baseStart_836913 baseEnd_836913 := by
    simpa [prefixWord, tailWord_836913, baseEnd_836913] using wordTrace_append hprefix tailTrace_836913
  have hstable : (prefixWord ++ tailWord_836913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836913).length < 2 ^ (prefixWord ++ tailWord_836913).sum := by decide
  have hdescent : baseEnd_836913 < baseStart_836913 := by decide
  rcases family_descends (prefixWord ++ tailWord_836913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836972 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 5]
def baseStart_836972 : Nat := 118140960795 + 836972 * 2 ^ 59
def prefixEnd_836972 : Nat := 4983230072969 + 3 ^ 40 * 836972 * 2
def baseEnd_836972 : Nat := 191008413491113145289263

theorem tailTrace_836972 : CollatzResearch.WordTrace tailWord_836972 prefixEnd_836972 191008413491113145289263 := by
  unfold tailWord_836972
  simp only [CollatzResearch.WordTrace]
  refine ⟨15263438361900431141200585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20351251149200574854934113 15263438361900431141200585)
  ·
    refine ⟨11447578771425323355900439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15263438361900431141200585 11447578771425323355900439)
    ·
      refine ⟨17171368157137985033850659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11447578771425323355900439 17171368157137985033850659)
      ·
        refine ⟨25757052235706977550775989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17171368157137985033850659 25757052235706977550775989)
        ·
          refine ⟨2414723647097529145385249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25757052235706977550775989 2414723647097529145385249)
          ·
            refine ⟨1811042735323146859038937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2414723647097529145385249 1811042735323146859038937)
            ·
              refine ⟨1358282051492360144279203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1811042735323146859038937 1358282051492360144279203)
              ·
                refine ⟨2037423077238540216418805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358282051492360144279203 2037423077238540216418805)
                ·
                  refine ⟨191008413491113145289263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2037423077238540216418805 191008413491113145289263)
                  ·
                    rfl

theorem cell21_836972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_836972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_836972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_836972 prefixEnd_836972 := by exact prefixLift 836972
  have htrace : WordTrace (prefixWord ++ tailWord_836972) baseStart_836972 baseEnd_836972 := by
    simpa [prefixWord, tailWord_836972, baseEnd_836972] using wordTrace_append hprefix tailTrace_836972
  have hstable : (prefixWord ++ tailWord_836972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836972).length < 2 ^ (prefixWord ++ tailWord_836972).sum := by decide
  have hdescent : baseEnd_836972 < baseStart_836972 := by decide
  rcases family_descends (prefixWord ++ tailWord_836972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837037 : List Nat := [1, 5, 2, 2, 1, 3, 2, 1, 4]
def baseStart_837037 : Nat := 118140960795 + 837037 * 2 ^ 59
def prefixEnd_837037 : Nat := 4983230072969 + 3 ^ 40 * 837037 * 2
def baseEnd_837037 : Nat := 191023247376687476705797

theorem tailTrace_837037 : CollatzResearch.WordTrace tailWord_837037 prefixEnd_837037 191023247376687476705797 := by
  unfold tailWord_837037
  simp only [CollatzResearch.WordTrace]
  refine ⟨30529247468565378383517365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20352831645710252255678243 30529247468565378383517365)
  ·
    refine ⟨2862116950178004223454753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30529247468565378383517365 2862116950178004223454753)
    ·
      refine ⟨2146587712633503167591065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2862116950178004223454753 2146587712633503167591065)
      ·
        refine ⟨1609940784475127375693299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2146587712633503167591065 1609940784475127375693299)
        ·
          refine ⟨2414911176712691063539949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609940784475127375693299 2414911176712691063539949)
          ·
            refine ⟨905591691267259148827481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2414911176712691063539949 905591691267259148827481)
            ·
              refine ⟨679193768450444361620611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905591691267259148827481 679193768450444361620611)
              ·
                refine ⟨1018790652675666542430917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679193768450444361620611 1018790652675666542430917)
                ·
                  refine ⟨191023247376687476705797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1018790652675666542430917 191023247376687476705797)
                  ·
                    rfl

theorem cell21_837037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_837037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837037 prefixEnd_837037 := by exact prefixLift 837037
  have htrace : WordTrace (prefixWord ++ tailWord_837037) baseStart_837037 baseEnd_837037 := by
    simpa [prefixWord, tailWord_837037, baseEnd_837037] using wordTrace_append hprefix tailTrace_837037
  have hstable : (prefixWord ++ tailWord_837037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837037).length < 2 ^ (prefixWord ++ tailWord_837037).sum := by decide
  have hdescent : baseEnd_837037 < baseStart_837037 := by decide
  rcases family_descends (prefixWord ++ tailWord_837037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837076 : List Nat := [2, 4, 1, 2, 12]
def baseStart_837076 : Nat := 118140960795 + 837076 * 2 ^ 59
def prefixEnd_837076 : Nat := 4983230072969 + 3 ^ 40 * 837076 * 2
def baseEnd_837076 : Nat := 2358421576642371303157

theorem tailTrace_837076 : CollatzResearch.WordTrace tailWord_837076 prefixEnd_837076 2358421576642371303157 := by
  unfold tailWord_837076
  simp only [CollatzResearch.WordTrace]
  refine ⟨15265334957712044022093541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20353779943616058696124721 15265334957712044022093541)
  ·
    refine ⟨2862250304571008254142539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15265334957712044022093541 2862250304571008254142539)
    ·
      refine ⟨4293375456856512381213809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2862250304571008254142539 4293375456856512381213809)
      ·
        refine ⟨3220031592642384285910357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4293375456856512381213809 3220031592642384285910357)
        ·
          refine ⟨2358421576642371303157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3220031592642384285910357 2358421576642371303157)
          ·
            rfl

theorem cell21_837076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 12].length) (baseStart_837076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837076 prefixEnd_837076 := by exact prefixLift 837076
  have htrace : WordTrace (prefixWord ++ tailWord_837076) baseStart_837076 baseEnd_837076 := by
    simpa [prefixWord, tailWord_837076, baseEnd_837076] using wordTrace_append hprefix tailTrace_837076
  have hstable : (prefixWord ++ tailWord_837076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837076).length < 2 ^ (prefixWord ++ tailWord_837076).sum := by decide
  have hdescent : baseEnd_837076 < baseStart_837076 := by decide
  rcases family_descends (prefixWord ++ tailWord_837076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837082 : List Nat := [3, 1, 1, 2, 3, 4, 2, 2, 3]
def baseStart_837082 : Nat := 118140960795 + 837082 * 2 ^ 59
def prefixEnd_837082 : Nat := 4983230072969 + 3 ^ 40 * 837082 * 2
def baseEnd_837082 : Nat := 191033516989777398455705

theorem tailTrace_837082 : CollatzResearch.WordTrace tailWord_837082 prefixEnd_837082 191033516989777398455705 := by
  unfold tailWord_837082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7632722188350587767226375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20353925835601567379270333 7632722188350587767226375)
  ·
    refine ⟨11449083282525881650839563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7632722188350587767226375 11449083282525881650839563)
    ·
      refine ⟨17173624923788822476259345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11449083282525881650839563 17173624923788822476259345)
      ·
        refine ⟨12880218692841616857194509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17173624923788822476259345 12880218692841616857194509)
        ·
          refine ⟨4830082009815606321447941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12880218692841616857194509 4830082009815606321447941)
          ·
            refine ⟨905640376840426185271489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4830082009815606321447941 905640376840426185271489)
            ·
              refine ⟨679230282630319638953617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905640376840426185271489 679230282630319638953617)
              ·
                refine ⟨509422711972739729215213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679230282630319638953617 509422711972739729215213)
                ·
                  refine ⟨191033516989777398455705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 509422711972739729215213 191033516989777398455705)
                  ·
                    rfl

theorem cell21_837082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_837082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837082 prefixEnd_837082 := by exact prefixLift 837082
  have htrace : WordTrace (prefixWord ++ tailWord_837082) baseStart_837082 baseEnd_837082 := by
    simpa [prefixWord, tailWord_837082, baseEnd_837082] using wordTrace_append hprefix tailTrace_837082
  have hstable : (prefixWord ++ tailWord_837082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837082).length < 2 ^ (prefixWord ++ tailWord_837082).sum := by decide
  have hdescent : baseEnd_837082 < baseStart_837082 := by decide
  rcases family_descends (prefixWord ++ tailWord_837082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837093 : List Nat := [1, 3, 1, 5, 1, 1, 3, 6]
def baseStart_837093 : Nat := 118140960795 + 837093 * 2 ^ 59
def prefixEnd_837093 : Nat := 4983230072969 + 3 ^ 40 * 837093 * 2
def baseEnd_837093 : Nat := 63678675779881274590783

theorem tailTrace_837093 : CollatzResearch.WordTrace tailWord_837093 prefixEnd_837093 63678675779881274590783 := by
  unfold tailWord_837093
  simp only [CollatzResearch.WordTrace]
  refine ⟨30531289956362499947555933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20354193304241666631703955 30531289956362499947555933)
  ·
    refine ⟨11449233733635937480333475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30531289956362499947555933 11449233733635937480333475)
    ·
      refine ⟨17173850600453906220500213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11449233733635937480333475 17173850600453906220500213)
      ·
        refine ⟨1610048493792553708171895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17173850600453906220500213 1610048493792553708171895)
        ·
          refine ⟨2415072740688830562257843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610048493792553708171895 2415072740688830562257843)
          ·
            refine ⟨3622609111033245843386765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415072740688830562257843 3622609111033245843386765)
            ·
              refine ⟨1358478416637467191270037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3622609111033245843386765 1358478416637467191270037)
              ·
                refine ⟨63678675779881274590783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1358478416637467191270037 63678675779881274590783)
                ·
                  rfl

theorem cell21_837093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 6].length) (baseStart_837093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837093 prefixEnd_837093 := by exact prefixLift 837093
  have htrace : WordTrace (prefixWord ++ tailWord_837093) baseStart_837093 baseEnd_837093 := by
    simpa [prefixWord, tailWord_837093, baseEnd_837093] using wordTrace_append hprefix tailTrace_837093
  have hstable : (prefixWord ++ tailWord_837093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837093).length < 2 ^ (prefixWord ++ tailWord_837093).sum := by decide
  have hdescent : baseEnd_837093 < baseStart_837093 := by decide
  rcases family_descends (prefixWord ++ tailWord_837093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837110 : List Nat := [5, 1, 1, 1, 2, 3, 3, 5]
def baseStart_837110 : Nat := 118140960795 + 837110 * 2 ^ 59
def prefixEnd_837110 : Nat := 4983230072969 + 3 ^ 40 * 837110 * 2
def baseEnd_837110 : Nat := 63679968990418523996327

theorem tailTrace_837110 : CollatzResearch.WordTrace tailWord_837110 prefixEnd_837110 63679968990418523996327 := by
  unfold tailWord_837110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908244374831306990682799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20354606664867274567283189 1908244374831306990682799)
  ·
    refine ⟨2862366562246960486024199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1908244374831306990682799 2862366562246960486024199)
    ·
      refine ⟨4293549843370440729036299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2862366562246960486024199 4293549843370440729036299)
      ·
        refine ⟨6440324765055661093554449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4293549843370440729036299 6440324765055661093554449)
        ·
          refine ⟨4830243573791745820165837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6440324765055661093554449 4830243573791745820165837)
          ·
            refine ⟨1811341340171904682562189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4830243573791745820165837 1811341340171904682562189)
            ·
              refine ⟨679253002564464255960821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1811341340171904682562189 679253002564464255960821)
              ·
                refine ⟨63679968990418523996327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 679253002564464255960821 63679968990418523996327)
                ·
                  rfl

theorem cell21_837110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_837110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837110 prefixEnd_837110 := by exact prefixLift 837110
  have htrace : WordTrace (prefixWord ++ tailWord_837110) baseStart_837110 baseEnd_837110 := by
    simpa [prefixWord, tailWord_837110, baseEnd_837110] using wordTrace_append hprefix tailTrace_837110
  have hstable : (prefixWord ++ tailWord_837110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837110).length < 2 ^ (prefixWord ++ tailWord_837110).sum := by decide
  have hdescent : baseEnd_837110 < baseStart_837110 := by decide
  rcases family_descends (prefixWord ++ tailWord_837110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837242 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_837242 : Nat := 118140960795 + 837242 * 2 ^ 59
def prefixEnd_837242 : Nat := 4983230072969 + 3 ^ 40 * 837242 * 2
def baseEnd_837242 : Nat := 191070031169652675788711

theorem tailTrace_837242 : CollatzResearch.WordTrace tailWord_837242 prefixEnd_837242 191070031169652675788711 := by
  unfold tailWord_837242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7634181108205674598682495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20357816288548465596486653 7634181108205674598682495)
  ·
    refine ⟨11451271662308511898023743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7634181108205674598682495 11451271662308511898023743)
    ·
      refine ⟨17176907493462767847035615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11451271662308511898023743 17176907493462767847035615)
      ·
        refine ⟨25765361240194151770553423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17176907493462767847035615 25765361240194151770553423)
        ·
          refine ⟨38648041860291227655830135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25765361240194151770553423 38648041860291227655830135)
          ·
            refine ⟨57972062790436841483745203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38648041860291227655830135 57972062790436841483745203)
            ·
              refine ⟨86958094185655262225617805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57972062790436841483745203 86958094185655262225617805)
              ·
                refine ⟨32609285319620723334606677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86958094185655262225617805 32609285319620723334606677)
                ·
                  refine ⟨191070031169652675788711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32609285319620723334606677 191070031169652675788711)
                  ·
                    rfl

theorem cell21_837242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_837242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837242 prefixEnd_837242 := by exact prefixLift 837242
  have htrace : WordTrace (prefixWord ++ tailWord_837242) baseStart_837242 baseEnd_837242 := by
    simpa [prefixWord, tailWord_837242, baseEnd_837242] using wordTrace_append hprefix tailTrace_837242
  have hstable : (prefixWord ++ tailWord_837242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837242).length < 2 ^ (prefixWord ++ tailWord_837242).sum := by decide
  have hdescent : baseEnd_837242 < baseStart_837242 := by decide
  rcases family_descends (prefixWord ++ tailWord_837242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837276 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 5]
def baseStart_837276 : Nat := 118140960795 + 837276 * 2 ^ 59
def prefixEnd_837276 : Nat := 4983230072969 + 3 ^ 40 * 837276 * 2
def baseEnd_837276 : Nat := 191077790432876172221975

theorem tailTrace_837276 : CollatzResearch.WordTrace tailWord_837276 prefixEnd_837276 191077790432876172221975 := by
  unfold tailWord_837276
  simp only [CollatzResearch.WordTrace]
  refine ⟨15268982257349761100733841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20358643009799681467645121 15268982257349761100733841)
  ·
    refine ⟨11451736693012320825550381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15268982257349761100733841 11451736693012320825550381)
    ·
      refine ⟨4294401259879620309581393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11451736693012320825550381 4294401259879620309581393)
      ·
        refine ⟨3220800944909715232186045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4294401259879620309581393 3220800944909715232186045)
        ·
          refine ⟨1207800354341143212069767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3220800944909715232186045 1207800354341143212069767)
          ·
            refine ⟨1811700531511714818104651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207800354341143212069767 1811700531511714818104651)
            ·
              refine ⟨2717550797267572227156977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811700531511714818104651 2717550797267572227156977)
              ·
                refine ⟨2038163097950679170367733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2717550797267572227156977 2038163097950679170367733)
                ·
                  refine ⟨191077790432876172221975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2038163097950679170367733 191077790432876172221975)
                  ·
                    rfl

theorem cell21_837276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_837276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837276 prefixEnd_837276 := by exact prefixLift 837276
  have htrace : WordTrace (prefixWord ++ tailWord_837276) baseStart_837276 baseEnd_837276 := by
    simpa [prefixWord, tailWord_837276, baseEnd_837276] using wordTrace_append hprefix tailTrace_837276
  have hstable : (prefixWord ++ tailWord_837276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837276).length < 2 ^ (prefixWord ++ tailWord_837276).sum := by decide
  have hdescent : baseEnd_837276 < baseStart_837276 := by decide
  rcases family_descends (prefixWord ++ tailWord_837276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837293 : List Nat := [1, 5, 2, 1, 1, 1, 4, 3, 3]
def baseStart_837293 : Nat := 118140960795 + 837293 * 2 ^ 59
def prefixEnd_837293 : Nat := 4983230072969 + 3 ^ 40 * 837293 * 2
def baseEnd_837293 : Nat := 191081670064487920438607

theorem tailTrace_837293 : CollatzResearch.WordTrace tailWord_837293 prefixEnd_837293 191081670064487920438607 := by
  unfold tailWord_837293
  simp only [CollatzResearch.WordTrace]
  refine ⟨30538584555637934104836533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20359056370425289403224355 30538584555637934104836533)
  ·
    refine ⟨2862992302091056322328425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30538584555637934104836533 2862992302091056322328425)
    ·
      refine ⟨2147244226568292241746319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2862992302091056322328425 2147244226568292241746319)
      ·
        refine ⟨3220866339852438362619479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2147244226568292241746319 3220866339852438362619479)
        ·
          refine ⟨4831299509778657543929219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3220866339852438362619479 4831299509778657543929219)
          ·
            refine ⟨7246949264667986315893829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4831299509778657543929219 7246949264667986315893829)
            ·
              refine ⟨1358802987125247434230093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7246949264667986315893829 1358802987125247434230093)
              ·
                refine ⟨509551120171967787836285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1358802987125247434230093 509551120171967787836285)
                ·
                  refine ⟨191081670064487920438607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 509551120171967787836285 191081670064487920438607)
                  ·
                    rfl

theorem cell21_837293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_837293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837293 prefixEnd_837293 := by exact prefixLift 837293
  have htrace : WordTrace (prefixWord ++ tailWord_837293) baseStart_837293 baseEnd_837293 := by
    simpa [prefixWord, tailWord_837293, baseEnd_837293] using wordTrace_append hprefix tailTrace_837293
  have hstable : (prefixWord ++ tailWord_837293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837293).length < 2 ^ (prefixWord ++ tailWord_837293).sum := by decide
  have hdescent : baseEnd_837293 < baseStart_837293 := by decide
  rcases family_descends (prefixWord ++ tailWord_837293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837324 : List Nat := [2, 2, 1, 5, 2, 1, 3, 1, 4]
def baseStart_837324 : Nat := 118140960795 + 837324 * 2 ^ 59
def prefixEnd_837324 : Nat := 4983230072969 + 3 ^ 40 * 837324 * 2
def baseEnd_837324 : Nat := 191088744686838755421877

theorem tailTrace_837324 : CollatzResearch.WordTrace tailWord_837324 prefixEnd_837324 191088744686838755421877 := by
  unfold tailWord_837324
  simp only [CollatzResearch.WordTrace]
  refine ⟨15269857609262813199607513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20359810145683750932810017 15269857609262813199607513)
  ·
    refine ⟨11452393206947109899705635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15269857609262813199607513 11452393206947109899705635)
    ·
      refine ⟨17178589810420664849558453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11452393206947109899705635 17178589810420664849558453)
      ·
        refine ⟨1610492794726937329646105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17178589810420664849558453 1610492794726937329646105)
        ·
          refine ⟨1207869596045202997234579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1610492794726937329646105 1207869596045202997234579)
          ·
            refine ⟨1811804394067804495851869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207869596045202997234579 1811804394067804495851869)
            ·
              refine ⟨679426647775426685944451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1811804394067804495851869 679426647775426685944451)
              ·
                refine ⟨1019139971663140028916677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679426647775426685944451 1019139971663140028916677)
                ·
                  refine ⟨191088744686838755421877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1019139971663140028916677 191088744686838755421877)
                  ·
                    rfl

theorem cell21_837324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_837324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837324 prefixEnd_837324 := by exact prefixLift 837324
  have htrace : WordTrace (prefixWord ++ tailWord_837324) baseStart_837324 baseEnd_837324 := by
    simpa [prefixWord, tailWord_837324, baseEnd_837324] using wordTrace_append hprefix tailTrace_837324
  have hstable : (prefixWord ++ tailWord_837324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837324).length < 2 ^ (prefixWord ++ tailWord_837324).sum := by decide
  have hdescent : baseEnd_837324 < baseStart_837324 := by decide
  rcases family_descends (prefixWord ++ tailWord_837324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837349 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 8]
def baseStart_837349 : Nat := 118140960795 + 837349 * 2 ^ 59
def prefixEnd_837349 : Nat := 4983230072969 + 3 ^ 40 * 837349 * 2
def baseEnd_837349 : Nat := 191094450027444267505159

theorem tailTrace_837349 : CollatzResearch.WordTrace tailWord_837349 prefixEnd_837349 191094450027444267505159 := by
  unfold tailWord_837349
  simp only [CollatzResearch.WordTrace]
  refine ⟨30540627043435055668875101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20360418028956703779250067 30540627043435055668875101)
  ·
    refine ⟨11452735141288145875828163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30540627043435055668875101 11452735141288145875828163)
    ·
      refine ⟨17179102711932218813742245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11452735141288145875828163 17179102711932218813742245)
      ·
        refine ⟨3221081758487291027576671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17179102711932218813742245 3221081758487291027576671)
        ·
          refine ⟨4831622637730936541365007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3221081758487291027576671 4831622637730936541365007)
          ·
            refine ⟨7247433956596404812047511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4831622637730936541365007 7247433956596404812047511)
            ·
              refine ⟨10871150934894607218071267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7247433956596404812047511 10871150934894607218071267)
              ·
                refine ⟨16306726402341910827106901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10871150934894607218071267 16306726402341910827106901)
                ·
                  refine ⟨191094450027444267505159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16306726402341910827106901 191094450027444267505159)
                  ·
                    rfl

theorem cell21_837349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_837349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837349 prefixEnd_837349 := by exact prefixLift 837349
  have htrace : WordTrace (prefixWord ++ tailWord_837349) baseStart_837349 baseEnd_837349 := by
    simpa [prefixWord, tailWord_837349, baseEnd_837349] using wordTrace_append hprefix tailTrace_837349
  have hstable : (prefixWord ++ tailWord_837349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837349).length < 2 ^ (prefixWord ++ tailWord_837349).sum := by decide
  have hdescent : baseEnd_837349 < baseStart_837349 := by decide
  rcases family_descends (prefixWord ++ tailWord_837349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837363 : List Nat := [1, 1, 1, 2, 2, 3, 11]
def baseStart_837363 : Nat := 118140960795 + 837363 * 2 ^ 59
def prefixEnd_837363 : Nat := 4983230072969 + 3 ^ 40 * 837363 * 2
def baseEnd_837363 : Nat := 21233071668687039363533

theorem tailTrace_837363 : CollatzResearch.WordTrace tailWord_837363 prefixEnd_837363 21233071668687039363533 := by
  unfold tailWord_837363
  simp only [CollatzResearch.WordTrace]
  refine ⟨30541137665384336059884743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20360758443589557373256495 30541137665384336059884743)
  ·
    refine ⟨45811706498076504089827115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30541137665384336059884743 45811706498076504089827115)
    ·
      refine ⟨68717559747114756134740673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45811706498076504089827115 68717559747114756134740673)
      ·
        refine ⟨51538169810336067101055505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68717559747114756134740673 51538169810336067101055505)
        ·
          refine ⟨38653627357752050325791629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51538169810336067101055505 38653627357752050325791629)
          ·
            refine ⟨14495110259157018872171861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38653627357752050325791629 14495110259157018872171861)
            ·
              refine ⟨21233071668687039363533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14495110259157018872171861 21233071668687039363533)
              ·
                rfl

theorem cell21_837363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 11].length) (baseStart_837363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837363 prefixEnd_837363 := by exact prefixLift 837363
  have htrace : WordTrace (prefixWord ++ tailWord_837363) baseStart_837363 baseEnd_837363 := by
    simpa [prefixWord, tailWord_837363, baseEnd_837363] using wordTrace_append hprefix tailTrace_837363
  have hstable : (prefixWord ++ tailWord_837363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837363).length < 2 ^ (prefixWord ++ tailWord_837363).sum := by decide
  have hdescent : baseEnd_837363 < baseStart_837363 := by decide
  rcases family_descends (prefixWord ++ tailWord_837363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837366 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_837366 : Nat := 118140960795 + 837366 * 2 ^ 59
def prefixEnd_837366 : Nat := 4983230072969 + 3 ^ 40 * 837366 * 2
def baseEnd_837366 : Nat := 191098329659056015721791

theorem tailTrace_837366 : CollatzResearch.WordTrace tailWord_837366 prefixEnd_837366 191098329659056015721791 := by
  unfold tailWord_837366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908827942773341723265247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20360831389582311714829301 1908827942773341723265247)
  ·
    refine ⟨2863241914160012584897871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1908827942773341723265247 2863241914160012584897871)
    ·
      refine ⟨4294862871240018877346807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2863241914160012584897871 4294862871240018877346807)
      ·
        refine ⟨6442294306860028316020211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294862871240018877346807 6442294306860028316020211)
        ·
          refine ⟨9663441460290042474030317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6442294306860028316020211 9663441460290042474030317)
          ·
            refine ⟨3623790547608765927761369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9663441460290042474030317 3623790547608765927761369)
            ·
              refine ⟨2717842910706574445821027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3623790547608765927761369 2717842910706574445821027)
              ·
                refine ⟨4076764366059861668731541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2717842910706574445821027 4076764366059861668731541)
                ·
                  refine ⟨191098329659056015721791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4076764366059861668731541 191098329659056015721791)
                  ·
                    rfl

theorem cell21_837366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_837366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837366 prefixEnd_837366 := by exact prefixLift 837366
  have htrace : WordTrace (prefixWord ++ tailWord_837366) baseStart_837366 baseEnd_837366 := by
    simpa [prefixWord, tailWord_837366, baseEnd_837366] using wordTrace_append hprefix tailTrace_837366
  have hstable : (prefixWord ++ tailWord_837366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837366).length < 2 ^ (prefixWord ++ tailWord_837366).sum := by decide
  have hdescent : baseEnd_837366 < baseStart_837366 := by decide
  rcases family_descends (prefixWord ++ tailWord_837366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837380 : List Nat := [2, 3, 2, 2, 1, 2, 1, 8]
def baseStart_837380 : Nat := 118140960795 + 837380 * 2 ^ 59
def prefixEnd_837380 : Nat := 4983230072969 + 3 ^ 40 * 837380 * 2
def baseEnd_837380 : Nat := 63700508216598367496143

theorem tailTrace_837380 : CollatzResearch.WordTrace tailWord_837380 prefixEnd_837380 63700508216598367496143 := by
  unfold tailWord_837380
  simp only [CollatzResearch.WordTrace]
  refine ⟨15270878853161373981626797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20361171804215165308835729 15270878853161373981626797)
  ·
    refine ⟨5726579569935515243110049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15270878853161373981626797 5726579569935515243110049)
    ·
      refine ⟨4294934677451636432332537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5726579569935515243110049 4294934677451636432332537)
      ·
        refine ⟨3221201008088727324249403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4294934677451636432332537 3221201008088727324249403)
        ·
          refine ⟨4831801512133090986374105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3221201008088727324249403 4831801512133090986374105)
          ·
            refine ⟨3623851134099818239780579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4831801512133090986374105 3623851134099818239780579)
            ·
              refine ⟨5435776701149727359670869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3623851134099818239780579 5435776701149727359670869)
              ·
                refine ⟨63700508216598367496143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5435776701149727359670869 63700508216598367496143)
                ·
                  rfl

theorem cell21_837380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_837380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837380 prefixEnd_837380 := by exact prefixLift 837380
  have htrace : WordTrace (prefixWord ++ tailWord_837380) baseStart_837380 baseEnd_837380 := by
    simpa [prefixWord, tailWord_837380, baseEnd_837380] using wordTrace_append hprefix tailTrace_837380
  have hstable : (prefixWord ++ tailWord_837380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837380).length < 2 ^ (prefixWord ++ tailWord_837380).sum := by decide
  have hdescent : baseEnd_837380 < baseStart_837380 := by decide
  rcases family_descends (prefixWord ++ tailWord_837380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837383 : List Nat := [1, 1, 4, 4, 2, 1, 1, 3, 4]
def baseStart_837383 : Nat := 118140960795 + 837383 * 2 ^ 59
def prefixEnd_837383 : Nat := 4983230072969 + 3 ^ 40 * 837383 * 2
def baseEnd_837383 : Nat := 191102209290667763938423

theorem tailTrace_837383 : CollatzResearch.WordTrace tailWord_837383 prefixEnd_837383 191102209290667763938423 := by
  unfold tailWord_837383
  simp only [CollatzResearch.WordTrace]
  refine ⟨30541867125311879475612803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20361244750207919650408535 30541867125311879475612803)
  ·
    refine ⟨45812800687967819213419205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30541867125311879475612803 45812800687967819213419205)
    ·
      refine ⟨8589900128993966102516101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45812800687967819213419205 8589900128993966102516101)
      ·
        refine ⟨1610606274186368644221769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8589900128993966102516101 1610606274186368644221769)
        ·
          refine ⟨1207954705639776483166327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1610606274186368644221769 1207954705639776483166327)
          ·
            refine ⟨1811932058459664724749491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207954705639776483166327 1811932058459664724749491)
            ·
              refine ⟨2717898087689497087124237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811932058459664724749491 2717898087689497087124237)
              ·
                refine ⟨1019211782883561407671589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2717898087689497087124237 1019211782883561407671589)
                ·
                  refine ⟨191102209290667763938423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1019211782883561407671589 191102209290667763938423)
                  ·
                    rfl

theorem cell21_837383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 4].length) (baseStart_837383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837383 prefixEnd_837383 := by exact prefixLift 837383
  have htrace : WordTrace (prefixWord ++ tailWord_837383) baseStart_837383 baseEnd_837383 := by
    simpa [prefixWord, tailWord_837383, baseEnd_837383] using wordTrace_append hprefix tailTrace_837383
  have hstable : (prefixWord ++ tailWord_837383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837383).length < 2 ^ (prefixWord ++ tailWord_837383).sum := by decide
  have hdescent : baseEnd_837383 < baseStart_837383 := by decide
  rcases family_descends (prefixWord ++ tailWord_837383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837476 : List Nat := [2, 3, 1, 1, 6, 1, 1, 2, 4]
def baseStart_837476 : Nat := 118140960795 + 837476 * 2 ^ 59
def prefixEnd_837476 : Nat := 4983230072969 + 3 ^ 40 * 837476 * 2
def baseEnd_837476 : Nat := 191123433157720268888233

theorem tailTrace_837476 : CollatzResearch.WordTrace tailWord_837476 prefixEnd_837476 191123433157720268888233 := by
  unfold tailWord_837476
  simp only [CollatzResearch.WordTrace]
  refine ⟨15272629556987478179374141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20363506075983304239165521 15272629556987478179374141)
  ·
    refine ⟨5727236083870304317265303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15272629556987478179374141 5727236083870304317265303)
    ·
      refine ⟨8590854125805456475897955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5727236083870304317265303 8590854125805456475897955)
      ·
        refine ⟨12886281188708184713846933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8590854125805456475897955 12886281188708184713846933)
        ·
          refine ⟨604044430720696158461575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12886281188708184713846933 604044430720696158461575)
          ·
            refine ⟨906066646081044237692363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604044430720696158461575 906066646081044237692363)
            ·
              refine ⟨1359099969121566356538545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906066646081044237692363 1359099969121566356538545)
              ·
                refine ⟨1019324976841174767403909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359099969121566356538545 1019324976841174767403909)
                ·
                  refine ⟨191123433157720268888233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1019324976841174767403909 191123433157720268888233)
                  ·
                    rfl

theorem cell21_837476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_837476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837476 prefixEnd_837476 := by exact prefixLift 837476
  have htrace : WordTrace (prefixWord ++ tailWord_837476) baseStart_837476 baseEnd_837476 := by
    simpa [prefixWord, tailWord_837476, baseEnd_837476] using wordTrace_append hprefix tailTrace_837476
  have hstable : (prefixWord ++ tailWord_837476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837476).length < 2 ^ (prefixWord ++ tailWord_837476).sum := by decide
  have hdescent : baseEnd_837476 < baseStart_837476 := by decide
  rcases family_descends (prefixWord ++ tailWord_837476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837532 : List Nat := [2, 2, 3, 3, 1, 1, 9]
def baseStart_837532 : Nat := 118140960795 + 837532 * 2 ^ 59
def prefixEnd_837532 : Nat := 4983230072969 + 3 ^ 40 * 837532 * 2
def baseEnd_837532 : Nat := 21237357013408512883865

theorem tailTrace_837532 : CollatzResearch.WordTrace tailWord_837532 prefixEnd_837532 21237357013408512883865 := by
  unfold tailWord_837532
  simp only [CollatzResearch.WordTrace]
  refine ⟨15273650800886038961393425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20364867734514718615191233 15273650800886038961393425)
  ·
    refine ⟨11455238100664529221045069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15273650800886038961393425 11455238100664529221045069)
    ·
      refine ⟨4295714287749198457891901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11455238100664529221045069 4295714287749198457891901)
      ·
        refine ⟨1610892857905949421709463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4295714287749198457891901 1610892857905949421709463)
        ·
          refine ⟨2416339286858924132564195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610892857905949421709463 2416339286858924132564195)
          ·
            refine ⟨3624508930288386198846293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416339286858924132564195 3624508930288386198846293)
            ·
              refine ⟨21237357013408512883865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3624508930288386198846293 21237357013408512883865)
              ·
                rfl

theorem cell21_837532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 9].length) (baseStart_837532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837532 prefixEnd_837532 := by exact prefixLift 837532
  have htrace : WordTrace (prefixWord ++ tailWord_837532) baseStart_837532 baseEnd_837532 := by
    simpa [prefixWord, tailWord_837532, baseEnd_837532] using wordTrace_append hprefix tailTrace_837532
  have hstable : (prefixWord ++ tailWord_837532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837532).length < 2 ^ (prefixWord ++ tailWord_837532).sum := by decide
  have hdescent : baseEnd_837532 < baseStart_837532 := by decide
  rcases family_descends (prefixWord ++ tailWord_837532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837538 : List Nat := [3, 3, 1, 2, 3, 1, 3, 2, 3]
def baseStart_837538 : Nat := 118140960795 + 837538 * 2 ^ 59
def prefixEnd_837538 : Nat := 4983230072969 + 3 ^ 40 * 837538 * 2
def baseEnd_837538 : Nat := 191137582402421938854773

theorem tailTrace_837538 : CollatzResearch.WordTrace tailWord_837538 prefixEnd_837538 191137582402421938854773 := by
  unfold tailWord_837538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636880109937585236876317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20365013626500227298336845 7636880109937585236876317)
  ·
    refine ⟨2863830041226594463828619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7636880109937585236876317 2863830041226594463828619)
    ·
      refine ⟨4295745061839891695742929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2863830041226594463828619 4295745061839891695742929)
      ·
        refine ⟨3221808796379918771807197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4295745061839891695742929 3221808796379918771807197)
        ·
          refine ⟨1208178298642469539427699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3221808796379918771807197 1208178298642469539427699)
          ·
            refine ⟨1812267447963704309141549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208178298642469539427699 1812267447963704309141549)
            ·
              refine ⟨679600292986389115928081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1812267447963704309141549 679600292986389115928081)
              ·
                refine ⟨509700219739791836946061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679600292986389115928081 509700219739791836946061)
                ·
                  refine ⟨191137582402421938854773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 509700219739791836946061 191137582402421938854773)
                  ·
                    rfl

theorem cell21_837538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_837538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837538 prefixEnd_837538 := by exact prefixLift 837538
  have htrace : WordTrace (prefixWord ++ tailWord_837538) baseStart_837538 baseEnd_837538 := by
    simpa [prefixWord, tailWord_837538, baseEnd_837538] using wordTrace_append hprefix tailTrace_837538
  have hstable : (prefixWord ++ tailWord_837538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837538).length < 2 ^ (prefixWord ++ tailWord_837538).sum := by decide
  have hdescent : baseEnd_837538 < baseStart_837538 := by decide
  rcases family_descends (prefixWord ++ tailWord_837538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837597 : List Nat := [1, 4, 3, 1, 3, 1, 1, 4, 3]
def baseStart_837597 : Nat := 118140960795 + 837597 * 2 ^ 59
def prefixEnd_837597 : Nat := 4983230072969 + 3 ^ 40 * 837597 * 2
def baseEnd_837597 : Nat := 191151047006250947371319

theorem tailTrace_837597 : CollatzResearch.WordTrace tailWord_837597 prefixEnd_837597 191151047006250947371319 := by
  unfold tailWord_837597
  simp only [CollatzResearch.WordTrace]
  refine ⟨30549672346536594023903045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20366448231024396015935363 30549672346536594023903045)
  ·
    refine ⟨5728063564975611379481821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30549672346536594023903045 5728063564975611379481821)
    ·
      refine ⟨2148023836865854267305683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5728063564975611379481821 2148023836865854267305683)
      ·
        refine ⟨3222035755298781400958525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2148023836865854267305683 3222035755298781400958525)
        ·
          refine ⟨1208263408237043025359447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3222035755298781400958525 1208263408237043025359447)
          ·
            refine ⟨1812395112355564538039171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208263408237043025359447 1812395112355564538039171)
            ·
              refine ⟨2718592668533346807058757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812395112355564538039171 2718592668533346807058757)
              ·
                refine ⟨509736125350002526323517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2718592668533346807058757 509736125350002526323517)
                ·
                  refine ⟨191151047006250947371319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 509736125350002526323517 191151047006250947371319)
                  ·
                    rfl

theorem cell21_837597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_837597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837597 prefixEnd_837597 := by exact prefixLift 837597
  have htrace : WordTrace (prefixWord ++ tailWord_837597) baseStart_837597 baseEnd_837597 := by
    simpa [prefixWord, tailWord_837597, baseEnd_837597] using wordTrace_append hprefix tailTrace_837597
  have hstable : (prefixWord ++ tailWord_837597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837597).length < 2 ^ (prefixWord ++ tailWord_837597).sum := by decide
  have hdescent : baseEnd_837597 < baseStart_837597 := by decide
  rcases family_descends (prefixWord ++ tailWord_837597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837667 : List Nat := [1, 1, 1, 4, 3, 1, 2, 8]
def baseStart_837667 : Nat := 118140960795 + 837667 * 2 ^ 59
def prefixEnd_837667 : Nat := 4983230072969 + 3 ^ 40 * 837667 * 2
def baseEnd_837667 : Nat := 63722340653315460401503

theorem tailTrace_837667 : CollatzResearch.WordTrace tailWord_837667 prefixEnd_837667 63722340653315460401503 := by
  unfold tailWord_837667
  simp only [CollatzResearch.WordTrace]
  refine ⟨30552225456282995978951255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20368150304188663985967503 30552225456282995978951255)
  ·
    refine ⟨45828338184424493968426883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30552225456282995978951255 45828338184424493968426883)
    ·
      refine ⟨68742507276636740952640325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45828338184424493968426883 68742507276636740952640325)
      ·
        refine ⟨12889220114369388928620061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68742507276636740952640325 12889220114369388928620061)
        ·
          refine ⟨4833457542888520848232523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12889220114369388928620061 4833457542888520848232523)
          ·
            refine ⟨7250186314332781272348785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4833457542888520848232523 7250186314332781272348785)
            ·
              refine ⟨5437639735749585954261589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7250186314332781272348785 5437639735749585954261589)
              ·
                refine ⟨63722340653315460401503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5437639735749585954261589 63722340653315460401503)
                ·
                  rfl

theorem cell21_837667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 8].length) (baseStart_837667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837667 prefixEnd_837667 := by exact prefixLift 837667
  have htrace : WordTrace (prefixWord ++ tailWord_837667) baseStart_837667 baseEnd_837667 := by
    simpa [prefixWord, tailWord_837667, baseEnd_837667] using wordTrace_append hprefix tailTrace_837667
  have hstable : (prefixWord ++ tailWord_837667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837667).length < 2 ^ (prefixWord ++ tailWord_837667).sum := by decide
  have hdescent : baseEnd_837667 < baseStart_837667 := by decide
  rcases family_descends (prefixWord ++ tailWord_837667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837718 : List Nat := [5, 2, 2, 1, 1, 2, 2, 6]
def baseStart_837718 : Nat := 118140960795 + 837718 * 2 ^ 59
def prefixEnd_837718 : Nat := 4983230072969 + 3 ^ 40 * 837718 * 2
def baseEnd_837718 : Nat := 63726220284927208618135

theorem tailTrace_837718 : CollatzResearch.WordTrace tailWord_837718 prefixEnd_837718 63726220284927208618135 := by
  unfold tailWord_837718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909630348693639480566113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20369390386065487792705205 1909630348693639480566113)
  ·
    refine ⟨1432222761520229610424585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1909630348693639480566113 1432222761520229610424585)
    ·
      refine ⟨1074167071140172207818439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1432222761520229610424585 1074167071140172207818439)
      ·
        refine ⟨1611250606710258311727659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074167071140172207818439 1611250606710258311727659)
        ·
          refine ⟨2416875910065387467591489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611250606710258311727659 2416875910065387467591489)
          ·
            refine ⟨1812656932549040600693617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2416875910065387467591489 1812656932549040600693617)
            ·
              refine ⟨1359492699411780450520213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812656932549040600693617 1359492699411780450520213)
              ·
                refine ⟨63726220284927208618135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1359492699411780450520213 63726220284927208618135)
                ·
                  rfl

theorem cell21_837718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_837718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837718 prefixEnd_837718 := by exact prefixLift 837718
  have htrace : WordTrace (prefixWord ++ tailWord_837718) baseStart_837718 baseEnd_837718 := by
    simpa [prefixWord, tailWord_837718, baseEnd_837718] using wordTrace_append hprefix tailTrace_837718
  have hstable : (prefixWord ++ tailWord_837718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837718).length < 2 ^ (prefixWord ++ tailWord_837718).sum := by decide
  have hdescent : baseEnd_837718 < baseStart_837718 := by decide
  rcases family_descends (prefixWord ++ tailWord_837718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837743 : List Nat := [1, 1, 2, 1, 3, 4, 2, 7]
def baseStart_837743 : Nat := 118140960795 + 837743 * 2 ^ 59
def prefixEnd_837743 : Nat := 4983230072969 + 3 ^ 40 * 837743 * 2
def baseEnd_837743 : Nat := 63728122065129045979229

theorem tailTrace_837743 : CollatzResearch.WordTrace tailWord_837743 prefixEnd_837743 63728122065129045979229 := by
  unfold tailWord_837743
  simp only [CollatzResearch.WordTrace]
  refine ⟨30554997404007660958717883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20369998269338440639145255 30554997404007660958717883)
  ·
    refine ⟨45832496106011491438076825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30554997404007660958717883 45832496106011491438076825)
    ·
      refine ⟨34374372079508618578557619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45832496106011491438076825 34374372079508618578557619)
      ·
        refine ⟨51561558119262927867836429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34374372079508618578557619 51561558119262927867836429)
        ·
          refine ⟨19335584294723597950438661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51561558119262927867836429 19335584294723597950438661)
          ·
            refine ⟨3625422055260674615707249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19335584294723597950438661 3625422055260674615707249)
            ·
              refine ⟨2719066541445505961780437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3625422055260674615707249 2719066541445505961780437)
              ·
                refine ⟨63728122065129045979229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2719066541445505961780437 63728122065129045979229)
                ·
                  rfl

theorem cell21_837743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 7].length) (baseStart_837743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837743 prefixEnd_837743 := by exact prefixLift 837743
  have htrace : WordTrace (prefixWord ++ tailWord_837743) baseStart_837743 baseEnd_837743 := by
    simpa [prefixWord, tailWord_837743, baseEnd_837743] using wordTrace_append hprefix tailTrace_837743
  have hstable : (prefixWord ++ tailWord_837743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837743).length < 2 ^ (prefixWord ++ tailWord_837743).sum := by decide
  have hdescent : baseEnd_837743 < baseStart_837743 := by decide
  rcases family_descends (prefixWord ++ tailWord_837743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837791 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 5]
def baseStart_837791 : Nat := 118140960795 + 837791 * 2 ^ 59
def prefixEnd_837791 : Nat := 4983230072969 + 3 ^ 40 * 837791 * 2
def baseEnd_837791 : Nat := 191195320449349721137589

theorem tailTrace_837791 : CollatzResearch.WordTrace tailWord_837791 prefixEnd_837791 191195320449349721137589 := by
  unfold tailWord_837791
  simp only [CollatzResearch.WordTrace]
  refine ⟨30556748107833765156465227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20371165405222510104310151 30556748107833765156465227)
  ·
    refine ⟨45835122161750647734697841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30556748107833765156465227 45835122161750647734697841)
    ·
      refine ⟨34376341621312985801023381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45835122161750647734697841 34376341621312985801023381)
      ·
        refine ⟨1611391013499046209422971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34376341621312985801023381 1611391013499046209422971)
        ·
          refine ⟨2417086520248569314134457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611391013499046209422971 2417086520248569314134457)
          ·
            refine ⟨1812814890186426985600843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2417086520248569314134457 1812814890186426985600843)
            ·
              refine ⟨2719222335279640478401265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812814890186426985600843 2719222335279640478401265)
              ·
                refine ⟨2039416751459730358800949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2719222335279640478401265 2039416751459730358800949)
                ·
                  refine ⟨191195320449349721137589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2039416751459730358800949 191195320449349721137589)
                  ·
                    rfl

theorem cell21_837791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 5].length) (baseStart_837791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837791 prefixEnd_837791 := by exact prefixLift 837791
  have htrace : WordTrace (prefixWord ++ tailWord_837791) baseStart_837791 baseEnd_837791 := by
    simpa [prefixWord, tailWord_837791, baseEnd_837791] using wordTrace_append hprefix tailTrace_837791
  have hstable : (prefixWord ++ tailWord_837791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837791).length < 2 ^ (prefixWord ++ tailWord_837791).sum := by decide
  have hdescent : baseEnd_837791 < baseStart_837791 := by decide
  rcases family_descends (prefixWord ++ tailWord_837791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837822 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_837822 : Nat := 118140960795 + 837822 * 2 ^ 59
def prefixEnd_837822 : Nat := 4983230072969 + 3 ^ 40 * 837822 * 2
def baseEnd_837822 : Nat := 191202395071700556120859

theorem tailTrace_837822 : CollatzResearch.WordTrace tailWord_837822 prefixEnd_837822 191202395071700556120859 := by
  unfold tailWord_837822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3819734846340182181355465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20371919180480971633895813 3819734846340182181355465)
  ·
    refine ⟨2864801134755136636016599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3819734846340182181355465 2864801134755136636016599)
    ·
      refine ⟨4297201702132704954024899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2864801134755136636016599 4297201702132704954024899)
      ·
        refine ⟨6445802553199057431037349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4297201702132704954024899 6445802553199057431037349)
        ·
          refine ⟨1208587978724823268319503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6445802553199057431037349 1208587978724823268319503)
          ·
            refine ⟨1812881968087234902479255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208587978724823268319503 1812881968087234902479255)
            ·
              refine ⟨2719322952130852353718883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812881968087234902479255 2719322952130852353718883)
              ·
                refine ⟨4078984428196278530578325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719322952130852353718883 4078984428196278530578325)
                ·
                  refine ⟨191202395071700556120859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4078984428196278530578325 191202395071700556120859)
                  ·
                    rfl

theorem cell21_837822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_837822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837822 prefixEnd_837822 := by exact prefixLift 837822
  have htrace : WordTrace (prefixWord ++ tailWord_837822) baseStart_837822 baseEnd_837822 := by
    simpa [prefixWord, tailWord_837822, baseEnd_837822] using wordTrace_append hprefix tailTrace_837822
  have hstable : (prefixWord ++ tailWord_837822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837822).length < 2 ^ (prefixWord ++ tailWord_837822).sum := by decide
  have hdescent : baseEnd_837822 < baseStart_837822 := by decide
  rcases family_descends (prefixWord ++ tailWord_837822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837850 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_837850 : Nat := 118140960795 + 837850 * 2 ^ 59
def prefixEnd_837850 : Nat := 4983230072969 + 3 ^ 40 * 837850 * 2
def baseEnd_837850 : Nat := 191208785053178729654135

theorem tailTrace_837850 : CollatzResearch.WordTrace tailWord_837850 prefixEnd_837850 191208785053178729654135 := by
  unfold tailWord_837850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7639725003655004558215751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20372600009746678821908669 7639725003655004558215751)
  ·
    refine ⟨11459587505482506837323627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7639725003655004558215751 11459587505482506837323627)
    ·
      refine ⟨17189381258223760255985441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11459587505482506837323627 17189381258223760255985441)
      ·
        refine ⟨12892035943667820191989081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17189381258223760255985441 12892035943667820191989081)
        ·
          refine ⟨9669026957750865143991811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12892035943667820191989081 9669026957750865143991811)
          ·
            refine ⟨14503540436626297715987717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9669026957750865143991811 14503540436626297715987717)
            ·
              refine ⟨2719413831867430821747697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14503540436626297715987717 2719413831867430821747697)
              ·
                refine ⟨2039560373900573116310773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2719413831867430821747697 2039560373900573116310773)
                ·
                  refine ⟨191208785053178729654135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2039560373900573116310773 191208785053178729654135)
                  ·
                    rfl

theorem cell21_837850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_837850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837850 prefixEnd_837850 := by exact prefixLift 837850
  have htrace : WordTrace (prefixWord ++ tailWord_837850) baseStart_837850 baseEnd_837850 := by
    simpa [prefixWord, tailWord_837850, baseEnd_837850] using wordTrace_append hprefix tailTrace_837850
  have hstable : (prefixWord ++ tailWord_837850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837850).length < 2 ^ (prefixWord ++ tailWord_837850).sum := by decide
  have hdescent : baseEnd_837850 < baseStart_837850 := by decide
  rcases family_descends (prefixWord ++ tailWord_837850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837853 : List Nat := [1, 4, 3, 2, 1, 1, 4, 5]
def baseStart_837853 : Nat := 118140960795 + 837853 * 2 ^ 59
def prefixEnd_837853 : Nat := 4983230072969 + 3 ^ 40 * 837853 * 2
def baseEnd_837853 : Nat := 63736489898017130368043

theorem tailTrace_837853 : CollatzResearch.WordTrace tailWord_837853 prefixEnd_837853 63736489898017130368043 := by
  unfold tailWord_837853
  simp only [CollatzResearch.WordTrace]
  refine ⟨30559009433609149745222213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20372672955739433163481475 30559009433609149745222213)
  ·
    refine ⟨5729814268801715577229165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30559009433609149745222213 5729814268801715577229165)
    ·
      refine ⟨2148680350800643341460937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5729814268801715577229165 2148680350800643341460937)
      ·
        refine ⟨1611510263100482506095703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2148680350800643341460937 1611510263100482506095703)
        ·
          refine ⟨2417265394650723759143555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611510263100482506095703 2417265394650723759143555)
          ·
            refine ⟨3625898091976085638715333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417265394650723759143555 3625898091976085638715333)
            ·
              refine ⟨679855892245516057259125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3625898091976085638715333 679855892245516057259125)
              ·
                refine ⟨63736489898017130368043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 679855892245516057259125 63736489898017130368043)
                ·
                  rfl

theorem cell21_837853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 5].length) (baseStart_837853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837853 prefixEnd_837853 := by exact prefixLift 837853
  have htrace : WordTrace (prefixWord ++ tailWord_837853) baseStart_837853 baseEnd_837853 := by
    simpa [prefixWord, tailWord_837853, baseEnd_837853] using wordTrace_append hprefix tailTrace_837853
  have hstable : (prefixWord ++ tailWord_837853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837853).length < 2 ^ (prefixWord ++ tailWord_837853).sum := by decide
  have hdescent : baseEnd_837853 < baseStart_837853 := by decide
  rcases family_descends (prefixWord ++ tailWord_837853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837898 : List Nat := [3, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_837898 : Nat := 118140960795 + 837898 * 2 ^ 59
def prefixEnd_837898 : Nat := 4983230072969 + 3 ^ 40 * 837898 * 2
def baseEnd_837898 : Nat := 191219739307141312854037

theorem tailTrace_837898 : CollatzResearch.WordTrace tailWord_837898 prefixEnd_837898 191219739307141312854037 := by
  unfold tailWord_837898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7640162679611530607652587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20373767145630748287073565 7640162679611530607652587)
  ·
    refine ⟨11460244019417295911478881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7640162679611530607652587 11460244019417295911478881)
    ·
      refine ⟨8595183014562971933609161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11460244019417295911478881 8595183014562971933609161)
      ·
        refine ⟨6446387260922228950206871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8595183014562971933609161 6446387260922228950206871)
        ·
          refine ⟨9669580891383343425310307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6446387260922228950206871 9669580891383343425310307)
          ·
            refine ⟨14504371337075015137965461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9669580891383343425310307 14504371337075015137965461)
            ·
              refine ⟨679892406425391334592131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14504371337075015137965461 679892406425391334592131)
              ·
                refine ⟨1019838609638087001888197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679892406425391334592131 1019838609638087001888197)
                ·
                  refine ⟨191219739307141312854037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1019838609638087001888197 191219739307141312854037)
                  ·
                    rfl

theorem cell21_837898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_837898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_837898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_837898 prefixEnd_837898 := by exact prefixLift 837898
  have htrace : WordTrace (prefixWord ++ tailWord_837898) baseStart_837898 baseEnd_837898 := by
    simpa [prefixWord, tailWord_837898, baseEnd_837898] using wordTrace_append hprefix tailTrace_837898
  have hstable : (prefixWord ++ tailWord_837898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837898).length < 2 ^ (prefixWord ++ tailWord_837898).sum := by decide
  have hdescent : baseEnd_837898 < baseStart_837898 := by decide
  rcases family_descends (prefixWord ++ tailWord_837898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838002 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_838002 : Nat := 118140960795 + 838002 * 2 ^ 59
def prefixEnd_838002 : Nat := 4983230072969 + 3 ^ 40 * 838002 * 2
def baseEnd_838002 : Nat := 191243473524060243120491

theorem tailTrace_838002 : CollatzResearch.WordTrace tailWord_838002 prefixEnd_838002 191243473524060243120491 := by
  unfold tailWord_838002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7641110977517337048099065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20376295940046232128264173 7641110977517337048099065)
  ·
    refine ⟨5730833233138002786074299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7641110977517337048099065 5730833233138002786074299)
    ·
      refine ⟨8596249849707004179111449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5730833233138002786074299 8596249849707004179111449)
      ·
        refine ⟨6447187387280253134333587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8596249849707004179111449 6447187387280253134333587)
        ·
          refine ⟨9670781080920379701500381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6447187387280253134333587 9670781080920379701500381)
          ·
            refine ⟨3626542905345142388062643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9670781080920379701500381 3626542905345142388062643)
            ·
              refine ⟨5439814358017713582093965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3626542905345142388062643 5439814358017713582093965)
              ·
                refine ⟨2039930384256642593285237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5439814358017713582093965 2039930384256642593285237)
                ·
                  refine ⟨191243473524060243120491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2039930384256642593285237 191243473524060243120491)
                  ·
                    rfl

theorem cell21_838002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_838002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838002 prefixEnd_838002 := by exact prefixLift 838002
  have htrace : WordTrace (prefixWord ++ tailWord_838002) baseStart_838002 baseEnd_838002 := by
    simpa [prefixWord, tailWord_838002, baseEnd_838002] using wordTrace_append hprefix tailTrace_838002
  have hstable : (prefixWord ++ tailWord_838002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838002).length < 2 ^ (prefixWord ++ tailWord_838002).sum := by decide
  have hdescent : baseEnd_838002 < baseStart_838002 := by decide
  rcases family_descends (prefixWord ++ tailWord_838002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838078 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_838078 : Nat := 118140960795 + 838078 * 2 ^ 59
def prefixEnd_838078 : Nat := 4983230072969 + 3 ^ 40 * 838078 * 2
def baseEnd_838078 : Nat := 191260817759500999853669

theorem tailTrace_838078 : CollatzResearch.WordTrace tailWord_838078 prefixEnd_838078 191260817759500999853669 := by
  unfold tailWord_838078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3820901982224251646520361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20378143905196008781441925 3820901982224251646520361)
  ·
    refine ⟨2865676486668188734890271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3820901982224251646520361 2865676486668188734890271)
    ·
      refine ⟨4298514730002283102335407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2865676486668188734890271 4298514730002283102335407)
      ·
        refine ⟨6447772095003424653503111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4298514730002283102335407 6447772095003424653503111)
        ·
          refine ⟨9671658142505136980254667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6447772095003424653503111 9671658142505136980254667)
          ·
            refine ⟨14507487213757705470382001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9671658142505136980254667 14507487213757705470382001)
            ·
              refine ⟨10880615410318279102786501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14507487213757705470382001 10880615410318279102786501)
              ·
                refine ⟨2040115389434677331772469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10880615410318279102786501 2040115389434677331772469)
                ·
                  refine ⟨191260817759500999853669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2040115389434677331772469 191260817759500999853669)
                  ·
                    rfl

theorem cell21_838078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_838078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838078 prefixEnd_838078 := by exact prefixLift 838078
  have htrace : WordTrace (prefixWord ++ tailWord_838078) baseStart_838078 baseEnd_838078 := by
    simpa [prefixWord, tailWord_838078, baseEnd_838078] using wordTrace_append hprefix tailTrace_838078
  have hstable : (prefixWord ++ tailWord_838078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838078).length < 2 ^ (prefixWord ++ tailWord_838078).sum := by decide
  have hdescent : baseEnd_838078 < baseStart_838078 := by decide
  rcases family_descends (prefixWord ++ tailWord_838078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838137 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 7]
def baseStart_838137 : Nat := 118140960795 + 838137 * 2 ^ 59
def prefixEnd_838137 : Nat := 4983230072969 + 3 ^ 40 * 838137 * 2
def baseEnd_838137 : Nat := 191274282363330008370215

theorem tailTrace_838137 : CollatzResearch.WordTrace tailWord_838137 prefixEnd_838137 191274282363330008370215 := by
  unfold tailWord_838137
  simp only [CollatzResearch.WordTrace]
  refine ⟨30569367764580266248560665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20379578509720177499040443 30569367764580266248560665)
  ·
    refine ⟨22927025823435199686420499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30569367764580266248560665 22927025823435199686420499)
    ·
      refine ⟨34390538735152799529630749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22927025823435199686420499 34390538735152799529630749)
      ·
        refine ⟨12896452025682299823611531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34390538735152799529630749 12896452025682299823611531)
        ·
          refine ⟨19344678038523449735417297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12896452025682299823611531 19344678038523449735417297)
          ·
            refine ⟨14508508528892587301562973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19344678038523449735417297 14508508528892587301562973)
            ·
              refine ⟨5440690698334720238086115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14508508528892587301562973 5440690698334720238086115)
              ·
                refine ⟨8161036047502080357129173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440690698334720238086115 8161036047502080357129173)
                ·
                  refine ⟨191274282363330008370215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8161036047502080357129173 191274282363330008370215)
                  ·
                    rfl

theorem cell21_838137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_838137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838137 prefixEnd_838137 := by exact prefixLift 838137
  have htrace : WordTrace (prefixWord ++ tailWord_838137) baseStart_838137 baseEnd_838137 := by
    simpa [prefixWord, tailWord_838137, baseEnd_838137] using wordTrace_append hprefix tailTrace_838137
  have hstable : (prefixWord ++ tailWord_838137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838137).length < 2 ^ (prefixWord ++ tailWord_838137).sum := by decide
  have hdescent : baseEnd_838137 < baseStart_838137 := by decide
  rcases family_descends (prefixWord ++ tailWord_838137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838157 : List Nat := [1, 7, 1, 1, 1, 2, 8]
def baseStart_838157 : Nat := 118140960795 + 838157 * 2 ^ 59
def prefixEnd_838157 : Nat := 4983230072969 + 3 ^ 40 * 838157 * 2
def baseEnd_838157 : Nat := 21253205181757157559649

theorem tailTrace_838157 : CollatzResearch.WordTrace tailWord_838157 prefixEnd_838157 21253205181757157559649 := by
  unfold tailWord_838157
  simp only [CollatzResearch.WordTrace]
  refine ⟨30570097224507809664288725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20380064816338539776192483 30570097224507809664288725)
  ·
    refine ⟨716486653699401789006767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30570097224507809664288725 716486653699401789006767)
    ·
      refine ⟨1074729980549102683510151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 716486653699401789006767 1074729980549102683510151)
      ·
        refine ⟨1612094970823654025265227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074729980549102683510151 1612094970823654025265227)
        ·
          refine ⟨2418142456235481037897841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612094970823654025265227 2418142456235481037897841)
          ·
            refine ⟨1813606842176610778423381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2418142456235481037897841 1813606842176610778423381)
            ·
              refine ⟨21253205181757157559649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1813606842176610778423381 21253205181757157559649)
              ·
                rfl

theorem cell21_838157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 8].length) (baseStart_838157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838157 prefixEnd_838157 := by exact prefixLift 838157
  have htrace : WordTrace (prefixWord ++ tailWord_838157) baseStart_838157 baseEnd_838157 := by
    simpa [prefixWord, tailWord_838157, baseEnd_838157] using wordTrace_append hprefix tailTrace_838157
  have hstable : (prefixWord ++ tailWord_838157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838157).length < 2 ^ (prefixWord ++ tailWord_838157).sum := by decide
  have hdescent : baseEnd_838157 < baseStart_838157 := by decide
  rcases family_descends (prefixWord ++ tailWord_838157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838236 : List Nat := [2, 2, 4, 1, 4, 1, 2, 1, 4]
def baseStart_838236 : Nat := 118140960795 + 838236 * 2 ^ 59
def prefixEnd_838236 : Nat := 4983230072969 + 3 ^ 40 * 838236 * 2
def baseEnd_838236 : Nat := 191296875512127836220013

theorem tailTrace_838236 : CollatzResearch.WordTrace tailWord_838236 prefixEnd_838236 191296875512127836220013 := by
  unfold tailWord_838236
  simp only [CollatzResearch.WordTrace]
  refine ⟨15286489295610803078207281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20381985727481070770943041 15286489295610803078207281)
  ·
    refine ⟨11464866971708102308655461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15286489295610803078207281 11464866971708102308655461)
    ·
      refine ⟨2149662557195269182872899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11464866971708102308655461 2149662557195269182872899)
      ·
        refine ⟨3224493835792903774309349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2149662557195269182872899 3224493835792903774309349)
        ·
          refine ⟨604592594211169457683003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3224493835792903774309349 604592594211169457683003)
          ·
            refine ⟨906888891316754186524505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604592594211169457683003 906888891316754186524505)
            ·
              refine ⟨680166668487565639893379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906888891316754186524505 680166668487565639893379)
              ·
                refine ⟨1020250002731348459840069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680166668487565639893379 1020250002731348459840069)
                ·
                  refine ⟨191296875512127836220013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1020250002731348459840069 191296875512127836220013)
                  ·
                    rfl

theorem cell21_838236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_838236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838236 prefixEnd_838236 := by exact prefixLift 838236
  have htrace : WordTrace (prefixWord ++ tailWord_838236) baseStart_838236 baseEnd_838236 := by
    simpa [prefixWord, tailWord_838236, baseEnd_838236] using wordTrace_append hprefix tailTrace_838236
  have hstable : (prefixWord ++ tailWord_838236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838236).length < 2 ^ (prefixWord ++ tailWord_838236).sum := by decide
  have hdescent : baseEnd_838236 < baseStart_838236 := by decide
  rcases family_descends (prefixWord ++ tailWord_838236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838292 : List Nat := [2, 4, 2, 2, 1, 1, 3, 6]
def baseStart_838292 : Nat := 118140960795 + 838292 * 2 ^ 59
def prefixEnd_838292 : Nat := 4983230072969 + 3 ^ 40 * 838292 * 2
def baseEnd_838292 : Nat := 63769885158361394428855

theorem tailTrace_838292 : CollatzResearch.WordTrace tailWord_838292 prefixEnd_838292 63769885158361394428855 := by
  unfold tailWord_838292
  simp only [CollatzResearch.WordTrace]
  refine ⟨15287510539509363860226565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20383347386012485146968753 15287510539509363860226565)
  ·
    refine ⟨2866408226158005723792481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15287510539509363860226565 2866408226158005723792481)
    ·
      refine ⟨2149806169618504292844361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2866408226158005723792481 2149806169618504292844361)
      ·
        refine ⟨1612354627213878219633271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2149806169618504292844361 1612354627213878219633271)
        ·
          refine ⟨2418531940820817329449907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612354627213878219633271 2418531940820817329449907)
          ·
            refine ⟨3627797911231225994174861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2418531940820817329449907 3627797911231225994174861)
            ·
              refine ⟨1360424216711709747815573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3627797911231225994174861 1360424216711709747815573)
              ·
                refine ⟨63769885158361394428855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1360424216711709747815573 63769885158361394428855)
                ·
                  rfl

theorem cell21_838292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_838292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838292 prefixEnd_838292 := by exact prefixLift 838292
  have htrace : WordTrace (prefixWord ++ tailWord_838292) baseStart_838292 baseEnd_838292 := by
    simpa [prefixWord, tailWord_838292, baseEnd_838292] using wordTrace_append hprefix tailTrace_838292
  have hstable : (prefixWord ++ tailWord_838292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838292).length < 2 ^ (prefixWord ++ tailWord_838292).sum := by decide
  have hdescent : baseEnd_838292 < baseStart_838292 := by decide
  rcases family_descends (prefixWord ++ tailWord_838292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838323 : List Nat := [1, 1, 1, 2, 3, 5, 2, 3, 3]
def baseStart_838323 : Nat := 118140960795 + 838323 * 2 ^ 59
def prefixEnd_838323 : Nat := 4983230072969 + 3 ^ 40 * 838323 * 2
def baseEnd_838323 : Nat := 191316730097435018269835

theorem tailTrace_838323 : CollatzResearch.WordTrace tailWord_838323 prefixEnd_838323 191316730097435018269835 := by
  unfold tailWord_838323
  simp only [CollatzResearch.WordTrace]
  refine ⟨30576151741906420014831623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20384101161270946676554415 30576151741906420014831623)
  ·
    refine ⟨45864227612859630022247435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30576151741906420014831623 45864227612859630022247435)
    ·
      refine ⟨68796341419289445033371153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45864227612859630022247435 68796341419289445033371153)
      ·
        refine ⟨51597256064467083775028365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68796341419289445033371153 51597256064467083775028365)
        ·
          refine ⟨19348971024175156415635637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51597256064467083775028365 19348971024175156415635637)
          ·
            refine ⟨1813966033516420913965841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19348971024175156415635637 1813966033516420913965841)
            ·
              refine ⟨1360474525137315685474381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1813966033516420913965841 1360474525137315685474381)
              ·
                refine ⟨510177946926493382052893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1360474525137315685474381 510177946926493382052893)
                ·
                  refine ⟨191316730097435018269835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 510177946926493382052893 191316730097435018269835)
                  ·
                    rfl

theorem cell21_838323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 3].length) (baseStart_838323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838323 prefixEnd_838323 := by exact prefixLift 838323
  have htrace : WordTrace (prefixWord ++ tailWord_838323) baseStart_838323 baseEnd_838323 := by
    simpa [prefixWord, tailWord_838323, baseEnd_838323] using wordTrace_append hprefix tailTrace_838323
  have hstable : (prefixWord ++ tailWord_838323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838323).length < 2 ^ (prefixWord ++ tailWord_838323).sum := by decide
  have hdescent : baseEnd_838323 < baseStart_838323 := by decide
  rcases family_descends (prefixWord ++ tailWord_838323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838396 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 6]
def baseStart_838396 : Nat := 118140960795 + 838396 * 2 ^ 59
def prefixEnd_838396 : Nat := 4983230072969 + 3 ^ 40 * 838396 * 2
def baseEnd_838396 : Nat := 191333389692003113553019

theorem tailTrace_838396 : CollatzResearch.WordTrace tailWord_838396 prefixEnd_838396 191333389692003113553019 := by
  unfold tailWord_838396
  simp only [CollatzResearch.WordTrace]
  refine ⟨15289407135320976741119521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20385876180427968988159361 15289407135320976741119521)
  ·
    refine ⟨11467055351490732555839641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15289407135320976741119521 11467055351490732555839641)
    ·
      refine ⟨8600291513618049416879731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11467055351490732555839641 8600291513618049416879731)
      ·
        refine ⟨12900437270427074125319597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8600291513618049416879731 12900437270427074125319597)
        ·
          refine ⟨4837663976410152796994849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12900437270427074125319597 4837663976410152796994849)
          ·
            refine ⟨3628247982307614597746137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4837663976410152796994849 3628247982307614597746137)
            ·
              refine ⟨2721185986730710948309603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3628247982307614597746137 2721185986730710948309603)
              ·
                refine ⟨4081778980096066422464405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2721185986730710948309603 4081778980096066422464405)
                ·
                  refine ⟨191333389692003113553019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4081778980096066422464405 191333389692003113553019)
                  ·
                    rfl

theorem cell21_838396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_838396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838396 prefixEnd_838396 := by exact prefixLift 838396
  have htrace : WordTrace (prefixWord ++ tailWord_838396) baseStart_838396 baseEnd_838396 := by
    simpa [prefixWord, tailWord_838396, baseEnd_838396] using wordTrace_append hprefix tailTrace_838396
  have hstable : (prefixWord ++ tailWord_838396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838396).length < 2 ^ (prefixWord ++ tailWord_838396).sum := by decide
  have hdescent : baseEnd_838396 < baseStart_838396 := by decide
  rcases family_descends (prefixWord ++ tailWord_838396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838461 : List Nat := [1, 4, 1, 4, 3, 1, 1, 6]
def baseStart_838461 : Nat := 118140960795 + 838461 * 2 ^ 59
def prefixEnd_838461 : Nat := 4983230072969 + 3 ^ 40 * 838461 * 2
def baseEnd_838461 : Nat := 63782741192525814989851

theorem tailTrace_838461 : CollatzResearch.WordTrace tailWord_838461 prefixEnd_838461 63782741192525814989851 := by
  unfold tailWord_838461
  simp only [CollatzResearch.WordTrace]
  refine ⟨30581185015406469583355237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20387456676937646388903491 30581185015406469583355237)
  ·
    refine ⟨5733972190388713046879107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30581185015406469583355237 5733972190388713046879107)
    ·
      refine ⟨8600958285583069570318661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5733972190388713046879107 8600958285583069570318661)
      ·
        refine ⟨1612679678546825544434749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8600958285583069570318661 1612679678546825544434749)
        ·
          refine ⟨604754879455059579163031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1612679678546825544434749 604754879455059579163031)
          ·
            refine ⟨907132319182589368744547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604754879455059579163031 907132319182589368744547)
            ·
              refine ⟨1360698478773884053116821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907132319182589368744547 1360698478773884053116821)
              ·
                refine ⟨63782741192525814989851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1360698478773884053116821 63782741192525814989851)
                ·
                  rfl

theorem cell21_838461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 6].length) (baseStart_838461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838461 prefixEnd_838461 := by exact prefixLift 838461
  have htrace : WordTrace (prefixWord ++ tailWord_838461) baseStart_838461 baseEnd_838461 := by
    simpa [prefixWord, tailWord_838461, baseEnd_838461] using wordTrace_append hprefix tailTrace_838461
  have hstable : (prefixWord ++ tailWord_838461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838461).length < 2 ^ (prefixWord ++ tailWord_838461).sum := by decide
  have hdescent : baseEnd_838461 < baseStart_838461 := by decide
  rcases family_descends (prefixWord ++ tailWord_838461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838472 : List Nat := [2, 1, 3, 1, 1, 3, 1, 5, 4]
def baseStart_838472 : Nat := 118140960795 + 838472 * 2 ^ 59
def prefixEnd_838472 : Nat := 4983230072969 + 3 ^ 40 * 838472 * 2
def baseEnd_838472 : Nat := 191350733927443870286197

theorem tailTrace_838472 : CollatzResearch.WordTrace tailWord_838472 prefixEnd_838472 191350733927443870286197 := by
  unfold tailWord_838472
  simp only [CollatzResearch.WordTrace]
  refine ⟨15290793109183309231002835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20387724145577745641337113 15290793109183309231002835)
  ·
    refine ⟨22936189663774963846504253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15290793109183309231002835 22936189663774963846504253)
    ·
      refine ⟨8601071123915611442439095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22936189663774963846504253 8601071123915611442439095)
      ·
        refine ⟨12901606685873417163658643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8601071123915611442439095 12901606685873417163658643)
        ·
          refine ⟨19352410028810125745487965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12901606685873417163658643 19352410028810125745487965)
          ·
            refine ⟨7257153760803797154557987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19352410028810125745487965 7257153760803797154557987)
            ·
              refine ⟨10885730641205695731836981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7257153760803797154557987 10885730641205695731836981)
              ·
                refine ⟨1020537247613033974859717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10885730641205695731836981 1020537247613033974859717)
                ·
                  refine ⟨191350733927443870286197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1020537247613033974859717 191350733927443870286197)
                  ·
                    rfl

theorem cell21_838472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_838472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838472 prefixEnd_838472 := by exact prefixLift 838472
  have htrace : WordTrace (prefixWord ++ tailWord_838472) baseStart_838472 baseEnd_838472 := by
    simpa [prefixWord, tailWord_838472, baseEnd_838472] using wordTrace_append hprefix tailTrace_838472
  have hstable : (prefixWord ++ tailWord_838472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838472).length < 2 ^ (prefixWord ++ tailWord_838472).sum := by decide
  have hdescent : baseEnd_838472 < baseStart_838472 := by decide
  rcases family_descends (prefixWord ++ tailWord_838472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838492 : List Nat := [2, 2, 4, 2, 1, 2, 2, 3, 3]
def baseStart_838492 : Nat := 118140960795 + 838492 * 2 ^ 59
def prefixEnd_838492 : Nat := 4983230072969 + 3 ^ 40 * 838492 * 2
def baseEnd_838492 : Nat := 191355298199928279952823

theorem tailTrace_838492 : CollatzResearch.WordTrace tailWord_838492 prefixEnd_838492 191355298199928279952823 := by
  unfold tailWord_838492
  simp only [CollatzResearch.WordTrace]
  refine ⟨15291157839147080938866865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20388210452196107918489153 15291157839147080938866865)
  ·
    refine ⟨11468368379360310704150149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15291157839147080938866865 11468368379360310704150149)
    ·
      refine ⟨2150319071130058257028153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11468368379360310704150149 2150319071130058257028153)
      ·
        refine ⟨1612739303347543692771115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2150319071130058257028153 1612739303347543692771115)
        ·
          refine ⟨2419108955021315539156673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612739303347543692771115 2419108955021315539156673)
          ·
            refine ⟨1814331716265986654367505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2419108955021315539156673 1814331716265986654367505)
            ·
              refine ⟨1360748787199489990775629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1814331716265986654367505 1360748787199489990775629)
              ·
                refine ⟨510280795199808746540861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1360748787199489990775629 510280795199808746540861)
                ·
                  refine ⟨191355298199928279952823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 510280795199808746540861 191355298199928279952823)
                  ·
                    rfl

theorem cell21_838492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_838492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838492 prefixEnd_838492 := by exact prefixLift 838492
  have htrace : WordTrace (prefixWord ++ tailWord_838492) baseStart_838492 baseEnd_838492 := by
    simpa [prefixWord, tailWord_838492, baseEnd_838492] using wordTrace_append hprefix tailTrace_838492
  have hstable : (prefixWord ++ tailWord_838492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838492).length < 2 ^ (prefixWord ++ tailWord_838492).sum := by decide
  have hdescent : baseEnd_838492 < baseStart_838492 := by decide
  rcases family_descends (prefixWord ++ tailWord_838492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838548 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 8]
def baseStart_838548 : Nat := 118140960795 + 838548 * 2 ^ 59
def prefixEnd_838548 : Nat := 4983230072969 + 3 ^ 40 * 838548 * 2
def baseEnd_838548 : Nat := 191368078162884627019375

theorem tailTrace_838548 : CollatzResearch.WordTrace tailWord_838548 prefixEnd_838548 191368078162884627019375 := by
  unfold tailWord_838548
  simp only [CollatzResearch.WordTrace]
  refine ⟨15292179083045641720886149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20389572110727522294514865 15292179083045641720886149)
  ·
    refine ⟨2867283578071057822666153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15292179083045641720886149 2867283578071057822666153)
    ·
      refine ⟨2150462683553293366999615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2867283578071057822666153 2150462683553293366999615)
      ·
        refine ⟨3225694025329940050499423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2150462683553293366999615 3225694025329940050499423)
        ·
          refine ⟨4838541037994910075749135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3225694025329940050499423 4838541037994910075749135)
          ·
            refine ⟨7257811556992365113623703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4838541037994910075749135 7257811556992365113623703)
            ·
              refine ⟨10886717335488547670435555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7257811556992365113623703 10886717335488547670435555)
              ·
                refine ⟨16330076003232821505653333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10886717335488547670435555 16330076003232821505653333)
                ·
                  refine ⟨191368078162884627019375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16330076003232821505653333 191368078162884627019375)
                  ·
                    rfl

theorem cell21_838548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_838548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838548 prefixEnd_838548 := by exact prefixLift 838548
  have htrace : WordTrace (prefixWord ++ tailWord_838548) baseStart_838548 baseEnd_838548 := by
    simpa [prefixWord, tailWord_838548, baseEnd_838548] using wordTrace_append hprefix tailTrace_838548
  have hstable : (prefixWord ++ tailWord_838548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838548).length < 2 ^ (prefixWord ++ tailWord_838548).sum := by decide
  have hdescent : baseEnd_838548 < baseStart_838548 := by decide
  rcases family_descends (prefixWord ++ tailWord_838548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838807 : List Nat := [1, 1, 3, 3, 3, 3, 1, 6]
def baseStart_838807 : Nat := 118140960795 + 838807 * 2 ^ 59
def prefixEnd_838807 : Nat := 4983230072969 + 3 ^ 40 * 838807 * 2
def baseEnd_838807 : Nat := 63809061830519244067393

theorem tailTrace_838807 : CollatzResearch.WordTrace tailWord_838807 prefixEnd_838807 63809061830519244067393 := by
  unfold tailWord_838807
  simp only [CollatzResearch.WordTrace]
  refine ⟨30593804672152970675450675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20395869781435313783633783 30593804672152970675450675)
  ·
    refine ⟨45890707008229456013176013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30593804672152970675450675 45890707008229456013176013)
    ·
      refine ⟨17209015128086046004941005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45890707008229456013176013 17209015128086046004941005)
      ·
        refine ⟨6453380673032267251852877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17209015128086046004941005 6453380673032267251852877)
        ·
          refine ⟨2420017752387100219444829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6453380673032267251852877 2420017752387100219444829)
          ·
            refine ⟨907506657145162582291811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2420017752387100219444829 907506657145162582291811)
            ·
              refine ⟨1361259985717743873437717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907506657145162582291811 1361259985717743873437717)
              ·
                refine ⟨63809061830519244067393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1361259985717743873437717 63809061830519244067393)
                ·
                  rfl

theorem cell21_838807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 6].length) (baseStart_838807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838807 prefixEnd_838807 := by exact prefixLift 838807
  have htrace : WordTrace (prefixWord ++ tailWord_838807) baseStart_838807 baseEnd_838807 := by
    simpa [prefixWord, tailWord_838807, baseEnd_838807] using wordTrace_append hprefix tailTrace_838807
  have hstable : (prefixWord ++ tailWord_838807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838807).length < 2 ^ (prefixWord ++ tailWord_838807).sum := by decide
  have hdescent : baseEnd_838807 < baseStart_838807 := by decide
  rcases family_descends (prefixWord ++ tailWord_838807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838821 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 5]
def baseStart_838821 : Nat := 118140960795 + 838821 * 2 ^ 59
def prefixEnd_838821 : Nat := 4983230072969 + 3 ^ 40 * 838821 * 2
def baseEnd_838821 : Nat := 191430380482296818968817

theorem tailTrace_838821 : CollatzResearch.WordTrace tailWord_838821 prefixEnd_838821 191430380482296818968817 := by
  unfold tailWord_838821
  simp only [CollatzResearch.WordTrace]
  refine ⟨30594315294102251066460317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20396210196068167377640211 30594315294102251066460317)
  ·
    refine ⟨11472868235288344149922619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30594315294102251066460317 11472868235288344149922619)
    ·
      refine ⟨17209302352932516224883929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11472868235288344149922619 17209302352932516224883929)
      ·
        refine ⟨12906976764699387168662947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17209302352932516224883929 12906976764699387168662947)
        ·
          refine ⟨19360465147049080752994421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12906976764699387168662947 19360465147049080752994421)
          ·
            refine ⟨1815043607535851320593227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19360465147049080752994421 1815043607535851320593227)
            ·
              refine ⟨2722565411303776980889841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815043607535851320593227 2722565411303776980889841)
              ·
                refine ⟨2041924058477832735667381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2722565411303776980889841 2041924058477832735667381)
                ·
                  refine ⟨191430380482296818968817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2041924058477832735667381 191430380482296818968817)
                  ·
                    rfl

theorem cell21_838821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_838821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838821 prefixEnd_838821 := by exact prefixLift 838821
  have htrace : WordTrace (prefixWord ++ tailWord_838821) baseStart_838821 baseEnd_838821 := by
    simpa [prefixWord, tailWord_838821, baseEnd_838821] using wordTrace_append hprefix tailTrace_838821
  have hstable : (prefixWord ++ tailWord_838821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838821).length < 2 ^ (prefixWord ++ tailWord_838821).sum := by decide
  have hdescent : baseEnd_838821 < baseStart_838821 := by decide
  rcases family_descends (prefixWord ++ tailWord_838821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838866 : List Nat := [3, 2, 2, 2, 1, 1, 2, 8]
def baseStart_838866 : Nat := 118140960795 + 838866 * 2 ^ 59
def prefixEnd_838866 : Nat := 4983230072969 + 3 ^ 40 * 838866 * 2
def baseEnd_838866 : Nat := 63813550031795580239575

theorem tailTrace_838866 : CollatzResearch.WordTrace tailWord_838866 prefixEnd_838866 63813550031795580239575 := by
  unfold tailWord_838866
  simp only [CollatzResearch.WordTrace]
  refine ⟨7648989144734805937962113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20397304385959482501232301 7648989144734805937962113)
  ·
    refine ⟨5736741858551104453471585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7648989144734805937962113 5736741858551104453471585)
    ·
      refine ⟨4302556393913328340103689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5736741858551104453471585 4302556393913328340103689)
      ·
        refine ⟨3226917295434996255077767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4302556393913328340103689 3226917295434996255077767)
        ·
          refine ⟨4840375943152494382616651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3226917295434996255077767 4840375943152494382616651)
          ·
            refine ⟨7260563914728741573924977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4840375943152494382616651 7260563914728741573924977)
            ·
              refine ⟨5445422936046556180443733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7260563914728741573924977 5445422936046556180443733)
              ·
                refine ⟨63813550031795580239575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5445422936046556180443733 63813550031795580239575)
                ·
                  rfl

theorem cell21_838866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_838866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838866 prefixEnd_838866 := by exact prefixLift 838866
  have htrace : WordTrace (prefixWord ++ tailWord_838866) baseStart_838866 baseEnd_838866 := by
    simpa [prefixWord, tailWord_838866, baseEnd_838866] using wordTrace_append hprefix tailTrace_838866
  have hstable : (prefixWord ++ tailWord_838866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838866).length < 2 ^ (prefixWord ++ tailWord_838866).sum := by decide
  have hdescent : baseEnd_838866 < baseStart_838866 := by decide
  rcases family_descends (prefixWord ++ tailWord_838866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838911 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 6]
def baseStart_838911 : Nat := 118140960795 + 838911 * 2 ^ 59
def prefixEnd_838911 : Nat := 4983230072969 + 3 ^ 40 * 838911 * 2
def baseEnd_838911 : Nat := 191450919708476662468633

theorem tailTrace_838911 : CollatzResearch.WordTrace tailWord_838911 prefixEnd_838911 191450919708476662468633 := by
  unfold tailWord_838911
  simp only [CollatzResearch.WordTrace]
  refine ⟨30597597863776196437236587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20398398575850797624824391 30597597863776196437236587)
  ·
    refine ⟨45896396795664294655854881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30597597863776196437236587 45896396795664294655854881)
    ·
      refine ⟨34422297596748220991891161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45896396795664294655854881 34422297596748220991891161)
      ·
        refine ⟨25816723197561165743918371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34422297596748220991891161 25816723197561165743918371)
        ·
          refine ⟨38725084796341748615877557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25816723197561165743918371 38725084796341748615877557)
          ·
            refine ⟨3630476699657038932738521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38725084796341748615877557 3630476699657038932738521)
            ·
              refine ⟨2722857524742779199553891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3630476699657038932738521 2722857524742779199553891)
              ·
                refine ⟨4084286287114168799330837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2722857524742779199553891 4084286287114168799330837)
                ·
                  refine ⟨191450919708476662468633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4084286287114168799330837 191450919708476662468633)
                  ·
                    rfl

theorem cell21_838911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 6].length) (baseStart_838911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_838911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_838911 prefixEnd_838911 := by exact prefixLift 838911
  have htrace : WordTrace (prefixWord ++ tailWord_838911) baseStart_838911 baseEnd_838911 := by
    simpa [prefixWord, tailWord_838911, baseEnd_838911] using wordTrace_append hprefix tailTrace_838911
  have hstable : (prefixWord ++ tailWord_838911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838911).length < 2 ^ (prefixWord ++ tailWord_838911).sum := by decide
  have hdescent : baseEnd_838911 < baseStart_838911 := by decide
  rcases family_descends (prefixWord ++ tailWord_838911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839001 : List Nat := [1, 2, 1, 2, 2, 2, 2, 9]
def baseStart_839001 : Nat := 118140960795 + 839001 * 2 ^ 59
def prefixEnd_839001 : Nat := 4983230072969 + 3 ^ 40 * 839001 * 2
def baseEnd_839001 : Nat := 63823819644885501989483

theorem tailTrace_839001 : CollatzResearch.WordTrace tailWord_839001 prefixEnd_839001 63823819644885501989483 := by
  unfold tailWord_839001
  simp only [CollatzResearch.WordTrace]
  refine ⟨30600880433450141808012857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20400586955633427872008571 30600880433450141808012857)
  ·
    refine ⟨22950660325087606356009643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30600880433450141808012857 22950660325087606356009643)
    ·
      refine ⟨34425990487631409534014465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22950660325087606356009643 34425990487631409534014465)
      ·
        refine ⟨25819492865723557150510849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34425990487631409534014465 25819492865723557150510849)
        ·
          refine ⟨19364619649292667862883137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25819492865723557150510849 19364619649292667862883137)
          ·
            refine ⟨14523464736969500897162353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19364619649292667862883137 14523464736969500897162353)
            ·
              refine ⟨10892598552727125672871765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14523464736969500897162353 10892598552727125672871765)
              ·
                refine ⟨63823819644885501989483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10892598552727125672871765 63823819644885501989483)
                ·
                  rfl

theorem cell21_839001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 9].length) (baseStart_839001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839001 prefixEnd_839001 := by exact prefixLift 839001
  have htrace : WordTrace (prefixWord ++ tailWord_839001) baseStart_839001 baseEnd_839001 := by
    simpa [prefixWord, tailWord_839001, baseEnd_839001] using wordTrace_append hprefix tailTrace_839001
  have hstable : (prefixWord ++ tailWord_839001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839001).length < 2 ^ (prefixWord ++ tailWord_839001).sum := by decide
  have hdescent : baseEnd_839001 < baseStart_839001 := by decide
  rcases family_descends (prefixWord ++ tailWord_839001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839021 : List Nat := [1, 5, 1, 1, 1, 5, 1, 2, 4]
def baseStart_839021 : Nat := 118140960795 + 839021 * 2 ^ 59
def prefixEnd_839021 : Nat := 4983230072969 + 3 ^ 40 * 839021 * 2
def baseEnd_839021 : Nat := 191476023207140915635075

theorem tailTrace_839021 : CollatzResearch.WordTrace tailWord_839021 prefixEnd_839021 191476023207140915635075 := by
  unfold tailWord_839021
  simp only [CollatzResearch.WordTrace]
  refine ⟨30601609893377685223740917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20401073262251790149160611 30601609893377685223740917)
  ·
    refine ⟨2868900927504157989725711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30601609893377685223740917 2868900927504157989725711)
    ·
      refine ⟨4303351391256236984588567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2868900927504157989725711 4303351391256236984588567)
      ·
        refine ⟨6455027086884355476882851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4303351391256236984588567 6455027086884355476882851)
        ·
          refine ⟨9682540630326533215324277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6455027086884355476882851 9682540630326533215324277)
          ·
            refine ⟨907738184093112488936651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9682540630326533215324277 907738184093112488936651)
            ·
              refine ⟨1361607276139668733404977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907738184093112488936651 1361607276139668733404977)
              ·
                refine ⟨1021205457104751550053733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361607276139668733404977 1021205457104751550053733)
                ·
                  refine ⟨191476023207140915635075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1021205457104751550053733 191476023207140915635075)
                  ·
                    rfl

theorem cell21_839021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_839021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839021 prefixEnd_839021 := by exact prefixLift 839021
  have htrace : WordTrace (prefixWord ++ tailWord_839021) baseStart_839021 baseEnd_839021 := by
    simpa [prefixWord, tailWord_839021, baseEnd_839021] using wordTrace_append hprefix tailTrace_839021
  have hstable : (prefixWord ++ tailWord_839021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839021).length < 2 ^ (prefixWord ++ tailWord_839021).sum := by decide
  have hdescent : baseEnd_839021 < baseStart_839021 := by decide
  rcases family_descends (prefixWord ++ tailWord_839021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839201 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 5]
def baseStart_839201 : Nat := 118140960795 + 839201 * 2 ^ 59
def prefixEnd_839201 : Nat := 4983230072969 + 3 ^ 40 * 839201 * 2
def baseEnd_839201 : Nat := 191517101659500602634707

theorem tailTrace_839201 : CollatzResearch.WordTrace tailWord_839201 prefixEnd_839201 191517101659500602634707 := by
  unfold tailWord_839201
  simp only [CollatzResearch.WordTrace]
  refine ⟨30608175032725575965293457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20405450021817050643528971 30608175032725575965293457)
  ·
    refine ⟨22956131274544181973970093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30608175032725575965293457 22956131274544181973970093)
    ·
      refine ⟨8608549227954068240238785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22956131274544181973970093 8608549227954068240238785)
      ·
        refine ⟨6456411920965551180179089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8608549227954068240238785 6456411920965551180179089)
        ·
          refine ⟨4842308940724163385134317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6456411920965551180179089 4842308940724163385134317)
          ·
            refine ⟨1815865852771561269425369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4842308940724163385134317 1815865852771561269425369)
            ·
              refine ⟨1361899389578670952069027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1815865852771561269425369 1361899389578670952069027)
              ·
                refine ⟨2042849084368006428103541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361899389578670952069027 2042849084368006428103541)
                ·
                  refine ⟨191517101659500602634707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2042849084368006428103541 191517101659500602634707)
                  ·
                    rfl

theorem cell21_839201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_839201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839201 prefixEnd_839201 := by exact prefixLift 839201
  have htrace : WordTrace (prefixWord ++ tailWord_839201) baseStart_839201 baseEnd_839201 := by
    simpa [prefixWord, tailWord_839201, baseEnd_839201] using wordTrace_append hprefix tailTrace_839201
  have hstable : (prefixWord ++ tailWord_839201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839201).length < 2 ^ (prefixWord ++ tailWord_839201).sum := by decide
  have hdescent : baseEnd_839201 < baseStart_839201 := by decide
  rcases family_descends (prefixWord ++ tailWord_839201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839353 : List Nat := [1, 2, 1, 4, 1, 1, 3, 5, 3]
def baseStart_839353 : Nat := 118140960795 + 839353 * 2 ^ 59
def prefixEnd_839353 : Nat := 4983230072969 + 3 ^ 40 * 839353 * 2
def baseEnd_839353 : Nat := 191551790130382116101063

theorem tailTrace_839353 : CollatzResearch.WordTrace tailWord_839353 prefixEnd_839353 191551790130382116101063 := by
  unfold tailWord_839353
  simp only [CollatzResearch.WordTrace]
  refine ⟨30613718928174905924826713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20409145952116603949884475 30613718928174905924826713)
  ·
    refine ⟨22960289196131179443620035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30613718928174905924826713 22960289196131179443620035)
    ·
      refine ⟨34440433794196769165430053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22960289196131179443620035 34440433794196769165430053)
      ·
        refine ⟨6457581336411894218518135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34440433794196769165430053 6457581336411894218518135)
        ·
          refine ⟨9686372004617841327777203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6457581336411894218518135 9686372004617841327777203)
          ·
            refine ⟨14529558006926761991665805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9686372004617841327777203 14529558006926761991665805)
            ·
              refine ⟨5448584252597535746874677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14529558006926761991665805 5448584252597535746874677)
              ·
                refine ⟨510804773681018976269501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5448584252597535746874677 510804773681018976269501)
                ·
                  refine ⟨191551790130382116101063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 510804773681018976269501 191551790130382116101063)
                  ·
                    rfl

theorem cell21_839353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 3].length) (baseStart_839353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839353 prefixEnd_839353 := by exact prefixLift 839353
  have htrace : WordTrace (prefixWord ++ tailWord_839353) baseStart_839353 baseEnd_839353 := by
    simpa [prefixWord, tailWord_839353, baseEnd_839353] using wordTrace_append hprefix tailTrace_839353
  have hstable : (prefixWord ++ tailWord_839353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839353).length < 2 ^ (prefixWord ++ tailWord_839353).sum := by decide
  have hdescent : baseEnd_839353 < baseStart_839353 := by decide
  rcases family_descends (prefixWord ++ tailWord_839353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839384 : List Nat := [2, 1, 2, 2, 3, 1, 5, 1, 4]
def baseStart_839384 : Nat := 118140960795 + 839384 * 2 ^ 59
def prefixEnd_839384 : Nat := 4983230072969 + 3 ^ 40 * 839384 * 2
def baseEnd_839384 : Nat := 191558864752732951084333

theorem tailTrace_839384 : CollatzResearch.WordTrace tailWord_839384 prefixEnd_839384 191558864752732951084333 := by
  unfold tailWord_839384
  simp only [CollatzResearch.WordTrace]
  refine ⟨15307424795531299109602603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20409899727375065479470137 15307424795531299109602603)
  ·
    refine ⟨22961137193296948664403905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15307424795531299109602603 22961137193296948664403905)
    ·
      refine ⟨17220852894972711498302929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22961137193296948664403905 17220852894972711498302929)
      ·
        refine ⟨12915639671229533623727197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17220852894972711498302929 12915639671229533623727197)
        ·
          refine ⟨4843364876711075108897699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12915639671229533623727197 4843364876711075108897699)
          ·
            refine ⟨7265047315066612663346549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4843364876711075108897699 7265047315066612663346549)
            ·
              refine ⟨681098185787494937188739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7265047315066612663346549 681098185787494937188739)
              ·
                refine ⟨1021647278681242405783109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681098185787494937188739 1021647278681242405783109)
                ·
                  refine ⟨191558864752732951084333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1021647278681242405783109 191558864752732951084333)
                  ·
                    rfl

theorem cell21_839384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_839384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839384 prefixEnd_839384 := by exact prefixLift 839384
  have htrace : WordTrace (prefixWord ++ tailWord_839384) baseStart_839384 baseEnd_839384 := by
    simpa [prefixWord, tailWord_839384, baseEnd_839384] using wordTrace_append hprefix tailTrace_839384
  have hstable : (prefixWord ++ tailWord_839384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839384).length < 2 ^ (prefixWord ++ tailWord_839384).sum := by decide
  have hdescent : baseEnd_839384 < baseStart_839384 := by decide
  rcases family_descends (prefixWord ++ tailWord_839384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839457 : List Nat := [1, 2, 3, 2, 1, 3, 2, 7]
def baseStart_839457 : Nat := 118140960795 + 839457 * 2 ^ 59
def prefixEnd_839457 : Nat := 4983230072969 + 3 ^ 40 * 839457 * 2
def baseEnd_839457 : Nat := 63858508115767015455839

theorem tailTrace_839457 : CollatzResearch.WordTrace tailWord_839457 prefixEnd_839457 63858508115767015455839 := by
  unfold tailWord_839457
  simp only [CollatzResearch.WordTrace]
  refine ⟨30617512119798131686612625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20411674746532087791075083 30617512119798131686612625)
  ·
    refine ⟨22963134089848598764959469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30617512119798131686612625 22963134089848598764959469)
    ·
      refine ⟨8611175283693224536859801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22963134089848598764959469 8611175283693224536859801)
      ·
        refine ⟨6458381462769918402644851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8611175283693224536859801 6458381462769918402644851)
        ·
          refine ⟨9687572194154877603967277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6458381462769918402644851 9687572194154877603967277)
          ·
            refine ⟨3632839572808079101487729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9687572194154877603967277 3632839572808079101487729)
            ·
              refine ⟨2724629679606059326115797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3632839572808079101487729 2724629679606059326115797)
              ·
                refine ⟨63858508115767015455839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2724629679606059326115797 63858508115767015455839)
                ·
                  rfl

theorem cell21_839457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 7].length) (baseStart_839457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839457 prefixEnd_839457 := by exact prefixLift 839457
  have htrace : WordTrace (prefixWord ++ tailWord_839457) baseStart_839457 baseEnd_839457 := by
    simpa [prefixWord, tailWord_839457, baseEnd_839457] using wordTrace_append hprefix tailTrace_839457
  have hstable : (prefixWord ++ tailWord_839457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839457).length < 2 ^ (prefixWord ++ tailWord_839457).sum := by decide
  have hdescent : baseEnd_839457 < baseStart_839457 := by decide
  rcases family_descends (prefixWord ++ tailWord_839457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839471 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 7]
def baseStart_839471 : Nat := 118140960795 + 839471 * 2 ^ 59
def prefixEnd_839471 : Nat := 4983230072969 + 3 ^ 40 * 839471 * 2
def baseEnd_839471 : Nat := 191578719338040133134155

theorem tailTrace_839471 : CollatzResearch.WordTrace tailWord_839471 prefixEnd_839471 191578719338040133134155 := by
  unfold tailWord_839471
  simp only [CollatzResearch.WordTrace]
  refine ⟨30618022741747412077622267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20412015161164941385081511 30618022741747412077622267)
  ·
    refine ⟨45927034112621118116433401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30618022741747412077622267 45927034112621118116433401)
    ·
      refine ⟨34445275584465838587325051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45927034112621118116433401 34445275584465838587325051)
      ·
        refine ⟨51667913376698757880987577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34445275584465838587325051 51667913376698757880987577)
        ·
          refine ⟨38750935032524068410740683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51667913376698757880987577 38750935032524068410740683)
          ·
            refine ⟨58126402548786102616111025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38750935032524068410740683 58126402548786102616111025)
            ·
              refine ⟨43594801911589576962083269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58126402548786102616111025 43594801911589576962083269)
              ·
                refine ⟨8174025358423045680390613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43594801911589576962083269 8174025358423045680390613)
                ·
                  refine ⟨191578719338040133134155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8174025358423045680390613 191578719338040133134155)
                  ·
                    rfl

theorem cell21_839471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_839471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839471 prefixEnd_839471 := by exact prefixLift 839471
  have htrace : WordTrace (prefixWord ++ tailWord_839471) baseStart_839471 baseEnd_839471 := by
    simpa [prefixWord, tailWord_839471, baseEnd_839471] using wordTrace_append hprefix tailTrace_839471
  have hstable : (prefixWord ++ tailWord_839471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839471).length < 2 ^ (prefixWord ++ tailWord_839471).sum := by decide
  have hdescent : baseEnd_839471 < baseStart_839471 := by decide
  rcases family_descends (prefixWord ++ tailWord_839471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839502 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_839502 : Nat := 118140960795 + 839502 * 2 ^ 59
def prefixEnd_839502 : Nat := 4983230072969 + 3 ^ 40 * 839502 * 2
def baseEnd_839502 : Nat := 191585793960390968117425

theorem tailTrace_839502 : CollatzResearch.WordTrace tailWord_839502 prefixEnd_839502 191585793960390968117425 := by
  unfold tailWord_839502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3827394175579388046500095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20412768936423402914667173 3827394175579388046500095)
  ·
    refine ⟨5741091263369082069750143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3827394175579388046500095 5741091263369082069750143)
    ·
      refine ⟨8611636895053623104625215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5741091263369082069750143 8611636895053623104625215)
      ·
        refine ⟨12917455342580434656937823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8611636895053623104625215 12917455342580434656937823)
        ·
          refine ⟨19376183013870651985406735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12917455342580434656937823 19376183013870651985406735)
          ·
            refine ⟨29064274520805977978110103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19376183013870651985406735 29064274520805977978110103)
            ·
              refine ⟨43596411781208966967165155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29064274520805977978110103 43596411781208966967165155)
              ·
                refine ⟨65394617671813450450747733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43596411781208966967165155 65394617671813450450747733)
                ·
                  refine ⟨191585793960390968117425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 65394617671813450450747733 191585793960390968117425)
                  ·
                    rfl

theorem cell21_839502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_839502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839502 prefixEnd_839502 := by exact prefixLift 839502
  have htrace : WordTrace (prefixWord ++ tailWord_839502) baseStart_839502 baseEnd_839502 := by
    simpa [prefixWord, tailWord_839502, baseEnd_839502] using wordTrace_append hprefix tailTrace_839502
  have hstable : (prefixWord ++ tailWord_839502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839502).length < 2 ^ (prefixWord ++ tailWord_839502).sum := by decide
  have hdescent : baseEnd_839502 < baseStart_839502 := by decide
  rcases family_descends (prefixWord ++ tailWord_839502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839522 : List Nat := [3, 3, 2, 1, 2, 1, 1, 5, 3]
def baseStart_839522 : Nat := 118140960795 + 839522 * 2 ^ 59
def prefixEnd_839522 : Nat := 4983230072969 + 3 ^ 40 * 839522 * 2
def baseEnd_839522 : Nat := 191590358232875377784051

theorem tailTrace_839522 : CollatzResearch.WordTrace tailWord_839522 prefixEnd_839522 191590358232875377784051 := by
  unfold tailWord_839522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7654970716140661946932205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20413255243041765191819213 7654970716140661946932205)
  ·
    refine ⟨2870614018552748230099577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7654970716140661946932205 2870614018552748230099577)
    ·
      refine ⟨2152960513914561172574683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2870614018552748230099577 2152960513914561172574683)
      ·
        refine ⟨3229440770871841758862025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2152960513914561172574683 3229440770871841758862025)
        ·
          refine ⟨2422080578153881319146519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3229440770871841758862025 2422080578153881319146519)
          ·
            refine ⟨3633120867230821978719779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422080578153881319146519 3633120867230821978719779)
            ·
              refine ⟨5449681300846232968079669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3633120867230821978719779 5449681300846232968079669)
              ·
                refine ⟨510907621954334340757469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5449681300846232968079669 510907621954334340757469)
                ·
                  refine ⟨191590358232875377784051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 510907621954334340757469 191590358232875377784051)
                  ·
                    rfl

theorem cell21_839522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_839522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839522 prefixEnd_839522 := by exact prefixLift 839522
  have htrace : WordTrace (prefixWord ++ tailWord_839522) baseStart_839522 baseEnd_839522 := by
    simpa [prefixWord, tailWord_839522, baseEnd_839522] using wordTrace_append hprefix tailTrace_839522
  have hstable : (prefixWord ++ tailWord_839522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839522).length < 2 ^ (prefixWord ++ tailWord_839522).sum := by decide
  have hdescent : baseEnd_839522 < baseStart_839522 := by decide
  rcases family_descends (prefixWord ++ tailWord_839522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839609 : List Nat := [1, 2, 1, 4, 2, 1, 4, 6]
def baseStart_839609 : Nat := 118140960795 + 839609 * 2 ^ 59
def prefixEnd_839609 : Nat := 4983230072969 + 3 ^ 40 * 839609 * 2
def baseEnd_839609 : Nat := 63870070939394186611291

theorem tailTrace_839609 : CollatzResearch.WordTrace tailWord_839609 prefixEnd_839609 63870070939394186611291 := by
  unfold tailWord_839609
  simp only [CollatzResearch.WordTrace]
  refine ⟨30623056015247461646145881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20415370676831641097430587 30623056015247461646145881)
  ·
    refine ⟨22967292011435596234609411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30623056015247461646145881 22967292011435596234609411)
    ·
      refine ⟨34450938017153394351914117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22967292011435596234609411 34450938017153394351914117)
      ·
        refine ⟨6459550878216261440983897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34450938017153394351914117 6459550878216261440983897)
        ·
          refine ⟨4844663158662196080737923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6459550878216261440983897 4844663158662196080737923)
          ·
            refine ⟨7266994737993294121106885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4844663158662196080737923 7266994737993294121106885)
            ·
              refine ⟨1362561513373742647707541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7266994737993294121106885 1362561513373742647707541)
              ·
                refine ⟨63870070939394186611291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1362561513373742647707541 63870070939394186611291)
                ·
                  rfl

theorem cell21_839609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 6].length) (baseStart_839609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839609 prefixEnd_839609 := by exact prefixLift 839609
  have htrace : WordTrace (prefixWord ++ tailWord_839609) baseStart_839609 baseEnd_839609 := by
    simpa [prefixWord, tailWord_839609, baseEnd_839609] using wordTrace_append hprefix tailTrace_839609
  have hstable : (prefixWord ++ tailWord_839609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839609).length < 2 ^ (prefixWord ++ tailWord_839609).sum := by decide
  have hdescent : baseEnd_839609 < baseStart_839609 := by decide
  rcases family_descends (prefixWord ++ tailWord_839609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839623 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 7]
def baseStart_839623 : Nat := 118140960795 + 839623 * 2 ^ 59
def prefixEnd_839623 : Nat := 4983230072969 + 3 ^ 40 * 839623 * 2
def baseEnd_839623 : Nat := 191613407808921646600511

theorem tailTrace_839623 : CollatzResearch.WordTrace tailWord_839623 prefixEnd_839623 191613407808921646600511 := by
  unfold tailWord_839623
  simp only [CollatzResearch.WordTrace]
  refine ⟨30623566637196742037155523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20415711091464494691437015 30623566637196742037155523)
  ·
    refine ⟨45935349955795113055733285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30623566637196742037155523 45935349955795113055733285)
    ·
      refine ⟨8612878116711583697949991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45935349955795113055733285 8612878116711583697949991)
      ·
        refine ⟨12919317175067375546924987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8612878116711583697949991 12919317175067375546924987)
        ·
          refine ⟨19378975762601063320387481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12919317175067375546924987 19378975762601063320387481)
          ·
            refine ⟨14534231821950797490290611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19378975762601063320387481 14534231821950797490290611)
            ·
              refine ⟨21801347732926196235435917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14534231821950797490290611 21801347732926196235435917)
              ·
                refine ⟨8175505399847323588288469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21801347732926196235435917 8175505399847323588288469)
                ·
                  refine ⟨191613407808921646600511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8175505399847323588288469 191613407808921646600511)
                  ·
                    rfl

theorem cell21_839623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_839623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839623 prefixEnd_839623 := by exact prefixLift 839623
  have htrace : WordTrace (prefixWord ++ tailWord_839623) baseStart_839623 baseEnd_839623 := by
    simpa [prefixWord, tailWord_839623, baseEnd_839623] using wordTrace_append hprefix tailTrace_839623
  have hstable : (prefixWord ++ tailWord_839623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839623).length < 2 ^ (prefixWord ++ tailWord_839623).sum := by decide
  have hdescent : baseEnd_839623 < baseStart_839623 := by decide
  rcases family_descends (prefixWord ++ tailWord_839623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839775 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 5]
def baseStart_839775 : Nat := 118140960795 + 839775 * 2 ^ 59
def prefixEnd_839775 : Nat := 4983230072969 + 3 ^ 40 * 839775 * 2
def baseEnd_839775 : Nat := 191648096279803160066867

theorem tailTrace_839775 : CollatzResearch.WordTrace tailWord_839775 prefixEnd_839775 191648096279803160066867 := by
  unfold tailWord_839775
  simp only [CollatzResearch.WordTrace]
  refine ⟨30629110532646071996688779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20419407021764047997792519 30629110532646071996688779)
  ·
    refine ⟨45943665798969107995033169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30629110532646071996688779 45943665798969107995033169)
    ·
      refine ⟨34457749349226830996274877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45943665798969107995033169 34457749349226830996274877)
      ·
        refine ⟨12921656005960061623603079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34457749349226830996274877 12921656005960061623603079)
        ·
          refine ⟨19382484008940092435404619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12921656005960061623603079 19382484008940092435404619)
          ·
            refine ⟨29073726013410138653106929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19382484008940092435404619 29073726013410138653106929)
            ·
              refine ⟨21805294510057603989830197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29073726013410138653106929 21805294510057603989830197)
              ·
                refine ⟨2044246360317900374046581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21805294510057603989830197 2044246360317900374046581)
                ·
                  refine ⟨191648096279803160066867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2044246360317900374046581 191648096279803160066867)
                  ·
                    rfl

theorem cell21_839775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 5].length) (baseStart_839775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839775 prefixEnd_839775 := by exact prefixLift 839775
  have htrace : WordTrace (prefixWord ++ tailWord_839775) baseStart_839775 baseEnd_839775 := by
    simpa [prefixWord, tailWord_839775, baseEnd_839775] using wordTrace_append hprefix tailTrace_839775
  have hstable : (prefixWord ++ tailWord_839775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839775).length < 2 ^ (prefixWord ++ tailWord_839775).sum := by decide
  have hdescent : baseEnd_839775 < baseStart_839775 := by decide
  rcases family_descends (prefixWord ++ tailWord_839775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839837 : List Nat := [1, 4, 2, 1, 1, 3, 3, 6]
def baseStart_839837 : Nat := 118140960795 + 839837 * 2 ^ 59
def prefixEnd_839837 : Nat := 4983230072969 + 3 ^ 40 * 839837 * 2
def baseEnd_839837 : Nat := 63887415174834943344469

theorem tailTrace_839837 : CollatzResearch.WordTrace tailWord_839837 prefixEnd_839837 63887415174834943344469 := by
  unfold tailWord_839837
  simp only [CollatzResearch.WordTrace]
  refine ⟨30631371858421456585445765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20420914572280971056963843 30631371858421456585445765)
  ·
    refine ⟨5743382223454023109771081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30631371858421456585445765 5743382223454023109771081)
    ·
      refine ⟨4307536667590517332328311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5743382223454023109771081 4307536667590517332328311)
      ·
        refine ⟨6461305001385775998492467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4307536667590517332328311 6461305001385775998492467)
        ·
          refine ⟨9691957502078663997738701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6461305001385775998492467 9691957502078663997738701)
          ·
            refine ⟨3634484063279498999152013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9691957502078663997738701 3634484063279498999152013)
            ·
              refine ⟨1362931523729812124682005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3634484063279498999152013 1362931523729812124682005)
              ·
                refine ⟨63887415174834943344469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1362931523729812124682005 63887415174834943344469)
                ·
                  rfl

theorem cell21_839837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 6].length) (baseStart_839837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839837 prefixEnd_839837 := by exact prefixLift 839837
  have htrace : WordTrace (prefixWord ++ tailWord_839837) baseStart_839837 baseEnd_839837 := by
    simpa [prefixWord, tailWord_839837, baseEnd_839837] using wordTrace_append hprefix tailTrace_839837
  have hstable : (prefixWord ++ tailWord_839837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839837).length < 2 ^ (prefixWord ++ tailWord_839837).sum := by decide
  have hdescent : baseEnd_839837 < baseStart_839837 := by decide
  rcases family_descends (prefixWord ++ tailWord_839837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839874 : List Nat := [3, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_839874 : Nat := 118140960795 + 839874 * 2 ^ 59
def prefixEnd_839874 : Nat := 4983230072969 + 3 ^ 40 * 839874 * 2
def baseEnd_839874 : Nat := 191670689428600987916665

theorem tailTrace_839874 : CollatzResearch.WordTrace tailWord_839874 prefixEnd_839874 191670689428600987916665 := by
  unfold tailWord_839874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658180339821852976135669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20421814239524941269695117 7658180339821852976135669)
  ·
    refine ⟨717954406858298716512719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7658180339821852976135669 717954406858298716512719)
    ·
      refine ⟨1076931610287448074769079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 717954406858298716512719 1076931610287448074769079)
      ·
        refine ⟨1615397415431172112153619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076931610287448074769079 1615397415431172112153619)
        ·
          refine ⟨2423096123146758168230429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615397415431172112153619 2423096123146758168230429)
          ·
            refine ⟨908661046180034313086411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2423096123146758168230429 908661046180034313086411)
            ·
              refine ⟨1362991569270051469629617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908661046180034313086411 1362991569270051469629617)
              ·
                refine ⟨1022243676952538602222213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362991569270051469629617 1022243676952538602222213)
                ·
                  refine ⟨191670689428600987916665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022243676952538602222213 191670689428600987916665)
                  ·
                    rfl

theorem cell21_839874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_839874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839874 prefixEnd_839874 := by exact prefixLift 839874
  have htrace : WordTrace (prefixWord ++ tailWord_839874) baseStart_839874 baseEnd_839874 := by
    simpa [prefixWord, tailWord_839874, baseEnd_839874] using wordTrace_append hprefix tailTrace_839874
  have hstable : (prefixWord ++ tailWord_839874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839874).length < 2 ^ (prefixWord ++ tailWord_839874).sum := by decide
  have hdescent : baseEnd_839874 < baseStart_839874 := by decide
  rcases family_descends (prefixWord ++ tailWord_839874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839882 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_839882 : Nat := 118140960795 + 839882 * 2 ^ 59
def prefixEnd_839882 : Nat := 4983230072969 + 3 ^ 40 * 839882 * 2
def baseEnd_839882 : Nat := 191672515137594751783315

theorem tailTrace_839882 : CollatzResearch.WordTrace tailWord_839882 prefixEnd_839882 191672515137594751783315 := by
  unfold tailWord_839882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658253285814607317708475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20422008762172286180555933 7658253285814607317708475)
  ·
    refine ⟨11487379928721910976562713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7658253285814607317708475 11487379928721910976562713)
    ·
      refine ⟨8615534946541433232422035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11487379928721910976562713 8615534946541433232422035)
      ·
        refine ⟨12923302419812149848633053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8615534946541433232422035 12923302419812149848633053)
        ·
          refine ⟨4846238407429556193237395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12923302419812149848633053 4846238407429556193237395)
          ·
            refine ⟨7269357611144334289856093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4846238407429556193237395 7269357611144334289856093)
            ·
              refine ⟨2726009104179125358696035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7269357611144334289856093 2726009104179125358696035)
              ·
                refine ⟨4089013656268688038044053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726009104179125358696035 4089013656268688038044053)
                ·
                  refine ⟨191672515137594751783315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4089013656268688038044053 191672515137594751783315)
                  ·
                    rfl

theorem cell21_839882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_839882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839882 prefixEnd_839882 := by exact prefixLift 839882
  have htrace : WordTrace (prefixWord ++ tailWord_839882) baseStart_839882 baseEnd_839882 := by
    simpa [prefixWord, tailWord_839882, baseEnd_839882] using wordTrace_append hprefix tailTrace_839882
  have hstable : (prefixWord ++ tailWord_839882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839882).length < 2 ^ (prefixWord ++ tailWord_839882).sum := by decide
  have hdescent : baseEnd_839882 < baseStart_839882 := by decide
  rcases family_descends (prefixWord ++ tailWord_839882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839944 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 5]
def baseStart_839944 : Nat := 118140960795 + 839944 * 2 ^ 59
def prefixEnd_839944 : Nat := 4983230072969 + 3 ^ 40 * 839944 * 2
def baseEnd_839944 : Nat := 191686664382296421749855

theorem tailTrace_839944 : CollatzResearch.WordTrace tailWord_839944 prefixEnd_839944 191686664382296421749855 := by
  unfold tailWord_839944
  simp only [CollatzResearch.WordTrace]
  refine ⟨15317637234516906929795443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20423516312689209239727257 15317637234516906929795443)
  ·
    refine ⟨22976455851775360394693165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15317637234516906929795443 22976455851775360394693165)
    ·
      refine ⟨8616170944415760148009937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22976455851775360394693165 8616170944415760148009937)
      ·
        refine ⟨6462128208311820111007453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8616170944415760148009937 6462128208311820111007453)
        ·
          refine ⟨2423298078116932541627795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6462128208311820111007453 2423298078116932541627795)
          ·
            refine ⟨3634947117175398812441693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423298078116932541627795 3634947117175398812441693)
            ·
              refine ⟨1363105168940774554665635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3634947117175398812441693 1363105168940774554665635)
              ·
                refine ⟨2044657753411161831998453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363105168940774554665635 2044657753411161831998453)
                ·
                  refine ⟨191686664382296421749855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2044657753411161831998453 191686664382296421749855)
                  ·
                    rfl

theorem cell21_839944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_839944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_839944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_839944 prefixEnd_839944 := by exact prefixLift 839944
  have htrace : WordTrace (prefixWord ++ tailWord_839944) baseStart_839944 baseEnd_839944 := by
    simpa [prefixWord, tailWord_839944, baseEnd_839944] using wordTrace_append hprefix tailTrace_839944
  have hstable : (prefixWord ++ tailWord_839944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839944).length < 2 ^ (prefixWord ++ tailWord_839944).sum := by decide
  have hdescent : baseEnd_839944 < baseStart_839944 := by decide
  rcases family_descends (prefixWord ++ tailWord_839944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840020 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 5]
def baseStart_840020 : Nat := 118140960795 + 840020 * 2 ^ 59
def prefixEnd_840020 : Nat := 4983230072969 + 3 ^ 40 * 840020 * 2
def baseEnd_840020 : Nat := 191704008617737178483033

theorem tailTrace_840020 : CollatzResearch.WordTrace tailWord_840020 prefixEnd_840020 191704008617737178483033 := by
  unfold tailWord_840020
  simp only [CollatzResearch.WordTrace]
  refine ⟨15319023208379239419678757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20425364277838985892905009 15319023208379239419678757)
  ·
    refine ⟨2872316851571107391189767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15319023208379239419678757 2872316851571107391189767)
    ·
      refine ⟨4308475277356661086784651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2872316851571107391189767 4308475277356661086784651)
      ·
        refine ⟨6462712916034991630176977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308475277356661086784651 6462712916034991630176977)
        ·
          refine ⟨4847034687026243722632733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6462712916034991630176977 4847034687026243722632733)
          ·
            refine ⟨1817638007634841395987275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4847034687026243722632733 1817638007634841395987275)
            ·
              refine ⟨2726457011452262093980913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817638007634841395987275 2726457011452262093980913)
              ·
                refine ⟨2044842758589196570485685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2726457011452262093980913 2044842758589196570485685)
                ·
                  refine ⟨191704008617737178483033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2044842758589196570485685 191704008617737178483033)
                  ·
                    rfl

theorem cell21_840020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_840020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840020 prefixEnd_840020 := by exact prefixLift 840020
  have htrace : WordTrace (prefixWord ++ tailWord_840020) baseStart_840020 baseEnd_840020 := by
    simpa [prefixWord, tailWord_840020, baseEnd_840020] using wordTrace_append hprefix tailTrace_840020
  have hstable : (prefixWord ++ tailWord_840020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840020).length < 2 ^ (prefixWord ++ tailWord_840020).sum := by decide
  have hdescent : baseEnd_840020 < baseStart_840020 := by decide
  rcases family_descends (prefixWord ++ tailWord_840020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840037 : List Nat := [1, 3, 1, 3, 1, 4, 2, 3, 3]
def baseStart_840037 : Nat := 118140960795 + 840037 * 2 ^ 59
def prefixEnd_840037 : Nat := 4983230072969 + 3 ^ 40 * 840037 * 2
def baseEnd_840037 : Nat := 191707888249348926699665

theorem tailTrace_840037 : CollatzResearch.WordTrace tailWord_840037 prefixEnd_840037 191707888249348926699665 := by
  unfold tailWord_840037
  simp only [CollatzResearch.WordTrace]
  refine ⟨30638666457696890742726365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20425777638464593828484243 30638666457696890742726365)
  ·
    refine ⟨11489499921636334028522387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30638666457696890742726365 11489499921636334028522387)
    ·
      refine ⟨17234249882454501042783581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11489499921636334028522387 17234249882454501042783581)
      ·
        refine ⟨6462843705920437891043843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17234249882454501042783581 6462843705920437891043843)
        ·
          refine ⟨9694265558880656836565765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6462843705920437891043843 9694265558880656836565765)
          ·
            refine ⟨1817674792290123156856081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9694265558880656836565765 1817674792290123156856081)
            ·
              refine ⟨1363256094217592367642061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817674792290123156856081 1363256094217592367642061)
              ·
                refine ⟨511221035331597137865773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1363256094217592367642061 511221035331597137865773)
                ·
                  refine ⟨191707888249348926699665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511221035331597137865773 191707888249348926699665)
                  ·
                    rfl

theorem cell21_840037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_840037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840037 prefixEnd_840037 := by exact prefixLift 840037
  have htrace : WordTrace (prefixWord ++ tailWord_840037) baseStart_840037 baseEnd_840037 := by
    simpa [prefixWord, tailWord_840037, baseEnd_840037] using wordTrace_append hprefix tailTrace_840037
  have hstable : (prefixWord ++ tailWord_840037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840037).length < 2 ^ (prefixWord ++ tailWord_840037).sum := by decide
  have hdescent : baseEnd_840037 < baseStart_840037 := by decide
  rcases family_descends (prefixWord ++ tailWord_840037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840048 : List Nat := [2, 1, 1, 1, 4, 4, 8]
def baseStart_840048 : Nat := 118140960795 + 840048 * 2 ^ 59
def prefixEnd_840048 : Nat := 4983230072969 + 3 ^ 40 * 840048 * 2
def baseEnd_840048 : Nat := 21301155399912816890701

theorem tailTrace_840048 : CollatzResearch.WordTrace tailWord_840048 prefixEnd_840048 21301155399912816890701 := by
  unfold tailWord_840048
  simp only [CollatzResearch.WordTrace]
  refine ⟨15319533830328519810688399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20426045107104693080917865 15319533830328519810688399)
  ·
    refine ⟨22979300745492779716032599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15319533830328519810688399 22979300745492779716032599)
    ·
      refine ⟨34468951118239169574048899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22979300745492779716032599 34468951118239169574048899)
      ·
        refine ⟨51703426677358754361073349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34468951118239169574048899 51703426677358754361073349)
        ·
          refine ⟨9694392502004766442701253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51703426677358754361073349 9694392502004766442701253)
          ·
            refine ⟨1817698594125893708006485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9694392502004766442701253 1817698594125893708006485)
            ·
              refine ⟨21301155399912816890701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1817698594125893708006485 21301155399912816890701)
              ·
                rfl

theorem cell21_840048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 8].length) (baseStart_840048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840048 prefixEnd_840048 := by exact prefixLift 840048
  have htrace : WordTrace (prefixWord ++ tailWord_840048) baseStart_840048 baseEnd_840048 := by
    simpa [prefixWord, tailWord_840048, baseEnd_840048] using wordTrace_append hprefix tailTrace_840048
  have hstable : (prefixWord ++ tailWord_840048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840048).length < 2 ^ (prefixWord ++ tailWord_840048).sum := by decide
  have hdescent : baseEnd_840048 < baseStart_840048 := by decide
  rcases family_descends (prefixWord ++ tailWord_840048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840054 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_840054 : Nat := 118140960795 + 840054 * 2 ^ 59
def prefixEnd_840054 : Nat := 4983230072969 + 3 ^ 40 * 840054 * 2
def baseEnd_840054 : Nat := 191711767880960674916297

theorem tailTrace_840054 : CollatzResearch.WordTrace tailWord_840054 prefixEnd_840054 191711767880960674916297 := by
  unfold tailWord_840054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914955406164706415380951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20426190999090201764063477 1914955406164706415380951)
  ·
    refine ⟨2872433109247059623071427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1914955406164706415380951 2872433109247059623071427)
    ·
      refine ⟨4308649663870589434607141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2872433109247059623071427 4308649663870589434607141)
      ·
        refine ⟨807871811975735518988839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4308649663870589434607141 807871811975735518988839)
        ·
          refine ⟨1211807717963603278483259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807871811975735518988839 1211807717963603278483259)
          ·
            refine ⟨1817711576945404917724889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211807717963603278483259 1817711576945404917724889)
            ·
              refine ⟨1363283682709053688293667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817711576945404917724889 1363283682709053688293667)
              ·
                refine ⟨2044925524063580532440501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363283682709053688293667 2044925524063580532440501)
                ·
                  refine ⟨191711767880960674916297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2044925524063580532440501 191711767880960674916297)
                  ·
                    rfl

theorem cell21_840054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_840054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840054 prefixEnd_840054 := by exact prefixLift 840054
  have htrace : WordTrace (prefixWord ++ tailWord_840054) baseStart_840054 baseEnd_840054 := by
    simpa [prefixWord, tailWord_840054, baseEnd_840054] using wordTrace_append hprefix tailTrace_840054
  have hstable : (prefixWord ++ tailWord_840054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840054).length < 2 ^ (prefixWord ++ tailWord_840054).sum := by decide
  have hdescent : baseEnd_840054 < baseStart_840054 := by decide
  rcases family_descends (prefixWord ++ tailWord_840054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840172 : List Nat := [2, 2, 1, 1, 2, 1, 5, 4, 3]
def baseStart_840172 : Nat := 118140960795 + 840172 * 2 ^ 59
def prefixEnd_840172 : Nat := 4983230072969 + 3 ^ 40 * 840172 * 2
def baseEnd_840172 : Nat := 191738697088618691949389

theorem tailTrace_840172 : CollatzResearch.WordTrace tailWord_840172 prefixEnd_840172 191738697088618691949389 := by
  unfold tailWord_840172
  simp only [CollatzResearch.WordTrace]
  refine ⟨15321795156103904399445385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20429060208138539199260513 15321795156103904399445385)
  ·
    refine ⟨11491346367077928299584039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15321795156103904399445385 11491346367077928299584039)
    ·
      refine ⟨17237019550616892449376059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11491346367077928299584039 17237019550616892449376059)
      ·
        refine ⟨25855529325925338674064089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17237019550616892449376059 25855529325925338674064089)
        ·
          refine ⟨19391646994444004005548067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25855529325925338674064089 19391646994444004005548067)
          ·
            refine ⟨29087470491666006008322101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19391646994444004005548067 29087470491666006008322101)
            ·
              refine ⟨2726950358593688063280197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29087470491666006008322101 2726950358593688063280197)
              ·
                refine ⟨511303192236316511865037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2726950358593688063280197 511303192236316511865037)
                ·
                  refine ⟨191738697088618691949389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511303192236316511865037 191738697088618691949389)
                  ·
                    rfl

theorem cell21_840172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_840172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840172 prefixEnd_840172 := by exact prefixLift 840172
  have htrace : WordTrace (prefixWord ++ tailWord_840172) baseStart_840172 baseEnd_840172 := by
    simpa [prefixWord, tailWord_840172, baseEnd_840172] using wordTrace_append hprefix tailTrace_840172
  have hstable : (prefixWord ++ tailWord_840172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840172).length < 2 ^ (prefixWord ++ tailWord_840172).sum := by decide
  have hdescent : baseEnd_840172 < baseStart_840172 := by decide
  rcases family_descends (prefixWord ++ tailWord_840172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840276 : List Nat := [2, 4, 1, 1, 1, 3, 9]
def baseStart_840276 : Nat := 118140960795 + 840276 * 2 ^ 59
def prefixEnd_840276 : Nat := 4983230072969 + 3 ^ 40 * 840276 * 2
def baseEnd_840276 : Nat := 21306936811726402468427

theorem tailTrace_840276 : CollatzResearch.WordTrace tailWord_840276 prefixEnd_840276 21306936811726402468427 := by
  unfold tailWord_840276
  simp only [CollatzResearch.WordTrace]
  refine ⟨15323691751915517280338341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20431589002554023040451121 15323691751915517280338341)
  ·
    refine ⟨2873192203484159490063439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15323691751915517280338341 2873192203484159490063439)
    ·
      refine ⟨4309788305226239235095159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2873192203484159490063439 4309788305226239235095159)
      ·
        refine ⟨6464682457839358852642739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4309788305226239235095159 6464682457839358852642739)
        ·
          refine ⟨9697023686759038278964109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6464682457839358852642739 9697023686759038278964109)
          ·
            refine ⟨3636383882534639354611541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9697023686759038278964109 3636383882534639354611541)
            ·
              refine ⟨21306936811726402468427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3636383882534639354611541 21306936811726402468427)
              ·
                rfl

theorem cell21_840276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 9].length) (baseStart_840276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840276 prefixEnd_840276 := by exact prefixLift 840276
  have htrace : WordTrace (prefixWord ++ tailWord_840276) baseStart_840276 baseEnd_840276 := by
    simpa [prefixWord, tailWord_840276, baseEnd_840276] using wordTrace_append hprefix tailTrace_840276
  have hstable : (prefixWord ++ tailWord_840276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840276).length < 2 ^ (prefixWord ++ tailWord_840276).sum := by decide
  have hdescent : baseEnd_840276 < baseStart_840276 := by decide
  rcases family_descends (prefixWord ++ tailWord_840276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840293 : List Nat := [1, 3, 1, 3, 4, 1, 2, 6]
def baseStart_840293 : Nat := 118140960795 + 840293 * 2 ^ 59
def prefixEnd_840293 : Nat := 4983230072969 + 3 ^ 40 * 840293 * 2
def baseEnd_840293 : Nat := 63922103645716456810825

theorem tailTrace_840293 : CollatzResearch.WordTrace tailWord_840293 prefixEnd_840293 63922103645716456810825 := by
  unfold tailWord_840293
  simp only [CollatzResearch.WordTrace]
  refine ⟨30648003544769446464045533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20432002363179630976030355 30648003544769446464045533)
  ·
    refine ⟨11493001329288542424017075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30648003544769446464045533 11493001329288542424017075)
    ·
      refine ⟨17239501993932813636025613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11493001329288542424017075 17239501993932813636025613)
      ·
        refine ⟨6464813247724805113509605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17239501993932813636025613 6464813247724805113509605)
        ·
          refine ⟨1212152483948400958783051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6464813247724805113509605 1212152483948400958783051)
          ·
            refine ⟨1818228725922601438174577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212152483948400958783051 1818228725922601438174577)
            ·
              refine ⟨1363671544441951078630933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1818228725922601438174577 1363671544441951078630933)
              ·
                refine ⟨63922103645716456810825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1363671544441951078630933 63922103645716456810825)
                ·
                  rfl

theorem cell21_840293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 6].length) (baseStart_840293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840293 prefixEnd_840293 := by exact prefixLift 840293
  have htrace : WordTrace (prefixWord ++ tailWord_840293) baseStart_840293 baseEnd_840293 := by
    simpa [prefixWord, tailWord_840293, baseEnd_840293] using wordTrace_append hprefix tailTrace_840293
  have hstable : (prefixWord ++ tailWord_840293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840293).length < 2 ^ (prefixWord ++ tailWord_840293).sum := by decide
  have hdescent : baseEnd_840293 < baseStart_840293 := by decide
  rcases family_descends (prefixWord ++ tailWord_840293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840442 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_840442 : Nat := 118140960795 + 840442 * 2 ^ 59
def prefixEnd_840442 : Nat := 4983230072969 + 3 ^ 40 * 840442 * 2
def baseEnd_840442 : Nat := 191800314767158222448837

theorem tailTrace_840442 : CollatzResearch.WordTrace tailWord_840442 prefixEnd_840442 191800314767158222448837 := by
  unfold tailWord_840442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7663359505307411227804895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20435625347486429940813053 7663359505307411227804895)
  ·
    refine ⟨11495039257961116841707343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7663359505307411227804895 11495039257961116841707343)
    ·
      refine ⟨17242558886941675262561015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11495039257961116841707343 17242558886941675262561015)
      ·
        refine ⟨25863838330412512893841523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17242558886941675262561015 25863838330412512893841523)
        ·
          refine ⟨38795757495618769340762285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25863838330412512893841523 38795757495618769340762285)
          ·
            refine ⟨14548409060857038502785857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38795757495618769340762285 14548409060857038502785857)
            ·
              refine ⟨10911306795642778877089393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14548409060857038502785857 10911306795642778877089393)
              ·
                refine ⟨8183480096732084157817045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10911306795642778877089393 8183480096732084157817045)
                ·
                  refine ⟨191800314767158222448837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8183480096732084157817045 191800314767158222448837)
                  ·
                    rfl

theorem cell21_840442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_840442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840442 prefixEnd_840442 := by exact prefixLift 840442
  have htrace : WordTrace (prefixWord ++ tailWord_840442) baseStart_840442 baseEnd_840442 := by
    simpa [prefixWord, tailWord_840442, baseEnd_840442] using wordTrace_append hprefix tailTrace_840442
  have hstable : (prefixWord ++ tailWord_840442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840442).length < 2 ^ (prefixWord ++ tailWord_840442).sum := by decide
  have hdescent : baseEnd_840442 < baseStart_840442 := by decide
  rcases family_descends (prefixWord ++ tailWord_840442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840535 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 5]
def baseStart_840535 : Nat := 118140960795 + 840535 * 2 ^ 59
def prefixEnd_840535 : Nat := 4983230072969 + 3 ^ 40 * 840535 * 2
def baseEnd_840535 : Nat := 191821538634210727398647

theorem tailTrace_840535 : CollatzResearch.WordTrace tailWord_840535 prefixEnd_840535 191821538634210727398647 := by
  unfold tailWord_840535
  simp only [CollatzResearch.WordTrace]
  refine ⟨30656830009892721794355059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20437886673261814529570039 30656830009892721794355059)
  ·
    refine ⟨45985245014839082691532589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30656830009892721794355059 45985245014839082691532589)
    ·
      refine ⟨17244466880564656009324721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45985245014839082691532589 17244466880564656009324721)
      ·
        refine ⟨12933350160423492006993541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17244466880564656009324721 12933350160423492006993541)
        ·
          refine ⟨2425003155079404751311289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12933350160423492006993541 2425003155079404751311289)
          ·
            refine ⟨1818752366309553563483467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2425003155079404751311289 1818752366309553563483467)
            ·
              refine ⟨2728128549464330345225201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1818752366309553563483467 2728128549464330345225201)
              ·
                refine ⟨2046096412098247758918901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2728128549464330345225201 2046096412098247758918901)
                ·
                  refine ⟨191821538634210727398647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2046096412098247758918901 191821538634210727398647)
                  ·
                    rfl

theorem cell21_840535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 5].length) (baseStart_840535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840535 prefixEnd_840535 := by exact prefixLift 840535
  have htrace : WordTrace (prefixWord ++ tailWord_840535) baseStart_840535 baseEnd_840535 := by
    simpa [prefixWord, tailWord_840535, baseEnd_840535] using wordTrace_append hprefix tailTrace_840535
  have hstable : (prefixWord ++ tailWord_840535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840535).length < 2 ^ (prefixWord ++ tailWord_840535).sum := by decide
  have hdescent : baseEnd_840535 < baseStart_840535 := by decide
  rcases family_descends (prefixWord ++ tailWord_840535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840552 : List Nat := [2, 1, 4, 2, 1, 2, 1, 5, 3]
def baseStart_840552 : Nat := 118140960795 + 840552 * 2 ^ 59
def prefixEnd_840552 : Nat := 4983230072969 + 3 ^ 40 * 840552 * 2
def baseEnd_840552 : Nat := 191825418265822475615279

theorem tailTrace_840552 : CollatzResearch.WordTrace tailWord_840552 prefixEnd_840552 191825418265822475615279 := by
  unfold tailWord_840552
  simp only [CollatzResearch.WordTrace]
  refine ⟨15328725025415566848861955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20438300033887422465149273 15328725025415566848861955)
  ·
    refine ⟨22993087538123350273292933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15328725025415566848861955 22993087538123350273292933)
    ·
      refine ⟨4311203913398128176242425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22993087538123350273292933 4311203913398128176242425)
      ·
        refine ⟨3233402935048596132181819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4311203913398128176242425 3233402935048596132181819)
        ·
          refine ⟨4850104402572894198272729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3233402935048596132181819 4850104402572894198272729)
          ·
            refine ⟨3637578301929670648704547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4850104402572894198272729 3637578301929670648704547)
            ·
              refine ⟨5456367452894505973056821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3637578301929670648704547 5456367452894505973056821)
              ·
                refine ⟨511534448708859934974077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5456367452894505973056821 511534448708859934974077)
                ·
                  refine ⟨191825418265822475615279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511534448708859934974077 191825418265822475615279)
                  ·
                    rfl

theorem cell21_840552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 3].length) (baseStart_840552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840552 prefixEnd_840552 := by exact prefixLift 840552
  have htrace : WordTrace (prefixWord ++ tailWord_840552) baseStart_840552 baseEnd_840552 := by
    simpa [prefixWord, tailWord_840552, baseEnd_840552] using wordTrace_append hprefix tailTrace_840552
  have hstable : (prefixWord ++ tailWord_840552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840552).length < 2 ^ (prefixWord ++ tailWord_840552).sum := by decide
  have hdescent : baseEnd_840552 < baseStart_840552 := by decide
  rcases family_descends (prefixWord ++ tailWord_840552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840583 : List Nat := [1, 1, 4, 2, 3, 2, 3, 1, 4]
def baseStart_840583 : Nat := 118140960795 + 840583 * 2 ^ 59
def prefixEnd_840583 : Nat := 4983230072969 + 3 ^ 40 * 840583 * 2
def baseEnd_840583 : Nat := 191832492888173310598549

theorem tailTrace_840583 : CollatzResearch.WordTrace tailWord_840583 prefixEnd_840583 191832492888173310598549 := by
  unfold tailWord_840583
  simp only [CollatzResearch.WordTrace]
  refine ⟨30658580713718825992102403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20439053809145883994734935 30658580713718825992102403)
  ·
    refine ⟨45987871070578238988153605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30658580713718825992102403 45987871070578238988153605)
    ·
      refine ⟨8622725825733419810278801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45987871070578238988153605 8622725825733419810278801)
      ·
        refine ⟨6467044369300064857709101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8622725825733419810278801 6467044369300064857709101)
        ·
          refine ⟨2425141638487524321640913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6467044369300064857709101 2425141638487524321640913)
          ·
            refine ⟨1818856228865643241230685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2425141638487524321640913 1818856228865643241230685)
            ·
              refine ⟨682071085824616215461507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1818856228865643241230685 682071085824616215461507)
              ·
                refine ⟨1023106628736924323192261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682071085824616215461507 1023106628736924323192261)
                ·
                  refine ⟨191832492888173310598549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1023106628736924323192261 191832492888173310598549)
                  ·
                    rfl

theorem cell21_840583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 4].length) (baseStart_840583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840583 prefixEnd_840583 := by exact prefixLift 840583
  have htrace : WordTrace (prefixWord ++ tailWord_840583) baseStart_840583 baseEnd_840583 := by
    simpa [prefixWord, tailWord_840583, baseEnd_840583] using wordTrace_append hprefix tailTrace_840583
  have hstable : (prefixWord ++ tailWord_840583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840583).length < 2 ^ (prefixWord ++ tailWord_840583).sum := by decide
  have hdescent : baseEnd_840583 < baseStart_840583 := by decide
  rcases family_descends (prefixWord ++ tailWord_840583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840597 : List Nat := [1, 3, 2, 1, 1, 6, 2, 5]
def baseStart_840597 : Nat := 118140960795 + 840597 * 2 ^ 59
def prefixEnd_840597 : Nat := 4983230072969 + 3 ^ 40 * 840597 * 2
def baseEnd_840597 : Nat := 63945229292970799121729

theorem tailTrace_840597 : CollatzResearch.WordTrace tailWord_840597 prefixEnd_840597 63945229292970799121729 := by
  unfold tailWord_840597
  simp only [CollatzResearch.WordTrace]
  refine ⟨30659091335668106383112045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20439394223778737588741363 30659091335668106383112045)
  ·
    refine ⟨11497159250875539893667017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30659091335668106383112045 11497159250875539893667017)
    ·
      refine ⟨8622869438156654920250263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11497159250875539893667017 8622869438156654920250263)
      ·
        refine ⟨12934304157234982380375395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8622869438156654920250263 12934304157234982380375395)
        ·
          refine ⟨19401456235852473570563093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12934304157234982380375395 19401456235852473570563093)
          ·
            refine ⟨909443261055584698620145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19401456235852473570563093 909443261055584698620145)
            ·
              refine ⟨682082445791688523965109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909443261055584698620145 682082445791688523965109)
              ·
                refine ⟨63945229292970799121729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 682082445791688523965109 63945229292970799121729)
                ·
                  rfl

theorem cell21_840597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 5].length) (baseStart_840597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840597 prefixEnd_840597 := by exact prefixLift 840597
  have htrace : WordTrace (prefixWord ++ tailWord_840597) baseStart_840597 baseEnd_840597 := by
    simpa [prefixWord, tailWord_840597, baseEnd_840597] using wordTrace_append hprefix tailTrace_840597
  have hstable : (prefixWord ++ tailWord_840597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840597).length < 2 ^ (prefixWord ++ tailWord_840597).sum := by decide
  have hdescent : baseEnd_840597 < baseStart_840597 := by decide
  rcases family_descends (prefixWord ++ tailWord_840597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840690 : List Nat := [3, 2, 1, 5, 1, 2, 1, 6]
def baseStart_840690 : Nat := 118140960795 + 840690 * 2 ^ 59
def prefixEnd_840690 : Nat := 4983230072969 + 3 ^ 40 * 840690 * 2
def baseEnd_840690 : Nat := 63952303915321634104999

theorem tailTrace_840690 : CollatzResearch.WordTrace tailWord_840690 prefixEnd_840690 63952303915321634104999 := by
  unfold tailWord_840690
  simp only [CollatzResearch.WordTrace]
  refine ⟨7665620831082795816561881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20441655549554122177498349 7665620831082795816561881)
  ·
    refine ⟨5749215623312096862421411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7665620831082795816561881 5749215623312096862421411)
    ·
      refine ⟨8623823434968145293632117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5749215623312096862421411 8623823434968145293632117)
      ·
        refine ⟨808483447028263621278011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8623823434968145293632117 808483447028263621278011)
        ·
          refine ⟨1212725170542395431917017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808483447028263621278011 1212725170542395431917017)
          ·
            refine ⟨909543877906796573937763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212725170542395431917017 909543877906796573937763)
            ·
              refine ⟨1364315816860194860906645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909543877906796573937763 1364315816860194860906645)
              ·
                refine ⟨63952303915321634104999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1364315816860194860906645 63952303915321634104999)
                ·
                  rfl

theorem cell21_840690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_840690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840690 prefixEnd_840690 := by exact prefixLift 840690
  have htrace : WordTrace (prefixWord ++ tailWord_840690) baseStart_840690 baseEnd_840690 := by
    simpa [prefixWord, tailWord_840690, baseEnd_840690] using wordTrace_append hprefix tailTrace_840690
  have hstable : (prefixWord ++ tailWord_840690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840690).length < 2 ^ (prefixWord ++ tailWord_840690).sum := by decide
  have hdescent : baseEnd_840690 < baseStart_840690 := by decide
  rcases family_descends (prefixWord ++ tailWord_840690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840732 : List Nat := [2, 2, 3, 1, 4, 1, 8]
def baseStart_840732 : Nat := 118140960795 + 840732 * 2 ^ 59
def prefixEnd_840732 : Nat := 4983230072969 + 3 ^ 40 * 840732 * 2
def baseEnd_840732 : Nat := 21318499635353573623879

theorem tailTrace_840732 : CollatzResearch.WordTrace tailWord_840732 prefixEnd_840732 21318499635353573623879 := by
  unfold tailWord_840732
  simp only [CollatzResearch.WordTrace]
  refine ⟨15332007595089512219638225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20442676793452682959517633 15332007595089512219638225)
  ·
    refine ⟨11499005696317134164728669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15332007595089512219638225 11499005696317134164728669)
    ·
      refine ⟨4312127136118925311773251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11499005696317134164728669 4312127136118925311773251)
      ·
        refine ⟨6468190704178387967659877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4312127136118925311773251 6468190704178387967659877)
        ·
          refine ⟨1212785757033447743936227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6468190704178387967659877 1212785757033447743936227)
          ·
            refine ⟨1819178635550171615904341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212785757033447743936227 1819178635550171615904341)
            ·
              refine ⟨21318499635353573623879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1819178635550171615904341 21318499635353573623879)
              ·
                rfl

theorem cell21_840732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 8].length) (baseStart_840732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840732 prefixEnd_840732 := by exact prefixLift 840732
  have htrace : WordTrace (prefixWord ++ tailWord_840732) baseStart_840732 baseEnd_840732 := by
    simpa [prefixWord, tailWord_840732, baseEnd_840732] using wordTrace_append hprefix tailTrace_840732
  have hstable : (prefixWord ++ tailWord_840732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840732).length < 2 ^ (prefixWord ++ tailWord_840732).sum := by decide
  have hdescent : baseEnd_840732 < baseStart_840732 := by decide
  rcases family_descends (prefixWord ++ tailWord_840732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840766 : List Nat := [4, 2, 1, 3, 1, 3, 2, 5]
def baseStart_840766 : Nat := 118140960795 + 840766 * 2 ^ 59
def prefixEnd_840766 : Nat := 4983230072969 + 3 ^ 40 * 840766 * 2
def baseEnd_840766 : Nat := 63958085327135219682725

theorem tailTrace_840766 : CollatzResearch.WordTrace tailWord_840766 prefixEnd_840766 63958085327135219682725 := by
  unfold tailWord_840766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3833156909006981030751769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20443503514703898830676101 3833156909006981030751769)
  ·
    refine ⟨2874867681755235773063827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3833156909006981030751769 2874867681755235773063827)
    ·
      refine ⟨4312301522632853659595741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2874867681755235773063827 4312301522632853659595741)
      ·
        refine ⟨1617113070987320122348403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4312301522632853659595741 1617113070987320122348403)
        ·
          refine ⟨2425669606480980183522605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617113070987320122348403 2425669606480980183522605)
          ·
            refine ⟨909626102430367568820977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2425669606480980183522605 909626102430367568820977)
            ·
              refine ⟨682219576822775676615733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909626102430367568820977 682219576822775676615733)
              ·
                refine ⟨63958085327135219682725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 682219576822775676615733 63958085327135219682725)
                ·
                  rfl

theorem cell21_840766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_840766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840766 prefixEnd_840766 := by exact prefixLift 840766
  have htrace : WordTrace (prefixWord ++ tailWord_840766) baseStart_840766 baseEnd_840766 := by
    simpa [prefixWord, tailWord_840766, baseEnd_840766] using wordTrace_append hprefix tailTrace_840766
  have hstable : (prefixWord ++ tailWord_840766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840766).length < 2 ^ (prefixWord ++ tailWord_840766).sum := by decide
  have hdescent : baseEnd_840766 < baseStart_840766 := by decide
  rcases family_descends (prefixWord ++ tailWord_840766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840797 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 5]
def baseStart_840797 : Nat := 118140960795 + 840797 * 2 ^ 59
def prefixEnd_840797 : Nat := 4983230072969 + 3 ^ 40 * 840797 * 2
def baseEnd_840797 : Nat := 191881330603756494031445

theorem tailTrace_840797 : CollatzResearch.WordTrace tailWord_840797 prefixEnd_840797 191881330603756494031445 := by
  unfold tailWord_840797
  simp only [CollatzResearch.WordTrace]
  refine ⟨30666385934943540540392645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20444257289962360360261763 30666385934943540540392645)
  ·
    refine ⟨5749947362801913851323621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30666385934943540540392645 5749947362801913851323621)
    ·
      refine ⟨1078115130525358847123179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5749947362801913851323621 1078115130525358847123179)
      ·
        refine ⟨1617172695788038270684769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078115130525358847123179 1617172695788038270684769)
        ·
          refine ⟨1212879521841028703013577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1617172695788038270684769 1212879521841028703013577)
          ·
            refine ⟨909659641380771527260183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212879521841028703013577 909659641380771527260183)
            ·
              refine ⟨1364489462071157290890275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909659641380771527260183 1364489462071157290890275)
              ·
                refine ⟨2046734193106735936335413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364489462071157290890275 2046734193106735936335413)
                ·
                  refine ⟨191881330603756494031445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2046734193106735936335413 191881330603756494031445)
                  ·
                    rfl

theorem cell21_840797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_840797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840797 prefixEnd_840797 := by exact prefixLift 840797
  have htrace : WordTrace (prefixWord ++ tailWord_840797) baseStart_840797 baseEnd_840797 := by
    simpa [prefixWord, tailWord_840797, baseEnd_840797] using wordTrace_append hprefix tailTrace_840797
  have hstable : (prefixWord ++ tailWord_840797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840797).length < 2 ^ (prefixWord ++ tailWord_840797).sum := by decide
  have hdescent : baseEnd_840797 < baseStart_840797 := by decide
  rcases family_descends (prefixWord ++ tailWord_840797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840839 : List Nat := [1, 1, 4, 2, 1, 1, 1, 7, 3]
def baseStart_840839 : Nat := 118140960795 + 840839 * 2 ^ 59
def prefixEnd_840839 : Nat := 4983230072969 + 3 ^ 40 * 840839 * 2
def baseEnd_840839 : Nat := 191890915575973754331359

theorem tailTrace_840839 : CollatzResearch.WordTrace tailWord_840839 prefixEnd_840839 191890915575973754331359 := by
  unfold tailWord_840839
  simp only [CollatzResearch.WordTrace]
  refine ⟨30667917800791381713421571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20445278533860921142281047 30667917800791381713421571)
  ·
    refine ⟨46001876701187072570132357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30667917800791381713421571 46001876701187072570132357)
    ·
      refine ⟨8625351881472576106899817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46001876701187072570132357 8625351881472576106899817)
      ·
        refine ⟨6469013911104432080174863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8625351881472576106899817 6469013911104432080174863)
        ·
          refine ⟨9703520866656648120262295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6469013911104432080174863 9703520866656648120262295)
          ·
            refine ⟨14555281299984972180393443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9703520866656648120262295 14555281299984972180393443)
            ·
              refine ⟨21832921949977458270590165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14555281299984972180393443 21832921949977458270590165)
              ·
                refine ⟨511709108202596678216957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21832921949977458270590165 511709108202596678216957)
                ·
                  refine ⟨191890915575973754331359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511709108202596678216957 191890915575973754331359)
                  ·
                    rfl

theorem cell21_840839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 3].length) (baseStart_840839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840839 prefixEnd_840839 := by exact prefixLift 840839
  have htrace : WordTrace (prefixWord ++ tailWord_840839) baseStart_840839 baseEnd_840839 := by
    simpa [prefixWord, tailWord_840839, baseEnd_840839] using wordTrace_append hprefix tailTrace_840839
  have hstable : (prefixWord ++ tailWord_840839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840839).length < 2 ^ (prefixWord ++ tailWord_840839).sum := by decide
  have hdescent : baseEnd_840839 < baseStart_840839 := by decide
  rcases family_descends (prefixWord ++ tailWord_840839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840856 : List Nat := [2, 1, 2, 4, 2, 2, 1, 4, 3]
def baseStart_840856 : Nat := 118140960795 + 840856 * 2 ^ 59
def prefixEnd_840856 : Nat := 4983230072969 + 3 ^ 40 * 840856 * 2
def baseEnd_840856 : Nat := 191894795207585502547991

theorem tailTrace_840856 : CollatzResearch.WordTrace tailWord_840856 prefixEnd_840856 191894795207585502547991 := by
  unfold tailWord_840856
  simp only [CollatzResearch.WordTrace]
  refine ⟨15334268920864896808395211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20445691894486529077860281 15334268920864896808395211)
  ·
    refine ⟨23001403381297345212592817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15334268920864896808395211 23001403381297345212592817)
    ·
      refine ⟨17251052535973008909444613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23001403381297345212592817 17251052535973008909444613)
      ·
        refine ⟨3234572350494939170520865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17251052535973008909444613 3234572350494939170520865)
        ·
          refine ⟨2425929262871204377890649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3234572350494939170520865 2425929262871204377890649)
          ·
            refine ⟨1819446947153403283417987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2425929262871204377890649 1819446947153403283417987)
            ·
              refine ⟨2729170420730104925126981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819446947153403283417987 2729170420730104925126981)
              ·
                refine ⟨511719453886894673461309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2729170420730104925126981 511719453886894673461309)
                ·
                  refine ⟨191894795207585502547991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511719453886894673461309 191894795207585502547991)
                  ·
                    rfl

theorem cell21_840856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 3].length) (baseStart_840856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_840856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_840856 prefixEnd_840856 := by exact prefixLift 840856
  have htrace : WordTrace (prefixWord ++ tailWord_840856) baseStart_840856 baseEnd_840856 := by
    simpa [prefixWord, tailWord_840856, baseEnd_840856] using wordTrace_append hprefix tailTrace_840856
  have hstable : (prefixWord ++ tailWord_840856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840856).length < 2 ^ (prefixWord ++ tailWord_840856).sum := by decide
  have hdescent : baseEnd_840856 < baseStart_840856 := by decide
  rcases family_descends (prefixWord ++ tailWord_840856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841022 : List Nat := [4, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_841022 : Nat := 118140960795 + 841022 * 2 ^ 59
def prefixEnd_841022 : Nat := 4983230072969 + 3 ^ 40 * 841022 * 2
def baseEnd_841022 : Nat := 191932678669206102780985

theorem tailTrace_841022 : CollatzResearch.WordTrace tailWord_841022 prefixEnd_841022 191932678669206102780985 := by
  unfold tailWord_841022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3834324044891050495916665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20449728239418935978222213 3834324044891050495916665)
  ·
    refine ⟨2875743033668287871937499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3834324044891050495916665 2875743033668287871937499)
    ·
      refine ⟨4313614550502431807906249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2875743033668287871937499 4313614550502431807906249)
      ·
        refine ⟨3235210912876823855929687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4313614550502431807906249 3235210912876823855929687)
        ·
          refine ⟨4852816369315235783894531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235210912876823855929687 4852816369315235783894531)
          ·
            refine ⟨7279224553972853675841797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4852816369315235783894531 7279224553972853675841797)
            ·
              refine ⟨1364854603869910064220337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7279224553972853675841797 1364854603869910064220337)
              ·
                refine ⟨1023640952902432548165253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364854603869910064220337 1023640952902432548165253)
                ·
                  refine ⟨191932678669206102780985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1023640952902432548165253 191932678669206102780985)
                  ·
                    rfl

theorem cell21_841022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_841022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841022 prefixEnd_841022 := by exact prefixLift 841022
  have htrace : WordTrace (prefixWord ++ tailWord_841022) baseStart_841022 baseEnd_841022 := by
    simpa [prefixWord, tailWord_841022, baseEnd_841022] using wordTrace_append hprefix tailTrace_841022
  have hstable : (prefixWord ++ tailWord_841022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841022).length < 2 ^ (prefixWord ++ tailWord_841022).sum := by decide
  have hdescent : baseEnd_841022 < baseStart_841022 := by decide
  rcases family_descends (prefixWord ++ tailWord_841022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841025 : List Nat := [1, 2, 5, 2, 1, 1, 4, 2, 3]
def baseStart_841025 : Nat := 118140960795 + 841025 * 2 ^ 59
def prefixEnd_841025 : Nat := 4983230072969 + 3 ^ 40 * 841025 * 2
def baseEnd_841025 : Nat := 191933363310078764230979

theorem tailTrace_841025 : CollatzResearch.WordTrace tailWord_841025 prefixEnd_841025 191933363310078764230979 := by
  unfold tailWord_841025
  simp only [CollatzResearch.WordTrace]
  refine ⟨30674701778117535479692529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20449801185411690319795019 30674701778117535479692529)
  ·
    refine ⟨23006026333588151609769397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30674701778117535479692529 23006026333588151609769397)
    ·
      refine ⟨2156814968773889213415881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23006026333588151609769397 2156814968773889213415881)
      ·
        refine ⟨1617611226580416910061911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2156814968773889213415881 1617611226580416910061911)
        ·
          refine ⟨2426416839870625365092867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617611226580416910061911 2426416839870625365092867)
          ·
            refine ⟨3639625259805938047639301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426416839870625365092867 3639625259805938047639301)
            ·
              refine ⟨682429736213613383932369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3639625259805938047639301 682429736213613383932369)
              ·
                refine ⟨511822302160210037949277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682429736213613383932369 511822302160210037949277)
                ·
                  refine ⟨191933363310078764230979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511822302160210037949277 191933363310078764230979)
                  ·
                    rfl

theorem cell21_841025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 3].length) (baseStart_841025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841025 prefixEnd_841025 := by exact prefixLift 841025
  have htrace : WordTrace (prefixWord ++ tailWord_841025) baseStart_841025 baseEnd_841025 := by
    simpa [prefixWord, tailWord_841025, baseEnd_841025] using wordTrace_append hprefix tailTrace_841025
  have hstable : (prefixWord ++ tailWord_841025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841025).length < 2 ^ (prefixWord ++ tailWord_841025).sum := by decide
  have hdescent : baseEnd_841025 < baseStart_841025 := by decide
  rcases family_descends (prefixWord ++ tailWord_841025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841036 : List Nat := [2, 2, 1, 3, 2, 4, 1, 6]
def baseStart_841036 : Nat := 118140960795 + 841036 * 2 ^ 59
def prefixEnd_841036 : Nat := 4983230072969 + 3 ^ 40 * 841036 * 2
def baseEnd_841036 : Nat := 63978624553315063182541

theorem tailTrace_841036 : CollatzResearch.WordTrace tailWord_841036 prefixEnd_841036 63978624553315063182541 := by
  unfold tailWord_841036
  simp only [CollatzResearch.WordTrace]
  refine ⟨15337551490538842179171481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20450068654051789572228641 15337551490538842179171481)
  ·
    refine ⟨11503163617904131634378611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15337551490538842179171481 11503163617904131634378611)
    ·
      refine ⟨17254745426856197451567917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11503163617904131634378611 17254745426856197451567917)
      ·
        refine ⟨6470529535071074044337969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17254745426856197451567917 6470529535071074044337969)
        ·
          refine ⟨4852897151303305533253477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6470529535071074044337969 4852897151303305533253477)
          ·
            refine ⟨909918215869369787485027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4852897151303305533253477 909918215869369787485027)
            ·
              refine ⟨1364877323804054681227541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909918215869369787485027 1364877323804054681227541)
              ·
                refine ⟨63978624553315063182541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1364877323804054681227541 63978624553315063182541)
                ·
                  rfl

theorem cell21_841036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 6].length) (baseStart_841036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841036 prefixEnd_841036 := by exact prefixLift 841036
  have htrace : WordTrace (prefixWord ++ tailWord_841036) baseStart_841036 baseEnd_841036 := by
    simpa [prefixWord, tailWord_841036, baseEnd_841036] using wordTrace_append hprefix tailTrace_841036
  have hstable : (prefixWord ++ tailWord_841036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841036).length < 2 ^ (prefixWord ++ tailWord_841036).sum := by decide
  have hdescent : baseEnd_841036 < baseStart_841036 := by decide
  rcases family_descends (prefixWord ++ tailWord_841036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841081 : List Nat := [1, 2, 1, 3, 2, 1, 5, 2, 4]
def baseStart_841081 : Nat := 118140960795 + 841081 * 2 ^ 59
def prefixEnd_841081 : Nat := 4983230072969 + 3 ^ 40 * 841081 * 2
def baseEnd_841081 : Nat := 191946143273035111297531

theorem tailTrace_841081 : CollatzResearch.WordTrace tailWord_841081 prefixEnd_841081 191946143273035111297531 := by
  unfold tailWord_841081
  simp only [CollatzResearch.WordTrace]
  refine ⟨30676744265914657043731097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20451162843943104695820731 30676744265914657043731097)
  ·
    refine ⟨23007558199435992782798323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30676744265914657043731097 23007558199435992782798323)
    ·
      refine ⟨34511337299153989174197485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23007558199435992782798323 34511337299153989174197485)
      ·
        refine ⟨12941751487182745940324057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34511337299153989174197485 12941751487182745940324057)
        ·
          refine ⟨9706313615387059455243043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12941751487182745940324057 9706313615387059455243043)
          ·
            refine ⟨14559470423080589182864565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9706313615387059455243043 14559470423080589182864565)
            ·
              refine ⟨1364950352163805235893553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14559470423080589182864565 1364950352163805235893553)
              ·
                refine ⟨1023712764122853926920165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364950352163805235893553 1023712764122853926920165)
                ·
                  refine ⟨191946143273035111297531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1023712764122853926920165 191946143273035111297531)
                  ·
                    rfl

theorem cell21_841081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_841081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841081 prefixEnd_841081 := by exact prefixLift 841081
  have htrace : WordTrace (prefixWord ++ tailWord_841081) baseStart_841081 baseEnd_841081 := by
    simpa [prefixWord, tailWord_841081, baseEnd_841081] using wordTrace_append hprefix tailTrace_841081
  have hstable : (prefixWord ++ tailWord_841081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841081).length < 2 ^ (prefixWord ++ tailWord_841081).sum := by decide
  have hdescent : baseEnd_841081 < baseStart_841081 := by decide
  rcases family_descends (prefixWord ++ tailWord_841081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841112 : List Nat := [2, 1, 2, 5, 2, 1, 1, 7]
def baseStart_841112 : Nat := 118140960795 + 841112 * 2 ^ 59
def prefixEnd_841112 : Nat := 4983230072969 + 3 ^ 40 * 841112 * 2
def baseEnd_841112 : Nat := 63984405965128648760267

theorem tailTrace_841112 : CollatzResearch.WordTrace tailWord_841112 prefixEnd_841112 63984405965128648760267 := by
  unfold tailWord_841112
  simp only [CollatzResearch.WordTrace]
  refine ⟨15338937464401174669054795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20451916619201566225406393 15338937464401174669054795)
  ·
    refine ⟨23008406196601762003582193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15338937464401174669054795 23008406196601762003582193)
    ·
      refine ⟨17256304647451321502686645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23008406196601762003582193 17256304647451321502686645)
      ·
        refine ⟨1617778560698561390876873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17256304647451321502686645 1617778560698561390876873)
        ·
          refine ⟨1213333920523921043157655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1617778560698561390876873 1213333920523921043157655)
          ·
            refine ⟨1820000880785881564736483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213333920523921043157655 1820000880785881564736483)
            ·
              refine ⟨2730001321178822347104725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820000880785881564736483 2730001321178822347104725)
              ·
                refine ⟨63984405965128648760267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2730001321178822347104725 63984405965128648760267)
                ·
                  rfl

theorem cell21_841112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_841112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841112 prefixEnd_841112 := by exact prefixLift 841112
  have htrace : WordTrace (prefixWord ++ tailWord_841112) baseStart_841112 baseEnd_841112 := by
    simpa [prefixWord, tailWord_841112, baseEnd_841112] using wordTrace_append hprefix tailTrace_841112
  have hstable : (prefixWord ++ tailWord_841112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841112).length < 2 ^ (prefixWord ++ tailWord_841112).sum := by decide
  have hdescent : baseEnd_841112 < baseStart_841112 := by decide
  rcases family_descends (prefixWord ++ tailWord_841112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841118 : List Nat := [4, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_841118 : Nat := 118140960795 + 841118 * 2 ^ 59
def prefixEnd_841118 : Nat := 4983230072969 + 3 ^ 40 * 841118 * 2
def baseEnd_841118 : Nat := 191954587177131269180789

theorem tailTrace_841118 : CollatzResearch.WordTrace tailWord_841118 prefixEnd_841118 191954587177131269180789 := by
  unfold tailWord_841118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3834761720847576545353501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20452062511187074908552005 3834761720847576545353501)
  ·
    refine ⟨1438035645317841204507563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3834761720847576545353501 1438035645317841204507563)
    ·
      refine ⟨2157053467976761806761345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1438035645317841204507563 2157053467976761806761345)
      ·
        refine ⟨1617790100982571355071009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2157053467976761806761345 1617790100982571355071009)
        ·
          refine ⟨1213342575736928516303257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1617790100982571355071009 1213342575736928516303257)
          ·
            refine ⟨910006931802696387227443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1213342575736928516303257 910006931802696387227443)
            ·
              refine ⟨1365010397704044580841165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910006931802696387227443 1365010397704044580841165)
              ·
                refine ⟨511878899139016717815437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1365010397704044580841165 511878899139016717815437)
                ·
                  refine ⟨191954587177131269180789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511878899139016717815437 191954587177131269180789)
                  ·
                    rfl

theorem cell21_841118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_841118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841118 prefixEnd_841118 := by exact prefixLift 841118
  have htrace : WordTrace (prefixWord ++ tailWord_841118) baseStart_841118 baseEnd_841118 := by
    simpa [prefixWord, tailWord_841118, baseEnd_841118] using wordTrace_append hprefix tailTrace_841118
  have hstable : (prefixWord ++ tailWord_841118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841118).length < 2 ^ (prefixWord ++ tailWord_841118).sum := by decide
  have hdescent : baseEnd_841118 < baseStart_841118 := by decide
  rcases family_descends (prefixWord ++ tailWord_841118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841194 : List Nat := [3, 1, 3, 1, 5, 1, 2, 2, 3]
def baseStart_841194 : Nat := 118140960795 + 841194 * 2 ^ 59
def prefixEnd_841194 : Nat := 4983230072969 + 3 ^ 40 * 841194 * 2
def baseEnd_841194 : Nat := 191971931412572025913967

theorem tailTrace_841194 : CollatzResearch.WordTrace tailWord_841194 prefixEnd_841194 191971931412572025913967 := by
  unfold tailWord_841194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7670216428626319335648659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20453910476336851561729757 7670216428626319335648659)
  ·
    refine ⟨11505324642939479003472989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7670216428626319335648659 11505324642939479003472989)
    ·
      refine ⟨4314496741102304626302371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11505324642939479003472989 4314496741102304626302371)
      ·
        refine ⟨6471745111653456939453557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4314496741102304626302371 6471745111653456939453557)
        ·
          refine ⟨606726104217511588073771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6471745111653456939453557 606726104217511588073771)
          ·
            refine ⟨910089156326267382110657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606726104217511588073771 910089156326267382110657)
            ·
              refine ⟨682566867244700536582993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910089156326267382110657 682566867244700536582993)
              ·
                refine ⟨511925150433525402437245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682566867244700536582993 511925150433525402437245)
                ·
                  refine ⟨191971931412572025913967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511925150433525402437245 191971931412572025913967)
                  ·
                    rfl

theorem cell21_841194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_841194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841194 prefixEnd_841194 := by exact prefixLift 841194
  have htrace : WordTrace (prefixWord ++ tailWord_841194) baseStart_841194 baseEnd_841194 := by
    simpa [prefixWord, tailWord_841194, baseEnd_841194] using wordTrace_append hprefix tailTrace_841194
  have hstable : (prefixWord ++ tailWord_841194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841194).length < 2 ^ (prefixWord ++ tailWord_841194).sum := by decide
  have hdescent : baseEnd_841194 < baseStart_841194 := by decide
  rcases family_descends (prefixWord ++ tailWord_841194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841205 : List Nat := [1, 3, 5, 1, 1, 3, 1, 6]
def baseStart_841205 : Nat := 118140960795 + 841205 * 2 ^ 59
def prefixEnd_841205 : Nat := 4983230072969 + 3 ^ 40 * 841205 * 2
def baseEnd_841205 : Nat := 63991480587479483743537

theorem tailTrace_841205 : CollatzResearch.WordTrace tailWord_841205 prefixEnd_841205 63991480587479483743537 := by
  unfold tailWord_841205
  simp only [CollatzResearch.WordTrace]
  refine ⟨30681266917465426221245069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20454177944976950814163379 30681266917465426221245069)
  ·
    refine ⟨11505475094049534832966901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30681266917465426221245069 11505475094049534832966901)
    ·
      refine ⟨1078638290067143890590647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11505475094049534832966901 1078638290067143890590647)
      ·
        refine ⟨1617957435100715835885971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078638290067143890590647 1617957435100715835885971)
        ·
          refine ⟨2426936152651073753828957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617957435100715835885971 2426936152651073753828957)
          ·
            refine ⟨910101057244152657685859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2426936152651073753828957 910101057244152657685859)
            ·
              refine ⟨1365151585866228986528789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910101057244152657685859 1365151585866228986528789)
              ·
                refine ⟨63991480587479483743537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1365151585866228986528789 63991480587479483743537)
                ·
                  rfl

theorem cell21_841205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 6].length) (baseStart_841205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841205 prefixEnd_841205 := by exact prefixLift 841205
  have htrace : WordTrace (prefixWord ++ tailWord_841205) baseStart_841205 baseEnd_841205 := by
    simpa [prefixWord, tailWord_841205, baseEnd_841205] using wordTrace_append hprefix tailTrace_841205
  have hstable : (prefixWord ++ tailWord_841205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841205).length < 2 ^ (prefixWord ++ tailWord_841205).sum := by decide
  have hdescent : baseEnd_841205 < baseStart_841205 := by decide
  rcases family_descends (prefixWord ++ tailWord_841205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841292 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 6]
def baseStart_841292 : Nat := 118140960795 + 841292 * 2 ^ 59
def prefixEnd_841292 : Nat := 4983230072969 + 3 ^ 40 * 841292 * 2
def baseEnd_841292 : Nat := 191994296347745633280433

theorem tailTrace_841292 : CollatzResearch.WordTrace tailWord_841292 prefixEnd_841292 191994296347745633280433 := by
  unfold tailWord_841292
  simp only [CollatzResearch.WordTrace]
  refine ⟨15342220034075120039831065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20456293378766826719774753 15342220034075120039831065)
  ·
    refine ⟨11506665025556340029873299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15342220034075120039831065 11506665025556340029873299)
    ·
      refine ⟨17259997538334510044809949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11506665025556340029873299 17259997538334510044809949)
      ·
        refine ⟨6472499076875441266803731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17259997538334510044809949 6472499076875441266803731)
        ·
          refine ⟨9708748615313161900205597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472499076875441266803731 9708748615313161900205597)
          ·
            refine ⟨3640780730742435712577099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9708748615313161900205597 3640780730742435712577099)
            ·
              refine ⟨5461171096113653568865649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3640780730742435712577099 5461171096113653568865649)
              ·
                refine ⟨4095878322085240176649237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5461171096113653568865649 4095878322085240176649237)
                ·
                  refine ⟨191994296347745633280433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4095878322085240176649237 191994296347745633280433)
                  ·
                    rfl

theorem cell21_841292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_841292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841292 prefixEnd_841292 := by exact prefixLift 841292
  have htrace : WordTrace (prefixWord ++ tailWord_841292) baseStart_841292 baseEnd_841292 := by
    simpa [prefixWord, tailWord_841292, baseEnd_841292] using wordTrace_append hprefix tailTrace_841292
  have hstable : (prefixWord ++ tailWord_841292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841292).length < 2 ^ (prefixWord ++ tailWord_841292).sum := by decide
  have hdescent : baseEnd_841292 < baseStart_841292 := by decide
  rcases family_descends (prefixWord ++ tailWord_841292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841326 : List Nat := [4, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_841326 : Nat := 118140960795 + 841326 * 2 ^ 59
def prefixEnd_841326 : Nat := 4983230072969 + 3 ^ 40 * 841326 * 2
def baseEnd_841326 : Nat := 192002055610969129713697

theorem tailTrace_841326 : CollatzResearch.WordTrace tailWord_841326 prefixEnd_841326 192002055610969129713697 := by
  unfold tailWord_841326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3835710018753382985799979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20457120100018042590933221 3835710018753382985799979)
  ·
    refine ⟨5753565028130074478699969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3835710018753382985799979 5753565028130074478699969)
    ·
      refine ⟨4315173771097555859024977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5753565028130074478699969 4315173771097555859024977)
      ·
        refine ⟨3236380328323166894268733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4315173771097555859024977 3236380328323166894268733)
        ·
          refine ⟨1213642623121187585350775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3236380328323166894268733 1213642623121187585350775)
          ·
            refine ⟨1820463934681781378026163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213642623121187585350775 1820463934681781378026163)
            ·
              refine ⟨2730695902022672067039245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820463934681781378026163 2730695902022672067039245)
              ·
                refine ⟨1024010963258502025139717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2730695902022672067039245 1024010963258502025139717)
                ·
                  refine ⟨192002055610969129713697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1024010963258502025139717 192002055610969129713697)
                  ·
                    rfl

theorem cell21_841326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_841326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841326 prefixEnd_841326 := by exact prefixLift 841326
  have htrace : WordTrace (prefixWord ++ tailWord_841326) baseStart_841326 baseEnd_841326 := by
    simpa [prefixWord, tailWord_841326, baseEnd_841326] using wordTrace_append hprefix tailTrace_841326
  have hstable : (prefixWord ++ tailWord_841326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841326).length < 2 ^ (prefixWord ++ tailWord_841326).sum := by decide
  have hdescent : baseEnd_841326 < baseStart_841326 := by decide
  rcases family_descends (prefixWord ++ tailWord_841326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841337 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 7]
def baseStart_841337 : Nat := 118140960795 + 841337 * 2 ^ 59
def prefixEnd_841337 : Nat := 4983230072969 + 3 ^ 40 * 841337 * 2
def baseEnd_841337 : Nat := 192004565960835555030341

theorem tailTrace_841337 : CollatzResearch.WordTrace tailWord_841337 prefixEnd_841337 192004565960835555030341 := by
  unfold tailWord_841337
  simp only [CollatzResearch.WordTrace]
  refine ⟨30686081352987212765050265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20457387568658141843366843 30686081352987212765050265)
  ·
    refine ⟨23014561014740409573787699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30686081352987212765050265 23014561014740409573787699)
    ·
      refine ⟨34521841522110614360681549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23014561014740409573787699 34521841522110614360681549)
      ·
        refine ⟨12945690570791480385255581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34521841522110614360681549 12945690570791480385255581)
        ·
          refine ⟨4854633964046805144470843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12945690570791480385255581 4854633964046805144470843)
          ·
            refine ⟨7281950946070207716706265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4854633964046805144470843 7281950946070207716706265)
            ·
              refine ⟨5461463209552655787529699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7281950946070207716706265 5461463209552655787529699)
              ·
                refine ⟨8192194814328983681294549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5461463209552655787529699 8192194814328983681294549)
                ·
                  refine ⟨192004565960835555030341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8192194814328983681294549 192004565960835555030341)
                  ·
                    rfl

theorem cell21_841337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_841337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841337 prefixEnd_841337 := by exact prefixLift 841337
  have htrace : WordTrace (prefixWord ++ tailWord_841337) baseStart_841337 baseEnd_841337 := by
    simpa [prefixWord, tailWord_841337, baseEnd_841337] using wordTrace_append hprefix tailTrace_841337
  have hstable : (prefixWord ++ tailWord_841337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841337).length < 2 ^ (prefixWord ++ tailWord_841337).sum := by decide
  have hdescent : baseEnd_841337 < baseStart_841337 := by decide
  rcases family_descends (prefixWord ++ tailWord_841337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841579 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 6]
def baseStart_841579 : Nat := 118140960795 + 841579 * 2 ^ 59
def prefixEnd_841579 : Nat := 4983230072969 + 3 ^ 40 * 841579 * 2
def baseEnd_841579 : Nat := 192059793657896911996513

theorem tailTrace_841579 : CollatzResearch.WordTrace tailWord_841579 prefixEnd_841579 192059793657896911996513 := by
  unfold tailWord_841579
  simp only [CollatzResearch.WordTrace]
  refine ⟨30694907818110488095359791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20463271878740325396906527 30694907818110488095359791)
  ·
    refine ⟨46042361727165732143039687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30694907818110488095359791 46042361727165732143039687)
    ·
      refine ⟨69063542590748598214559531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46042361727165732143039687 69063542590748598214559531)
      ·
        refine ⟨103595313886122897321839297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69063542590748598214559531 103595313886122897321839297)
        ·
          refine ⟨77696485414592172991379473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103595313886122897321839297 77696485414592172991379473)
          ·
            refine ⟨58272364060944129743534605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77696485414592172991379473 58272364060944129743534605)
            ·
              refine ⟨21852136522854048653825477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58272364060944129743534605 21852136522854048653825477)
              ·
                refine ⟨4097275598035134122592277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21852136522854048653825477 4097275598035134122592277)
                ·
                  refine ⟨192059793657896911996513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4097275598035134122592277 192059793657896911996513)
                  ·
                    rfl

theorem cell21_841579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_841579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841579 prefixEnd_841579 := by exact prefixLift 841579
  have htrace : WordTrace (prefixWord ++ tailWord_841579) baseStart_841579 baseEnd_841579 := by
    simpa [prefixWord, tailWord_841579, baseEnd_841579] using wordTrace_append hprefix tailTrace_841579
  have hstable : (prefixWord ++ tailWord_841579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841579).length < 2 ^ (prefixWord ++ tailWord_841579).sum := by decide
  have hdescent : baseEnd_841579 < baseStart_841579 := by decide
  rcases family_descends (prefixWord ++ tailWord_841579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841633 : List Nat := [1, 2, 3, 4, 3, 1, 1, 3, 3]
def baseStart_841633 : Nat := 118140960795 + 841633 * 2 ^ 59
def prefixEnd_841633 : Nat := 4983230072969 + 3 ^ 40 * 841633 * 2
def baseEnd_841633 : Nat := 192072117193604818096403

theorem tailTrace_841633 : CollatzResearch.WordTrace tailWord_841633 prefixEnd_841633 192072117193604818096403 := by
  unfold tailWord_841633
  simp only [CollatzResearch.WordTrace]
  refine ⟨30696877359914855317825553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20464584906609903545217035 30696877359914855317825553)
  ·
    refine ⟨23022658019936141488369165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30696877359914855317825553 23022658019936141488369165)
    ·
      refine ⟨8633496757476053058138437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23022658019936141488369165 8633496757476053058138437)
      ·
        refine ⟨1618780642026759948400957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8633496757476053058138437 1618780642026759948400957)
        ·
          refine ⟨607042740760034980650359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1618780642026759948400957 607042740760034980650359)
          ·
            refine ⟨910564111140052470975539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607042740760034980650359 910564111140052470975539)
            ·
              refine ⟨1365846166710078706463309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910564111140052470975539 1365846166710078706463309)
              ·
                refine ⟨512192312516279514923741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1365846166710078706463309 512192312516279514923741)
                ·
                  refine ⟨192072117193604818096403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 512192312516279514923741 192072117193604818096403)
                  ·
                    rfl

theorem cell21_841633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 3].length) (baseStart_841633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841633 prefixEnd_841633 := by exact prefixLift 841633
  have htrace : WordTrace (prefixWord ++ tailWord_841633) baseStart_841633 baseEnd_841633 := by
    simpa [prefixWord, tailWord_841633, baseEnd_841633] using wordTrace_append hprefix tailTrace_841633
  have hstable : (prefixWord ++ tailWord_841633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841633).length < 2 ^ (prefixWord ++ tailWord_841633).sum := by decide
  have hdescent : baseEnd_841633 < baseStart_841633 := by decide
  rcases family_descends (prefixWord ++ tailWord_841633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841703 : List Nat := [1, 1, 5, 2, 4, 8]
def baseStart_841703 : Nat := 118140960795 + 841703 * 2 ^ 59
def prefixEnd_841703 : Nat := 4983230072969 + 3 ^ 40 * 841703 * 2
def baseEnd_841703 : Nat := 7114373783233342664059

theorem tailTrace_841703 : CollatzResearch.WordTrace tailWord_841703 prefixEnd_841703 7114373783233342664059 := by
  unfold tailWord_841703
  simp only [CollatzResearch.WordTrace]
  refine ⟨30699430469661257272873763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20466286979774171515249175 30699430469661257272873763)
  ·
    refine ⟨46049145704491885909310645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30699430469661257272873763 46049145704491885909310645)
    ·
      refine ⟨4317107409796114303997873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46049145704491885909310645 4317107409796114303997873)
      ·
        refine ⟨3237830557347085727998405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4317107409796114303997873 3237830557347085727998405)
        ·
          refine ⟨607093229502578573999701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3237830557347085727998405 607093229502578573999701)
          ·
            refine ⟨7114373783233342664059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 607093229502578573999701 7114373783233342664059)
            ·
              rfl

theorem cell21_841703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 8].length) (baseStart_841703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841703 prefixEnd_841703 := by exact prefixLift 841703
  have htrace : WordTrace (prefixWord ++ tailWord_841703) baseStart_841703 baseEnd_841703 := by
    simpa [prefixWord, tailWord_841703, baseEnd_841703] using wordTrace_append hprefix tailTrace_841703
  have hstable : (prefixWord ++ tailWord_841703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841703).length < 2 ^ (prefixWord ++ tailWord_841703).sum := by decide
  have hdescent : baseEnd_841703 < baseStart_841703 := by decide
  rcases family_descends (prefixWord ++ tailWord_841703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841762 : List Nat := [3, 3, 1, 1, 1, 2, 10]
def baseStart_841762 : Nat := 118140960795 + 841762 * 2 ^ 59
def prefixEnd_841762 : Nat := 4983230072969 + 3 ^ 40 * 841762 * 2
def baseEnd_841762 : Nat := 21344617416792140049571

theorem tailTrace_841762 : CollatzResearch.WordTrace tailWord_841762 prefixEnd_841762 21344617416792140049571 := by
  unfold tailWord_841762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7675395594111877587317885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20467721584298340232847693 7675395594111877587317885)
  ·
    refine ⟨2878273347791954095244207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7675395594111877587317885 2878273347791954095244207)
    ·
      refine ⟨4317410021687931142866311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2878273347791954095244207 4317410021687931142866311)
      ·
        refine ⟨6476115032531896714299467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4317410021687931142866311 6476115032531896714299467)
        ·
          refine ⟨9714172548797845071449201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6476115032531896714299467 9714172548797845071449201)
          ·
            refine ⟨7285629411598383803586901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9714172548797845071449201 7285629411598383803586901)
            ·
              refine ⟨21344617416792140049571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7285629411598383803586901 21344617416792140049571)
              ·
                rfl

theorem cell21_841762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 10].length) (baseStart_841762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841762 prefixEnd_841762 := by exact prefixLift 841762
  have htrace : WordTrace (prefixWord ++ tailWord_841762) baseStart_841762 baseEnd_841762 := by
    simpa [prefixWord, tailWord_841762, baseEnd_841762] using wordTrace_append hprefix tailTrace_841762
  have hstable : (prefixWord ++ tailWord_841762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841762).length < 2 ^ (prefixWord ++ tailWord_841762).sum := by decide
  have hdescent : baseEnd_841762 < baseStart_841762 := by decide
  rcases family_descends (prefixWord ++ tailWord_841762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841765 : List Nat := [1, 3, 1, 2, 2, 5, 1, 2, 4]
def baseStart_841765 : Nat := 118140960795 + 841765 * 2 ^ 59
def prefixEnd_841765 : Nat := 4983230072969 + 3 ^ 40 * 841765 * 2
def baseEnd_841765 : Nat := 192102241392001921896133

theorem tailTrace_841765 : CollatzResearch.WordTrace tailWord_841765 prefixEnd_841765 192102241392001921896133 := by
  unfold tailWord_841765
  simp only [CollatzResearch.WordTrace]
  refine ⟨30701691795436641861630749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20467794530291094574420499 30701691795436641861630749)
  ·
    refine ⟨11513134423288740698111531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30701691795436641861630749 11513134423288740698111531)
    ·
      refine ⟨17269701634933111047167297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11513134423288740698111531 17269701634933111047167297)
      ·
        refine ⟨12952276226199833285375473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17269701634933111047167297 12952276226199833285375473)
        ·
          refine ⟨9714207169649874964031605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12952276226199833285375473 9714207169649874964031605)
          ·
            refine ⟨910706922154675777877963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9714207169649874964031605 910706922154675777877963)
            ·
              refine ⟨1366060383232013666816945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910706922154675777877963 1366060383232013666816945)
              ·
                refine ⟨1024545287424010250112709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366060383232013666816945 1024545287424010250112709)
                ·
                  refine ⟨192102241392001921896133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1024545287424010250112709 192102241392001921896133)
                  ·
                    rfl

theorem cell21_841765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_841765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841765 prefixEnd_841765 := by exact prefixLift 841765
  have htrace : WordTrace (prefixWord ++ tailWord_841765) baseStart_841765 baseEnd_841765 := by
    simpa [prefixWord, tailWord_841765, baseEnd_841765] using wordTrace_append hprefix tailTrace_841765
  have hstable : (prefixWord ++ tailWord_841765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841765).length < 2 ^ (prefixWord ++ tailWord_841765).sum := by decide
  have hdescent : baseEnd_841765 < baseStart_841765 := by decide
  rcases family_descends (prefixWord ++ tailWord_841765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841782 : List Nat := [5, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_841782 : Nat := 118140960795 + 841782 * 2 ^ 59
def prefixEnd_841782 : Nat := 4983230072969 + 3 ^ 40 * 841782 * 2
def baseEnd_841782 : Nat := 192106121023613670112765

theorem tailTrace_841782 : CollatzResearch.WordTrace tailWord_841782 prefixEnd_841782 192106121023613670112765 := by
  unfold tailWord_841782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1918894489773440860312475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20468207890916702509999733 1918894489773440860312475)
  ·
    refine ⟨2878341734660161290468713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1918894489773440860312475 2878341734660161290468713)
    ·
      refine ⟨2158756300995120967851535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2878341734660161290468713 2158756300995120967851535)
      ·
        refine ⟨3238134451492681451777303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2158756300995120967851535 3238134451492681451777303)
        ·
          refine ⟨4857201677239022177665955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3238134451492681451777303 4857201677239022177665955)
          ·
            refine ⟨7285802515858533266498933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4857201677239022177665955 7285802515858533266498933)
            ·
              refine ⟨683043985861737493734275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7285802515858533266498933 683043985861737493734275)
              ·
                refine ⟨1024565978792606240601413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683043985861737493734275 1024565978792606240601413)
                ·
                  refine ⟨192106121023613670112765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1024565978792606240601413 192106121023613670112765)
                  ·
                    rfl

theorem cell21_841782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_841782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841782 prefixEnd_841782 := by exact prefixLift 841782
  have htrace : WordTrace (prefixWord ++ tailWord_841782) baseStart_841782 baseEnd_841782 := by
    simpa [prefixWord, tailWord_841782, baseEnd_841782] using wordTrace_append hprefix tailTrace_841782
  have hstable : (prefixWord ++ tailWord_841782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841782).length < 2 ^ (prefixWord ++ tailWord_841782).sum := by decide
  have hdescent : baseEnd_841782 < baseStart_841782 := by decide
  rcases family_descends (prefixWord ++ tailWord_841782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841928 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 9]
def baseStart_841928 : Nat := 118140960795 + 841928 * 2 ^ 59
def prefixEnd_841928 : Nat := 4983230072969 + 3 ^ 40 * 841928 * 2
def baseEnd_841928 : Nat := 192139440212749860679133

theorem tailTrace_841928 : CollatzResearch.WordTrace tailWord_841928 prefixEnd_841928 192139440212749860679133 := by
  unfold tailWord_841928
  simp only [CollatzResearch.WordTrace]
  refine ⟨15353818446923060349907219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20471757929230747133209625 15353818446923060349907219)
  ·
    refine ⟨23030727670384590524860829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15353818446923060349907219 23030727670384590524860829)
    ·
      refine ⟨8636522876394221446822811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23030727670384590524860829 8636522876394221446822811)
      ·
        refine ⟨12954784314591332170234217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8636522876394221446822811 12954784314591332170234217)
        ·
          refine ⟨9716088235943499127675663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12954784314591332170234217 9716088235943499127675663)
          ·
            refine ⟨14574132353915248691513495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9716088235943499127675663 14574132353915248691513495)
            ·
              refine ⟨21861198530872873037270243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14574132353915248691513495 21861198530872873037270243)
              ·
                refine ⟨32791797796309309555905365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21861198530872873037270243 32791797796309309555905365)
                ·
                  refine ⟨192139440212749860679133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32791797796309309555905365 192139440212749860679133)
                  ·
                    rfl

theorem cell21_841928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_841928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841928 prefixEnd_841928 := by exact prefixLift 841928
  have htrace : WordTrace (prefixWord ++ tailWord_841928) baseStart_841928 baseEnd_841928 := by
    simpa [prefixWord, tailWord_841928, baseEnd_841928] using wordTrace_append hprefix tailTrace_841928
  have hstable : (prefixWord ++ tailWord_841928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841928).length < 2 ^ (prefixWord ++ tailWord_841928).sum := by decide
  have hdescent : baseEnd_841928 < baseStart_841928 := by decide
  rcases family_descends (prefixWord ++ tailWord_841928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841965 : List Nat := [1, 5, 1, 2, 4, 1, 2, 5]
def baseStart_841965 : Nat := 118140960795 + 841965 * 2 ^ 59
def prefixEnd_841965 : Nat := 4983230072969 + 3 ^ 40 * 841965 * 2
def baseEnd_841965 : Nat := 64049294705615339520797

theorem tailTrace_841965 : CollatzResearch.WordTrace tailWord_841965 prefixEnd_841965 64049294705615339520797 := by
  unfold tailWord_841965
  simp only [CollatzResearch.WordTrace]
  refine ⟨30708986394712076018911349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20472657596474717345940899 30708986394712076018911349)
  ·
    refine ⟨2878967474504257126772939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30708986394712076018911349 2878967474504257126772939)
    ·
      refine ⟨4318451211756385690159409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2878967474504257126772939 4318451211756385690159409)
      ·
        refine ⟨3238838408817289267619557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4318451211756385690159409 3238838408817289267619557)
        ·
          refine ⟨607282201653241737678667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3238838408817289267619557 607282201653241737678667)
          ·
            refine ⟨910923302479862606518001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607282201653241737678667 910923302479862606518001)
            ·
              refine ⟨683192476859896954888501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910923302479862606518001 683192476859896954888501)
              ·
                refine ⟨64049294705615339520797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 683192476859896954888501 64049294705615339520797)
                ·
                  rfl

theorem cell21_841965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 5].length) (baseStart_841965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_841965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_841965 prefixEnd_841965 := by exact prefixLift 841965
  have htrace : WordTrace (prefixWord ++ tailWord_841965) baseStart_841965 baseEnd_841965 := by
    simpa [prefixWord, tailWord_841965, baseEnd_841965] using wordTrace_append hprefix tailTrace_841965
  have hstable : (prefixWord ++ tailWord_841965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841965).length < 2 ^ (prefixWord ++ tailWord_841965).sum := by decide
  have hdescent : baseEnd_841965 < baseStart_841965 := by decide
  rcases family_descends (prefixWord ++ tailWord_841965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842010 : List Nat := [3, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_842010 : Nat := 118140960795 + 842010 * 2 ^ 59
def prefixEnd_842010 : Nat := 4983230072969 + 3 ^ 40 * 842010 * 2
def baseEnd_842010 : Nat := 192158153729935940312299

theorem tailTrace_842010 : CollatzResearch.WordTrace tailWord_842010 prefixEnd_842010 192158153729935940312299 := by
  unfold tailWord_842010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7677656919887262176074871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20473751786366032469532989 7677656919887262176074871)
  ·
    refine ⟨11516485379830893264112307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7677656919887262176074871 11516485379830893264112307)
    ·
      refine ⟨17274728069746339896168461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11516485379830893264112307 17274728069746339896168461)
      ·
        refine ⟨6478023026154877461063173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17274728069746339896168461 6478023026154877461063173)
        ·
          refine ⟨1214629317404039523949345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6478023026154877461063173 1214629317404039523949345)
          ·
            refine ⟨910971988053029642962009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1214629317404039523949345 910971988053029642962009)
            ·
              refine ⟨683228991039772232221507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910971988053029642962009 683228991039772232221507)
              ·
                refine ⟨1024843486559658348332261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683228991039772232221507 1024843486559658348332261)
                ·
                  refine ⟨192158153729935940312299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1024843486559658348332261 192158153729935940312299)
                  ·
                    rfl

theorem cell21_842010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_842010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842010 prefixEnd_842010 := by exact prefixLift 842010
  have htrace : WordTrace (prefixWord ++ tailWord_842010) baseStart_842010 baseEnd_842010 := by
    simpa [prefixWord, tailWord_842010, baseEnd_842010] using wordTrace_append hprefix tailTrace_842010
  have hstable : (prefixWord ++ tailWord_842010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842010).length < 2 ^ (prefixWord ++ tailWord_842010).sum := by decide
  have hdescent : baseEnd_842010 < baseStart_842010 := by decide
  rcases family_descends (prefixWord ++ tailWord_842010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842066 : List Nat := [3, 2, 2, 1, 1, 1, 5, 6]
def baseStart_842066 : Nat := 118140960795 + 842066 * 2 ^ 59
def prefixEnd_842066 : Nat := 4983230072969 + 3 ^ 40 * 842066 * 2
def baseEnd_842066 : Nat := 64056977897630762459617

theorem tailTrace_842066 : CollatzResearch.WordTrace tailWord_842066 prefixEnd_842066 64056977897630762459617 := by
  unfold tailWord_842066
  simp only [CollatzResearch.WordTrace]
  refine ⟨7678167541836542567084513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20475113444897446845558701 7678167541836542567084513)
  ·
    refine ⟨5758625656377406925313385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7678167541836542567084513 5758625656377406925313385)
    ·
      refine ⟨4318969242283055193985039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5758625656377406925313385 4318969242283055193985039)
      ·
        refine ⟨6478453863424582790977559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4318969242283055193985039 6478453863424582790977559)
        ·
          refine ⟨9717680795136874186466339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6478453863424582790977559 9717680795136874186466339)
          ·
            refine ⟨14576521192705311279699509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9717680795136874186466339 14576521192705311279699509)
            ·
              refine ⟨1366548861816122932471829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14576521192705311279699509 1366548861816122932471829)
              ·
                refine ⟨64056977897630762459617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1366548861816122932471829 64056977897630762459617)
                ·
                  rfl

theorem cell21_842066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_842066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842066 prefixEnd_842066 := by exact prefixLift 842066
  have htrace : WordTrace (prefixWord ++ tailWord_842066) baseStart_842066 baseEnd_842066 := by
    simpa [prefixWord, tailWord_842066, baseEnd_842066] using wordTrace_append hprefix tailTrace_842066
  have hstable : (prefixWord ++ tailWord_842066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842066).length < 2 ^ (prefixWord ++ tailWord_842066).sum := by decide
  have hdescent : baseEnd_842066 < baseStart_842066 := by decide
  rcases family_descends (prefixWord ++ tailWord_842066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842173 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 5]
def baseStart_842173 : Nat := 118140960795 + 842173 * 2 ^ 59
def prefixEnd_842173 : Nat := 4983230072969 + 3 ^ 40 * 842173 * 2
def baseEnd_842173 : Nat := 192195352550683879095299

theorem tailTrace_842173 : CollatzResearch.WordTrace tailWord_842173 prefixEnd_842173 192195352550683879095299 := by
  unfold tailWord_842173
  simp only [CollatzResearch.WordTrace]
  refine ⟨30716572777958527542483173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20477715185305685028322115 30716572777958527542483173)
  ·
    refine ⟨5759357395867223914215595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30716572777958527542483173 5759357395867223914215595)
    ·
      refine ⟨8639036093800835871323393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5759357395867223914215595 8639036093800835871323393)
      ·
        refine ⟨6479277070350626903492545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8639036093800835871323393 6479277070350626903492545)
        ·
          refine ⟨4859457802762970177619409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6479277070350626903492545 4859457802762970177619409)
          ·
            refine ⟨3644593352072227633214557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4859457802762970177619409 3644593352072227633214557)
            ·
              refine ⟨1366722507027085362455459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3644593352072227633214557 1366722507027085362455459)
              ·
                refine ⟨2050083760540628043683189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366722507027085362455459 2050083760540628043683189)
                ·
                  refine ⟨192195352550683879095299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2050083760540628043683189 192195352550683879095299)
                  ·
                    rfl

theorem cell21_842173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_842173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842173 prefixEnd_842173 := by exact prefixLift 842173
  have htrace : WordTrace (prefixWord ++ tailWord_842173) baseStart_842173 baseEnd_842173 := by
    simpa [prefixWord, tailWord_842173, baseEnd_842173] using wordTrace_append hprefix tailTrace_842173
  have hstable : (prefixWord ++ tailWord_842173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842173).length < 2 ^ (prefixWord ++ tailWord_842173).sum := by decide
  have hdescent : baseEnd_842173 < baseStart_842173 := by decide
  rcases family_descends (prefixWord ++ tailWord_842173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842201 : List Nat := [1, 2, 1, 2, 4, 1, 1, 9]
def baseStart_842201 : Nat := 118140960795 + 842201 * 2 ^ 59
def prefixEnd_842201 : Nat := 4983230072969 + 3 ^ 40 * 842201 * 2
def baseEnd_842201 : Nat := 64067247510720684209525

theorem tailTrace_842201 : CollatzResearch.WordTrace tailWord_842201 prefixEnd_842201 64067247510720684209525 := by
  unfold tailWord_842201
  simp only [CollatzResearch.WordTrace]
  refine ⟨30717594021857088324502457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20478396014571392216334971 30717594021857088324502457)
  ·
    refine ⟨23038195516392816243376843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30717594021857088324502457 23038195516392816243376843)
    ·
      refine ⟨34557293274589224365065265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23038195516392816243376843 34557293274589224365065265)
      ·
        refine ⟨25917969955941918273798949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34557293274589224365065265 25917969955941918273798949)
        ·
          refine ⟨4859619366739109676337303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25917969955941918273798949 4859619366739109676337303)
          ·
            refine ⟨7289429050108664514505955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4859619366739109676337303 7289429050108664514505955)
            ·
              refine ⟨10934143575162996771758933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7289429050108664514505955 10934143575162996771758933)
              ·
                refine ⟨64067247510720684209525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10934143575162996771758933 64067247510720684209525)
                ·
                  rfl

theorem cell21_842201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 9].length) (baseStart_842201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842201 prefixEnd_842201 := by exact prefixLift 842201
  have htrace : WordTrace (prefixWord ++ tailWord_842201) baseStart_842201 baseEnd_842201 := by
    simpa [prefixWord, tailWord_842201, baseEnd_842201] using wordTrace_append hprefix tailTrace_842201
  have hstable : (prefixWord ++ tailWord_842201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842201).length < 2 ^ (prefixWord ++ tailWord_842201).sum := by decide
  have hdescent : baseEnd_842201 < baseStart_842201 := by decide
  rcases family_descends (prefixWord ++ tailWord_842201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842221 : List Nat := [1, 5, 1, 3, 1, 2, 2, 2, 4]
def baseStart_842221 : Nat := 118140960795 + 842221 * 2 ^ 59
def prefixEnd_842221 : Nat := 4983230072969 + 3 ^ 40 * 842221 * 2
def baseEnd_842221 : Nat := 192206306804646462295201

theorem tailTrace_842221 : CollatzResearch.WordTrace tailWord_842221 prefixEnd_842221 192206306804646462295201 := by
  unfold tailWord_842221
  simp only [CollatzResearch.WordTrace]
  refine ⟨30718323481784631740230517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20478882321189754493487011 30718323481784631740230517)
  ·
    refine ⟨2879842826417309225646611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30718323481784631740230517 2879842826417309225646611)
    ·
      refine ⟨4319764239625963838469917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2879842826417309225646611 4319764239625963838469917)
      ·
        refine ⟨1619911589859736439426219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4319764239625963838469917 1619911589859736439426219)
        ·
          refine ⟨2429867384789604659139329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1619911589859736439426219 2429867384789604659139329)
          ·
            refine ⟨1822400538592203494354497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2429867384789604659139329 1822400538592203494354497)
            ·
              refine ⟨1366800403944152620765873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1822400538592203494354497 1366800403944152620765873)
              ·
                refine ⟨1025100302958114465574405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366800403944152620765873 1025100302958114465574405)
                ·
                  refine ⟨192206306804646462295201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1025100302958114465574405 192206306804646462295201)
                  ·
                    rfl

theorem cell21_842221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_842221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842221 prefixEnd_842221 := by exact prefixLift 842221
  have htrace : WordTrace (prefixWord ++ tailWord_842221) baseStart_842221 baseEnd_842221 := by
    simpa [prefixWord, tailWord_842221, baseEnd_842221] using wordTrace_append hprefix tailTrace_842221
  have hstable : (prefixWord ++ tailWord_842221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842221).length < 2 ^ (prefixWord ++ tailWord_842221).sum := by decide
  have hdescent : baseEnd_842221 < baseStart_842221 := by decide
  rcases family_descends (prefixWord ++ tailWord_842221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842232 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 5]
def baseStart_842232 : Nat := 118140960795 + 842232 * 2 ^ 59
def prefixEnd_842232 : Nat := 4983230072969 + 3 ^ 40 * 842232 * 2
def baseEnd_842232 : Nat := 192208817154512887611845

theorem tailTrace_842232 : CollatzResearch.WordTrace tailWord_842232 prefixEnd_842232 192208817154512887611845 := by
  unfold tailWord_842232
  simp only [CollatzResearch.WordTrace]
  refine ⟨15359362342372390309440475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20479149789829853745920633 15359362342372390309440475)
  ·
    refine ⟨23039043513558585464160713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15359362342372390309440475 23039043513558585464160713)
    ·
      refine ⟨17279282635168939098120535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23039043513558585464160713 17279282635168939098120535)
      ·
        refine ⟨25918923952753408647180803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17279282635168939098120535 25918923952753408647180803)
        ·
          refine ⟨38878385929130112970771205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25918923952753408647180803 38878385929130112970771205)
          ·
            refine ⟨7289697361711896182019601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38878385929130112970771205 7289697361711896182019601)
            ·
              refine ⟨5467273021283922136514701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7289697361711896182019601 5467273021283922136514701)
              ·
                refine ⟨2050227382981470801193013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5467273021283922136514701 2050227382981470801193013)
                ·
                  refine ⟨192208817154512887611845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2050227382981470801193013 192208817154512887611845)
                  ·
                    rfl

theorem cell21_842232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_842232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842232 prefixEnd_842232 := by exact prefixLift 842232
  have htrace : WordTrace (prefixWord ++ tailWord_842232) baseStart_842232 baseEnd_842232 := by
    simpa [prefixWord, tailWord_842232, baseEnd_842232] using wordTrace_append hprefix tailTrace_842232
  have hstable : (prefixWord ++ tailWord_842232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842232).length < 2 ^ (prefixWord ++ tailWord_842232).sum := by decide
  have hdescent : baseEnd_842232 < baseStart_842232 := by decide
  rcases family_descends (prefixWord ++ tailWord_842232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842280 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 6]
def baseStart_842280 : Nat := 118140960795 + 842280 * 2 ^ 59
def prefixEnd_842280 : Nat := 4983230072969 + 3 ^ 40 * 842280 * 2
def baseEnd_842280 : Nat := 192219771408475470811747

theorem tailTrace_842280 : CollatzResearch.WordTrace tailWord_842280 prefixEnd_842280 192219771408475470811747 := by
  unfold tailWord_842280
  simp only [CollatzResearch.WordTrace]
  refine ⟨15360237694285442408314147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20480316925713923211085529 15360237694285442408314147)
  ·
    refine ⟨23040356541428163612471221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15360237694285442408314147 23040356541428163612471221)
    ·
      refine ⟨2160033425758890338669177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23040356541428163612471221 2160033425758890338669177)
      ·
        refine ⟨1620025069319167754001883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2160033425758890338669177 1620025069319167754001883)
        ·
          refine ⟨2430037603978751631002825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1620025069319167754001883 2430037603978751631002825)
          ·
            refine ⟨1822528202984063723252119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2430037603978751631002825 1822528202984063723252119)
            ·
              refine ⟨2733792304476095584878179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822528202984063723252119 2733792304476095584878179)
              ·
                refine ⟨4100688456714143377317269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733792304476095584878179 4100688456714143377317269)
                ·
                  refine ⟨192219771408475470811747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4100688456714143377317269 192219771408475470811747)
                  ·
                    rfl

theorem cell21_842280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_842280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842280 prefixEnd_842280 := by exact prefixLift 842280
  have htrace : WordTrace (prefixWord ++ tailWord_842280) baseStart_842280 baseEnd_842280 := by
    simpa [prefixWord, tailWord_842280, baseEnd_842280] using wordTrace_append hprefix tailTrace_842280
  have hstable : (prefixWord ++ tailWord_842280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842280).length < 2 ^ (prefixWord ++ tailWord_842280).sum := by decide
  have hdescent : baseEnd_842280 < baseStart_842280 := by decide
  rcases family_descends (prefixWord ++ tailWord_842280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842311 : List Nat := [1, 1, 4, 1, 4, 3, 2, 5]
def baseStart_842311 : Nat := 118140960795 + 842311 * 2 ^ 59
def prefixEnd_842311 : Nat := 4983230072969 + 3 ^ 40 * 842311 * 2
def baseEnd_842311 : Nat := 64075615343608768598339

theorem tailTrace_842311 : CollatzResearch.WordTrace tailWord_842311 prefixEnd_842311 64075615343608768598339 := by
  unfold tailWord_842311
  simp only [CollatzResearch.WordTrace]
  refine ⟨30721606051458577111006787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20481070700972384740671191 30721606051458577111006787)
  ·
    refine ⟨46082409077187865666510181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30721606051458577111006787 46082409077187865666510181)
    ·
      refine ⟨8640451701972724812470659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46082409077187865666510181 8640451701972724812470659)
      ·
        refine ⟨12960677552959087218705989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8640451701972724812470659 12960677552959087218705989)
        ·
          refine ⟨2430127041179828853507373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12960677552959087218705989 2430127041179828853507373)
          ·
            refine ⟨911297640442435820065265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2430127041179828853507373 911297640442435820065265)
            ·
              refine ⟨683473230331826865048949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911297640442435820065265 683473230331826865048949)
              ·
                refine ⟨64075615343608768598339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 683473230331826865048949 64075615343608768598339)
                ·
                  rfl

theorem cell21_842311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 5].length) (baseStart_842311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842311 prefixEnd_842311 := by exact prefixLift 842311
  have htrace : WordTrace (prefixWord ++ tailWord_842311) baseStart_842311 baseEnd_842311 := by
    simpa [prefixWord, tailWord_842311, baseEnd_842311] using wordTrace_append hprefix tailTrace_842311
  have hstable : (prefixWord ++ tailWord_842311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842311).length < 2 ^ (prefixWord ++ tailWord_842311).sum := by decide
  have hdescent : baseEnd_842311 < baseStart_842311 := by decide
  rcases family_descends (prefixWord ++ tailWord_842311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842334 : List Nat := [4, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_842334 : Nat := 118140960795 + 842334 * 2 ^ 59
def prefixEnd_842334 : Nat := 4983230072969 + 3 ^ 40 * 842334 * 2
def baseEnd_842334 : Nat := 192232094944183376911637

theorem tailTrace_842334 : CollatzResearch.WordTrace tailWord_842334 prefixEnd_842334 192232094944183376911637 := by
  unfold tailWord_842334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840305616296906504886757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20481629953583501359396037 3840305616296906504886757)
  ·
    refine ⟨720057303055669969666267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3840305616296906504886757 720057303055669969666267)
    ·
      refine ⟨1080085954583504954499401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 720057303055669969666267 1080085954583504954499401)
      ·
        refine ⟨810064465937628715874551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1080085954583504954499401 810064465937628715874551)
        ·
          refine ⟨1215096698906443073811827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810064465937628715874551 1215096698906443073811827)
          ·
            refine ⟨1822645048359664610717741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215096698906443073811827 1822645048359664610717741)
            ·
              refine ⟨683491893134874229019153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1822645048359664610717741 683491893134874229019153)
              ·
                refine ⟨512618919851155671764365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683491893134874229019153 512618919851155671764365)
                ·
                  refine ⟨192232094944183376911637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 512618919851155671764365 192232094944183376911637)
                  ·
                    rfl

theorem cell21_842334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_842334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842334 prefixEnd_842334 := by exact prefixLift 842334
  have htrace : WordTrace (prefixWord ++ tailWord_842334) baseStart_842334 baseEnd_842334 := by
    simpa [prefixWord, tailWord_842334, baseEnd_842334] using wordTrace_append hprefix tailTrace_842334
  have hstable : (prefixWord ++ tailWord_842334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842334).length < 2 ^ (prefixWord ++ tailWord_842334).sum := by decide
  have hdescent : baseEnd_842334 < baseStart_842334 := by decide
  rcases family_descends (prefixWord ++ tailWord_842334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842339 : List Nat := [1, 1, 1, 5, 1, 2, 2, 4, 4]
def baseStart_842339 : Nat := 118140960795 + 842339 * 2 ^ 59
def prefixEnd_842339 : Nat := 4983230072969 + 3 ^ 40 * 842339 * 2
def baseEnd_842339 : Nat := 192233236012304479328293

theorem tailTrace_842339 : CollatzResearch.WordTrace tailWord_842339 prefixEnd_842339 192233236012304479328293 := by
  unfold tailWord_842339
  simp only [CollatzResearch.WordTrace]
  refine ⟨30722627295357137893026071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20481751530238091928684047 30722627295357137893026071)
  ·
    refine ⟨46083940943035706839539107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30722627295357137893026071 46083940943035706839539107)
    ·
      refine ⟨69125911414553560259308661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46083940943035706839539107 69125911414553560259308661)
      ·
        refine ⟨6480554195114396274310187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69125911414553560259308661 6480554195114396274310187)
        ·
          refine ⟨9720831292671594411465281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6480554195114396274310187 9720831292671594411465281)
          ·
            refine ⟨7290623469503695808598961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9720831292671594411465281 7290623469503695808598961)
            ·
              refine ⟨5467967602127771856449221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7290623469503695808598961 5467967602127771856449221)
              ·
                refine ⟨1025243925398957223084229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5467967602127771856449221 1025243925398957223084229)
                ·
                  refine ⟨192233236012304479328293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1025243925398957223084229 192233236012304479328293)
                  ·
                    rfl

theorem cell21_842339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 4].length) (baseStart_842339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842339 prefixEnd_842339 := by exact prefixLift 842339
  have htrace : WordTrace (prefixWord ++ tailWord_842339) baseStart_842339 baseEnd_842339 := by
    simpa [prefixWord, tailWord_842339, baseEnd_842339] using wordTrace_append hprefix tailTrace_842339
  have hstable : (prefixWord ++ tailWord_842339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842339).length < 2 ^ (prefixWord ++ tailWord_842339).sum := by decide
  have hdescent : baseEnd_842339 < baseStart_842339 := by decide
  rcases family_descends (prefixWord ++ tailWord_842339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842415 : List Nat := [1, 1, 2, 1, 2, 5, 2, 3, 4]
def baseStart_842415 : Nat := 118140960795 + 842415 * 2 ^ 59
def prefixEnd_842415 : Nat := 4983230072969 + 3 ^ 40 * 842415 * 2
def baseEnd_842415 : Nat := 192250580247745236061471

theorem tailTrace_842415 : CollatzResearch.WordTrace tailWord_842415 prefixEnd_842415 192250580247745236061471 := by
  unfold tailWord_842415
  simp only [CollatzResearch.WordTrace]
  refine ⟨30725399243081802872792699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20483599495387868581861799 30725399243081802872792699)
  ·
    refine ⟨46088098864622704309189049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30725399243081802872792699 46088098864622704309189049)
    ·
      refine ⟨34566074148467028231891787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46088098864622704309189049 34566074148467028231891787)
      ·
        refine ⟨51849111222700542347837681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34566074148467028231891787 51849111222700542347837681)
        ·
          refine ⟨38886833417025406760878261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51849111222700542347837681 38886833417025406760878261)
          ·
            refine ⟨3645640632846131883832337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38886833417025406760878261 3645640632846131883832337)
            ·
              refine ⟨2734230474634598912874253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3645640632846131883832337 2734230474634598912874253)
              ·
                refine ⟨1025336427987974592327845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2734230474634598912874253 1025336427987974592327845)
                ·
                  refine ⟨192250580247745236061471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1025336427987974592327845 192250580247745236061471)
                  ·
                    rfl

theorem cell21_842415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 4].length) (baseStart_842415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842415 prefixEnd_842415 := by exact prefixLift 842415
  have htrace : WordTrace (prefixWord ++ tailWord_842415) baseStart_842415 baseEnd_842415 := by
    simpa [prefixWord, tailWord_842415, baseEnd_842415] using wordTrace_append hprefix tailTrace_842415
  have hstable : (prefixWord ++ tailWord_842415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842415).length < 2 ^ (prefixWord ++ tailWord_842415).sum := by decide
  have hdescent : baseEnd_842415 < baseStart_842415 := by decide
  rcases family_descends (prefixWord ++ tailWord_842415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842525 : List Nat := [1, 4, 2, 4, 1, 1, 1, 3, 4]
def baseStart_842525 : Nat := 118140960795 + 842525 * 2 ^ 59
def prefixEnd_842525 : Nat := 4983230072969 + 3 ^ 40 * 842525 * 2
def baseEnd_842525 : Nat := 192275683746409489227913

theorem tailTrace_842525 : CollatzResearch.WordTrace tailWord_842525 prefixEnd_842525 192275683746409489227913 := by
  unfold tailWord_842525
  simp only [CollatzResearch.WordTrace]
  refine ⟨30729411272683291659297029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20486274181788861106198019 30729411272683291659297029)
  ·
    refine ⟨5761764613628117186118193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30729411272683291659297029 5761764613628117186118193)
    ·
      refine ⟨4321323460221087889588645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5761764613628117186118193 4321323460221087889588645)
      ·
        refine ⟨810248148791453979297871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4321323460221087889588645 810248148791453979297871)
        ·
          refine ⟨1215372223187180968946807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810248148791453979297871 1215372223187180968946807)
          ·
            refine ⟨1823058334780771453420211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215372223187180968946807 1823058334780771453420211)
            ·
              refine ⟨2734587502171157180130317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1823058334780771453420211 2734587502171157180130317)
              ·
                refine ⟨1025470313314183942548869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2734587502171157180130317 1025470313314183942548869)
                ·
                  refine ⟨192275683746409489227913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1025470313314183942548869 192275683746409489227913)
                  ·
                    rfl

theorem cell21_842525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_842525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842525 prefixEnd_842525 := by exact prefixLift 842525
  have htrace : WordTrace (prefixWord ++ tailWord_842525) baseStart_842525 baseEnd_842525 := by
    simpa [prefixWord, tailWord_842525, baseEnd_842525] using wordTrace_append hprefix tailTrace_842525
  have hstable : (prefixWord ++ tailWord_842525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842525).length < 2 ^ (prefixWord ++ tailWord_842525).sum := by decide
  have hdescent : baseEnd_842525 < baseStart_842525 := by decide
  rcases family_descends (prefixWord ++ tailWord_842525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842536 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 7]
def baseStart_842536 : Nat := 118140960795 + 842536 * 2 ^ 59
def prefixEnd_842536 : Nat := 4983230072969 + 3 ^ 40 * 842536 * 2
def baseEnd_842536 : Nat := 192278194096275914544557

theorem tailTrace_842536 : CollatzResearch.WordTrace tailWord_842536 prefixEnd_842536 192278194096275914544557 := by
  unfold tailWord_842536
  simp only [CollatzResearch.WordTrace]
  refine ⟨15364906237821720268973731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20486541650428960358631641 15364906237821720268973731)
  ·
    refine ⟨23047359356732580403460597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15364906237821720268973731 23047359356732580403460597)
    ·
      refine ⟨2160689939693679412824431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23047359356732580403460597 2160689939693679412824431)
      ·
        refine ⟨3241034909540519119236647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2160689939693679412824431 3241034909540519119236647)
        ·
          refine ⟨4861552364310778678854971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3241034909540519119236647 4861552364310778678854971)
          ·
            refine ⟨7292328546466168018282457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4861552364310778678854971 7292328546466168018282457)
            ·
              refine ⟨5469246409849626013711843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7292328546466168018282457 5469246409849626013711843)
              ·
                refine ⟨8203869614774439020567765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5469246409849626013711843 8203869614774439020567765)
                ·
                  refine ⟨192278194096275914544557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8203869614774439020567765 192278194096275914544557)
                  ·
                    rfl

theorem cell21_842536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_842536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842536 prefixEnd_842536 := by exact prefixLift 842536
  have htrace : WordTrace (prefixWord ++ tailWord_842536) baseStart_842536 baseEnd_842536 := by
    simpa [prefixWord, tailWord_842536, baseEnd_842536] using wordTrace_append hprefix tailTrace_842536
  have hstable : (prefixWord ++ tailWord_842536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842536).length < 2 ^ (prefixWord ++ tailWord_842536).sum := by decide
  have hdescent : baseEnd_842536 < baseStart_842536 := by decide
  rcases family_descends (prefixWord ++ tailWord_842536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842629 : List Nat := [1, 3, 1, 1, 3, 3, 2, 4, 3]
def baseStart_842629 : Nat := 118140960795 + 842629 * 2 ^ 59
def prefixEnd_842629 : Nat := 4983230072969 + 3 ^ 40 * 842629 * 2
def baseEnd_842629 : Nat := 192299417963328419494367

theorem tailTrace_842629 : CollatzResearch.WordTrace tailWord_842629 prefixEnd_842629 192299417963328419494367 := by
  unfold tailWord_842629
  simp only [CollatzResearch.WordTrace]
  refine ⟨30733204464306517421082941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20488802976204344947388627 30733204464306517421082941)
  ·
    refine ⟨11524951674114944032906103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30733204464306517421082941 11524951674114944032906103)
    ·
      refine ⟨17287427511172416049359155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11524951674114944032906103 17287427511172416049359155)
      ·
        refine ⟨25931141266758624074038733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17287427511172416049359155 25931141266758624074038733)
        ·
          refine ⟨9724177975034484027764525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25931141266758624074038733 9724177975034484027764525)
          ·
            refine ⟨3646566740637931510411697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9724177975034484027764525 3646566740637931510411697)
            ·
              refine ⟨2734925055478448632808773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3646566740637931510411697 2734925055478448632808773)
              ·
                refine ⟨512798447902209118651645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2734925055478448632808773 512798447902209118651645)
                ·
                  refine ⟨192299417963328419494367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 512798447902209118651645 192299417963328419494367)
                  ·
                    rfl

theorem cell21_842629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_842629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842629 prefixEnd_842629 := by exact prefixLift 842629
  have htrace : WordTrace (prefixWord ++ tailWord_842629) baseStart_842629 baseEnd_842629 := by
    simpa [prefixWord, tailWord_842629, baseEnd_842629] using wordTrace_append hprefix tailTrace_842629
  have hstable : (prefixWord ++ tailWord_842629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842629).length < 2 ^ (prefixWord ++ tailWord_842629).sum := by decide
  have hdescent : baseEnd_842629 < baseStart_842629 := by decide
  rcases family_descends (prefixWord ++ tailWord_842629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842663 : List Nat := [1, 1, 6, 1, 3, 2, 1, 3, 3]
def baseStart_842663 : Nat := 118140960795 + 842663 * 2 ^ 59
def prefixEnd_842663 : Nat := 4983230072969 + 3 ^ 40 * 842663 * 2
def baseEnd_842663 : Nat := 192307177226551915927631

theorem tailTrace_842663 : CollatzResearch.WordTrace tailWord_842663 prefixEnd_842663 192307177226551915927631 := by
  unfold tailWord_842663
  simp only [CollatzResearch.WordTrace]
  refine ⟨30734444546183341227820643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20489629697455560818547095 30734444546183341227820643)
  ·
    refine ⟨46101666819275011841730965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30734444546183341227820643 46101666819275011841730965)
    ·
      refine ⟨2161015632153516180081139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46101666819275011841730965 2161015632153516180081139)
      ·
        refine ⟨3241523448230274270121709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2161015632153516180081139 3241523448230274270121709)
        ·
          refine ⟨1215571293086352851295641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3241523448230274270121709 1215571293086352851295641)
          ·
            refine ⟨911678469814764638471731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215571293086352851295641 911678469814764638471731)
            ·
              refine ⟨1367517704722146957707597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911678469814764638471731 1367517704722146957707597)
              ·
                refine ⟨512819139270805109140349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1367517704722146957707597 512819139270805109140349)
                ·
                  refine ⟨192307177226551915927631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 512819139270805109140349 192307177226551915927631)
                  ·
                    rfl

theorem cell21_842663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 3].length) (baseStart_842663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842663 prefixEnd_842663 := by exact prefixLift 842663
  have htrace : WordTrace (prefixWord ++ tailWord_842663) baseStart_842663 baseEnd_842663 := by
    simpa [prefixWord, tailWord_842663, baseEnd_842663] using wordTrace_append hprefix tailTrace_842663
  have hstable : (prefixWord ++ tailWord_842663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842663).length < 2 ^ (prefixWord ++ tailWord_842663).sum := by decide
  have hdescent : baseEnd_842663 < baseStart_842663 := by decide
  rcases family_descends (prefixWord ++ tailWord_842663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842688 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 5]
def baseStart_842688 : Nat := 118140960795 + 842688 * 2 ^ 59
def prefixEnd_842688 : Nat := 4983230072969 + 3 ^ 40 * 842688 * 2
def baseEnd_842688 : Nat := 192312882567157428010913

theorem tailTrace_842688 : CollatzResearch.WordTrace tailWord_842688 prefixEnd_842688 192312882567157428010913 := by
  unfold tailWord_842688
  simp only [CollatzResearch.WordTrace]
  refine ⟨15367678185546385248740359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20490237580728513664987145 15367678185546385248740359)
  ·
    refine ⟨23051517278319577873110539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15367678185546385248740359 23051517278319577873110539)
    ·
      refine ⟨34577275917479366809665809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23051517278319577873110539 34577275917479366809665809)
      ·
        refine ⟨25932956938109525107249357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34577275917479366809665809 25932956938109525107249357)
        ·
          refine ⟨9724858851791071915218509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25932956938109525107249357 9724858851791071915218509)
          ·
            refine ⟨3646822069421651968206941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9724858851791071915218509 3646822069421651968206941)
            ·
              refine ⟨1367558276033119488077603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3646822069421651968206941 1367558276033119488077603)
              ·
                refine ⟨2051337414049679232116405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367558276033119488077603 2051337414049679232116405)
                ·
                  refine ⟨192312882567157428010913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2051337414049679232116405 192312882567157428010913)
                  ·
                    rfl

theorem cell21_842688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_842688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842688 prefixEnd_842688 := by exact prefixLift 842688
  have htrace : WordTrace (prefixWord ++ tailWord_842688) baseStart_842688 baseEnd_842688 := by
    simpa [prefixWord, tailWord_842688, baseEnd_842688] using wordTrace_append hprefix tailTrace_842688
  have hstable : (prefixWord ++ tailWord_842688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842688).length < 2 ^ (prefixWord ++ tailWord_842688).sum := by decide
  have hdescent : baseEnd_842688 < baseStart_842688 := by decide
  rcases family_descends (prefixWord ++ tailWord_842688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842747 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 5]
def baseStart_842747 : Nat := 118140960795 + 842747 * 2 ^ 59
def prefixEnd_842747 : Nat := 4983230072969 + 3 ^ 40 * 842747 * 2
def baseEnd_842747 : Nat := 192326347170986436527459

theorem tailTrace_842747 : CollatzResearch.WordTrace tailWord_842747 prefixEnd_842747 192326347170986436527459 := by
  unfold tailWord_842747
  simp only [CollatzResearch.WordTrace]
  refine ⟨30737508277879023573878495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20491672185252682382585663 30737508277879023573878495)
  ·
    refine ⟨46106262416818535360817743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30737508277879023573878495 46106262416818535360817743)
    ·
      refine ⟨69159393625227803041226615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46106262416818535360817743 69159393625227803041226615)
      ·
        refine ⟨103739090437841704561839923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69159393625227803041226615 103739090437841704561839923)
        ·
          refine ⟨155608635656762556842759885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103739090437841704561839923 155608635656762556842759885)
          ·
            refine ⟨58353238371285958816034957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155608635656762556842759885 58353238371285958816034957)
            ·
              refine ⟨21882464389232234556013109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58353238371285958816034957 21882464389232234556013109)
              ·
                refine ⟨2051481036490521989626229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21882464389232234556013109 2051481036490521989626229)
                ·
                  refine ⟨192326347170986436527459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2051481036490521989626229 192326347170986436527459)
                  ·
                    rfl

theorem cell21_842747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 5].length) (baseStart_842747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842747 prefixEnd_842747 := by exact prefixLift 842747
  have htrace : WordTrace (prefixWord ++ tailWord_842747) baseStart_842747 baseEnd_842747 := by
    simpa [prefixWord, tailWord_842747, baseEnd_842747] using wordTrace_append hprefix tailTrace_842747
  have hstable : (prefixWord ++ tailWord_842747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842747).length < 2 ^ (prefixWord ++ tailWord_842747).sum := by decide
  have hdescent : baseEnd_842747 < baseStart_842747 := by decide
  rcases family_descends (prefixWord ++ tailWord_842747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842764 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 5]
def baseStart_842764 : Nat := 118140960795 + 842764 * 2 ^ 59
def prefixEnd_842764 : Nat := 4983230072969 + 3 ^ 40 * 842764 * 2
def baseEnd_842764 : Nat := 192330226802598184744091

theorem tailTrace_842764 : CollatzResearch.WordTrace tailWord_842764 prefixEnd_842764 192330226802598184744091 := by
  unfold tailWord_842764
  simp only [CollatzResearch.WordTrace]
  refine ⟨15369064159408717738623673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20492085545878290318164897 15369064159408717738623673)
  ·
    refine ⟨11526798119556538303967755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15369064159408717738623673 11526798119556538303967755)
    ·
      refine ⟨17290197179334807455951633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11526798119556538303967755 17290197179334807455951633)
      ·
        refine ⟨12967647884501105591963725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17290197179334807455951633 12967647884501105591963725)
        ·
          refine ⟨4862867956687914596986397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12967647884501105591963725 4862867956687914596986397)
          ·
            refine ⟨1823575483757967973869899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4862867956687914596986397 1823575483757967973869899)
            ·
              refine ⟨2735363225636951960804849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1823575483757967973869899 2735363225636951960804849)
              ·
                refine ⟨2051522419227713970603637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2735363225636951960804849 2051522419227713970603637)
                ·
                  refine ⟨192330226802598184744091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2051522419227713970603637 192330226802598184744091)
                  ·
                    rfl

theorem cell21_842764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_842764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842764 prefixEnd_842764 := by exact prefixLift 842764
  have htrace : WordTrace (prefixWord ++ tailWord_842764) baseStart_842764 baseEnd_842764 := by
    simpa [prefixWord, tailWord_842764, baseEnd_842764] using wordTrace_append hprefix tailTrace_842764
  have hstable : (prefixWord ++ tailWord_842764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842764).length < 2 ^ (prefixWord ++ tailWord_842764).sum := by decide
  have hdescent : baseEnd_842764 < baseStart_842764 := by decide
  rcases family_descends (prefixWord ++ tailWord_842764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842778 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_842778 : Nat := 118140960795 + 842778 * 2 ^ 59
def prefixEnd_842778 : Nat := 4983230072969 + 3 ^ 40 * 842778 * 2
def baseEnd_842778 : Nat := 192333421793337271510729

theorem tailTrace_842778 : CollatzResearch.WordTrace tailWord_842778 prefixEnd_842778 192333421793337271510729 := by
  unfold tailWord_842778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7684659735191678967064247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20492425960511143912171325 7684659735191678967064247)
  ·
    refine ⟨11526989602787518450596371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7684659735191678967064247 11526989602787518450596371)
    ·
      refine ⟨17290484404181277675894557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11526989602787518450596371 17290484404181277675894557)
      ·
        refine ⟨6483931651567979128460459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17290484404181277675894557 6483931651567979128460459)
        ·
          refine ⟨9725897477351968692690689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6483931651567979128460459 9725897477351968692690689)
          ·
            refine ⟨7294423108013976519518017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9725897477351968692690689 7294423108013976519518017)
            ·
              refine ⟨5470817331010482389638513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7294423108013976519518017 5470817331010482389638513)
              ·
                refine ⟨4103112998257861792228885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5470817331010482389638513 4103112998257861792228885)
                ·
                  refine ⟨192333421793337271510729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4103112998257861792228885 192333421793337271510729)
                  ·
                    rfl

theorem cell21_842778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_842778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842778 prefixEnd_842778 := by exact prefixLift 842778
  have htrace : WordTrace (prefixWord ++ tailWord_842778) baseStart_842778 baseEnd_842778 := by
    simpa [prefixWord, tailWord_842778, baseEnd_842778] using wordTrace_append hprefix tailTrace_842778
  have hstable : (prefixWord ++ tailWord_842778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842778).length < 2 ^ (prefixWord ++ tailWord_842778).sum := by decide
  have hdescent : baseEnd_842778 < baseStart_842778 := by decide
  rcases family_descends (prefixWord ++ tailWord_842778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842812 : List Nat := [2, 2, 2, 2, 2, 3, 3, 1, 4]
def baseStart_842812 : Nat := 118140960795 + 842812 * 2 ^ 59
def prefixEnd_842812 : Nat := 4983230072969 + 3 ^ 40 * 842812 * 2
def baseEnd_842812 : Nat := 192341181056560767943993

theorem tailTrace_842812 : CollatzResearch.WordTrace tailWord_842812 prefixEnd_842812 192341181056560767943993 := by
  unfold tailWord_842812
  simp only [CollatzResearch.WordTrace]
  refine ⟨15369939511321769837497345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20493252681762359783329793 15369939511321769837497345)
  ·
    refine ⟨11527454633491327378123009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15369939511321769837497345 11527454633491327378123009)
    ·
      refine ⟨8645590975118495533592257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11527454633491327378123009 8645590975118495533592257)
      ·
        refine ⟨6484193231338871650194193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8645590975118495533592257 6484193231338871650194193)
        ·
          refine ⟨4863144923504153737645645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6484193231338871650194193 4863144923504153737645645)
          ·
            refine ⟨1823679346314057651617117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4863144923504153737645645 1823679346314057651617117)
            ·
              refine ⟨683879754867771619356419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1823679346314057651617117 683879754867771619356419)
              ·
                refine ⟨1025819632301657429034629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683879754867771619356419 1025819632301657429034629)
                ·
                  refine ⟨192341181056560767943993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1025819632301657429034629 192341181056560767943993)
                  ·
                    rfl

theorem cell21_842812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_842812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842812 prefixEnd_842812 := by exact prefixLift 842812
  have htrace : WordTrace (prefixWord ++ tailWord_842812) baseStart_842812 baseEnd_842812 := by
    simpa [prefixWord, tailWord_842812, baseEnd_842812] using wordTrace_append hprefix tailTrace_842812
  have hstable : (prefixWord ++ tailWord_842812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842812).length < 2 ^ (prefixWord ++ tailWord_842812).sum := by decide
  have hdescent : baseEnd_842812 < baseStart_842812 := by decide
  rcases family_descends (prefixWord ++ tailWord_842812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842964 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 6]
def baseStart_842964 : Nat := 118140960795 + 842964 * 2 ^ 59
def prefixEnd_842964 : Nat := 4983230072969 + 3 ^ 40 * 842964 * 2
def baseEnd_842964 : Nat := 192375869527442281410349

theorem tailTrace_842964 : CollatzResearch.WordTrace tailWord_842964 prefixEnd_842964 192375869527442281410349 := by
  unfold tailWord_842964
  simp only [CollatzResearch.WordTrace]
  refine ⟨15372711459046434817263973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20496948612061913089685297 15372711459046434817263973)
  ·
    refine ⟨2882383398571206528236995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15372711459046434817263973 2882383398571206528236995)
    ·
      refine ⟨4323575097856809792355493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2882383398571206528236995 4323575097856809792355493)
      ·
        refine ⟨810670330848151836066655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4323575097856809792355493 810670330848151836066655)
        ·
          refine ⟨1216005496272227754099983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810670330848151836066655 1216005496272227754099983)
          ·
            refine ⟨1824008244408341631149975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216005496272227754099983 1824008244408341631149975)
            ·
              refine ⟨2736012366612512446724963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824008244408341631149975 2736012366612512446724963)
              ·
                refine ⟨4104018549918768670087445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2736012366612512446724963 4104018549918768670087445)
                ·
                  refine ⟨192375869527442281410349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4104018549918768670087445 192375869527442281410349)
                  ·
                    rfl

theorem cell21_842964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_842964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842964 prefixEnd_842964 := by exact prefixLift 842964
  have htrace : WordTrace (prefixWord ++ tailWord_842964) baseStart_842964 baseEnd_842964 := by
    simpa [prefixWord, tailWord_842964, baseEnd_842964] using wordTrace_append hprefix tailTrace_842964
  have hstable : (prefixWord ++ tailWord_842964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842964).length < 2 ^ (prefixWord ++ tailWord_842964).sum := by decide
  have hdescent : baseEnd_842964 < baseStart_842964 := by decide
  rcases family_descends (prefixWord ++ tailWord_842964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842975 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 5]
def baseStart_842975 : Nat := 118140960795 + 842975 * 2 ^ 59
def prefixEnd_842975 : Nat := 4983230072969 + 3 ^ 40 * 842975 * 2
def baseEnd_842975 : Nat := 192378379877308706726993

theorem tailTrace_842975 : CollatzResearch.WordTrace tailWord_842975 prefixEnd_842975 192378379877308706726993 := by
  unfold tailWord_842975
  simp only [CollatzResearch.WordTrace]
  refine ⟨30745824121053018513178379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20497216080702012342118919 30745824121053018513178379)
  ·
    refine ⟨46118736181579527769767569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30745824121053018513178379 46118736181579527769767569)
    ·
      refine ⟨34589052136184645827325677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46118736181579527769767569 34589052136184645827325677)
      ·
        refine ⟨12970894551069242185247129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34589052136184645827325677 12970894551069242185247129)
        ·
          refine ⟨9728170913301931638935347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12970894551069242185247129 9728170913301931638935347)
          ·
            refine ⟨14592256369952897458403021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9728170913301931638935347 14592256369952897458403021)
            ·
              refine ⟨5472096138732336546901133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14592256369952897458403021 5472096138732336546901133)
              ·
                refine ⟨2052036052024626205087925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5472096138732336546901133 2052036052024626205087925)
                ·
                  refine ⟨192378379877308706726993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2052036052024626205087925 192378379877308706726993)
                  ·
                    rfl

theorem cell21_842975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 5].length) (baseStart_842975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_842975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_842975 prefixEnd_842975 := by exact prefixLift 842975
  have htrace : WordTrace (prefixWord ++ tailWord_842975) baseStart_842975 baseEnd_842975 := by
    simpa [prefixWord, tailWord_842975, baseEnd_842975] using wordTrace_append hprefix tailTrace_842975
  have hstable : (prefixWord ++ tailWord_842975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842975).length < 2 ^ (prefixWord ++ tailWord_842975).sum := by decide
  have hdescent : baseEnd_842975 < baseStart_842975 := by decide
  rcases family_descends (prefixWord ++ tailWord_842975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843009 : List Nat := [1, 2, 4, 1, 1, 3, 3, 3, 3]
def baseStart_843009 : Nat := 118140960795 + 843009 * 2 ^ 59
def prefixEnd_843009 : Nat := 4983230072969 + 3 ^ 40 * 843009 * 2
def baseEnd_843009 : Nat := 192386139140532203160257

theorem tailTrace_843009 : CollatzResearch.WordTrace tailWord_843009 prefixEnd_843009 192386139140532203160257 := by
  unfold tailWord_843009
  simp only [CollatzResearch.WordTrace]
  refine ⟨30747064202929842319916081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20498042801953228213277387 30747064202929842319916081)
  ·
    refine ⟨23060298152197381739937061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30747064202929842319916081 23060298152197381739937061)
    ·
      refine ⟨4323805903537009076238199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23060298152197381739937061 4323805903537009076238199)
      ·
        refine ⟨6485708855305513614357299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4323805903537009076238199 6485708855305513614357299)
        ·
          refine ⟨9728563282958270421535949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6485708855305513614357299 9728563282958270421535949)
          ·
            refine ⟨3648211231109351408075981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9728563282958270421535949 3648211231109351408075981)
            ·
              refine ⟨1368079211666006778028493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3648211231109351408075981 1368079211666006778028493)
              ·
                refine ⟨513029704374752541760685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1368079211666006778028493 513029704374752541760685)
                ·
                  refine ⟨192386139140532203160257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513029704374752541760685 192386139140532203160257)
                  ·
                    rfl

theorem cell21_843009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 3].length) (baseStart_843009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843009 prefixEnd_843009 := by exact prefixLift 843009
  have htrace : WordTrace (prefixWord ++ tailWord_843009) baseStart_843009 baseEnd_843009 := by
    simpa [prefixWord, tailWord_843009, baseEnd_843009] using wordTrace_append hprefix tailTrace_843009
  have hstable : (prefixWord ++ tailWord_843009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843009).length < 2 ^ (prefixWord ++ tailWord_843009).sum := by decide
  have hdescent : baseEnd_843009 < baseStart_843009 := by decide
  rcases family_descends (prefixWord ++ tailWord_843009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843020 : List Nat := [2, 2, 1, 2, 2, 3, 9]
def baseStart_843020 : Nat := 118140960795 + 843020 * 2 ^ 59
def prefixEnd_843020 : Nat := 4983230072969 + 3 ^ 40 * 843020 * 2
def baseEnd_843020 : Nat := 21376516610044292052989

theorem tailTrace_843020 : CollatzResearch.WordTrace tailWord_843020 prefixEnd_843020 21376516610044292052989 := by
  unfold tailWord_843020
  simp only [CollatzResearch.WordTrace]
  refine ⟨15373732702944995599283257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20498310270593327465711009 15373732702944995599283257)
  ·
    refine ⟨11530299527208746699462443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15373732702944995599283257 11530299527208746699462443)
    ·
      refine ⟨17295449290813120049193665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11530299527208746699462443 17295449290813120049193665)
      ·
        refine ⟨12971586968109840036895249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17295449290813120049193665 12971586968109840036895249)
        ·
          refine ⟨9728690226082380027671437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12971586968109840036895249 9728690226082380027671437)
          ·
            refine ⟨3648258834780892510376789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9728690226082380027671437 3648258834780892510376789)
            ·
              refine ⟨21376516610044292052989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3648258834780892510376789 21376516610044292052989)
              ·
                rfl

theorem cell21_843020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 9].length) (baseStart_843020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843020 prefixEnd_843020 := by exact prefixLift 843020
  have htrace : WordTrace (prefixWord ++ tailWord_843020) baseStart_843020 baseEnd_843020 := by
    simpa [prefixWord, tailWord_843020, baseEnd_843020] using wordTrace_append hprefix tailTrace_843020
  have hstable : (prefixWord ++ tailWord_843020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843020).length < 2 ^ (prefixWord ++ tailWord_843020).sum := by decide
  have hdescent : baseEnd_843020 < baseStart_843020 := by decide
  rcases family_descends (prefixWord ++ tailWord_843020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843037 : List Nat := [1, 4, 2, 3, 1, 1, 1, 8]
def baseStart_843037 : Nat := 118140960795 + 843037 * 2 ^ 59
def prefixEnd_843037 : Nat := 4983230072969 + 3 ^ 40 * 843037 * 2
def baseEnd_843037 : Nat := 64130843040670125564511

theorem tailTrace_843037 : CollatzResearch.WordTrace tailWord_843037 prefixEnd_843037 64130843040670125564511 := by
  unfold tailWord_843037
  simp only [CollatzResearch.WordTrace]
  refine ⟨30748085446828403101935365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20498723631218935401290243 30748085446828403101935365)
  ·
    refine ⟨5765266021280325581612881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30748085446828403101935365 5765266021280325581612881)
    ·
      refine ⟨4323949515960244186209661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5765266021280325581612881 4323949515960244186209661)
      ·
        refine ⟨1621481068485091569828623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4323949515960244186209661 1621481068485091569828623)
        ·
          refine ⟨2432221602727637354742935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1621481068485091569828623 2432221602727637354742935)
          ·
            refine ⟨3648332404091456032114403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432221602727637354742935 3648332404091456032114403)
            ·
              refine ⟨5472498606137184048171605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648332404091456032114403 5472498606137184048171605)
              ·
                refine ⟨64130843040670125564511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5472498606137184048171605 64130843040670125564511)
                ·
                  rfl

theorem cell21_843037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 8].length) (baseStart_843037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843037 prefixEnd_843037 := by exact prefixLift 843037
  have htrace : WordTrace (prefixWord ++ tailWord_843037) baseStart_843037 baseEnd_843037 := by
    simpa [prefixWord, tailWord_843037, baseEnd_843037] using wordTrace_append hprefix tailTrace_843037
  have hstable : (prefixWord ++ tailWord_843037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843037).length < 2 ^ (prefixWord ++ tailWord_843037).sum := by decide
  have hdescent : baseEnd_843037 < baseStart_843037 := by decide
  rcases family_descends (prefixWord ++ tailWord_843037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843144 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 5]
def baseStart_843144 : Nat := 118140960795 + 843144 * 2 ^ 59
def prefixEnd_843144 : Nat := 4983230072969 + 3 ^ 40 * 843144 * 2
def baseEnd_843144 : Nat := 192416947979801968409981

theorem tailTrace_843144 : CollatzResearch.WordTrace tailWord_843144 prefixEnd_843144 192416947979801968409981 := by
  unfold tailWord_843144
  simp only [CollatzResearch.WordTrace]
  refine ⟨15375994028720380188040243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20501325371627173584053657 15375994028720380188040243)
  ·
    refine ⟨23063991043080570282060365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15375994028720380188040243 23063991043080570282060365)
    ·
      refine ⟨8648996641155213855772637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23063991043080570282060365 8648996641155213855772637)
      ·
        refine ⟨3243373740433205195914739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8648996641155213855772637 3243373740433205195914739)
        ·
          refine ⟨4865060610649807793872109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243373740433205195914739 4865060610649807793872109)
          ·
            refine ⟨1824397728993677922702041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4865060610649807793872109 1824397728993677922702041)
            ·
              refine ⟨1368298296745258442026531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1824397728993677922702041 1368298296745258442026531)
              ·
                refine ⟨2052447445117887663039797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368298296745258442026531 2052447445117887663039797)
                ·
                  refine ⟨192416947979801968409981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2052447445117887663039797 192416947979801968409981)
                  ·
                    rfl

theorem cell21_843144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_843144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843144 prefixEnd_843144 := by exact prefixLift 843144
  have htrace : WordTrace (prefixWord ++ tailWord_843144) baseStart_843144 baseEnd_843144 := by
    simpa [prefixWord, tailWord_843144, baseEnd_843144] using wordTrace_append hprefix tailTrace_843144
  have hstable : (prefixWord ++ tailWord_843144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843144).length < 2 ^ (prefixWord ++ tailWord_843144).sum := by decide
  have hdescent : baseEnd_843144 < baseStart_843144 := by decide
  rcases family_descends (prefixWord ++ tailWord_843144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843164 : List Nat := [2, 2, 3, 4, 2, 1, 2, 5]
def baseStart_843164 : Nat := 118140960795 + 843164 * 2 ^ 59
def prefixEnd_843164 : Nat := 4983230072969 + 3 ^ 40 * 843164 * 2
def baseEnd_843164 : Nat := 64140504084095459358869

theorem tailTrace_843164 : CollatzResearch.WordTrace tailWord_843164 prefixEnd_843164 64140504084095459358869 := by
  unfold tailWord_843164
  simp only [CollatzResearch.WordTrace]
  refine ⟨15376358758684151895904273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20501811678245535861205697 15376358758684151895904273)
  ·
    refine ⟨11532269069013113921928205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15376358758684151895904273 11532269069013113921928205)
    ·
      refine ⟨4324600900879917720723077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11532269069013113921928205 4324600900879917720723077)
      ·
        refine ⟨810862668914984572635577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4324600900879917720723077 810862668914984572635577)
        ·
          refine ⟨608147001686238429476683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 810862668914984572635577 608147001686238429476683)
          ·
            refine ⟨912220502529357644215025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608147001686238429476683 912220502529357644215025)
            ·
              refine ⟨684165376897018233161269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912220502529357644215025 684165376897018233161269)
              ·
                refine ⟨64140504084095459358869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 684165376897018233161269 64140504084095459358869)
                ·
                  rfl

theorem cell21_843164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 5].length) (baseStart_843164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843164 prefixEnd_843164 := by exact prefixLift 843164
  have htrace : WordTrace (prefixWord ++ tailWord_843164) baseStart_843164 baseEnd_843164 := by
    simpa [prefixWord, tailWord_843164, baseEnd_843164] using wordTrace_append hprefix tailTrace_843164
  have hstable : (prefixWord ++ tailWord_843164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843164).length < 2 ^ (prefixWord ++ tailWord_843164).sum := by decide
  have hdescent : baseEnd_843164 < baseStart_843164 := by decide
  rcases family_descends (prefixWord ++ tailWord_843164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843189 : List Nat := [1, 3, 3, 2, 2, 3, 7]
def baseStart_843189 : Nat := 118140960795 + 843189 * 2 ^ 59
def prefixEnd_843189 : Nat := 4983230072969 + 3 ^ 40 * 843189 * 2
def baseEnd_843189 : Nat := 21380801954765765573321

theorem tailTrace_843189 : CollatzResearch.WordTrace tailWord_843189 prefixEnd_843189 21380801954765765573321 := by
  unfold tailWord_843189
  simp only [CollatzResearch.WordTrace]
  refine ⟨30753629342277733061468621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20502419561518488707645747 30753629342277733061468621)
  ·
    refine ⟨11532611003354149898050733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30753629342277733061468621 11532611003354149898050733)
    ·
      refine ⟨4324729126257806211769025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11532611003354149898050733 4324729126257806211769025)
      ·
        refine ⟨3243546844693354658826769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4324729126257806211769025 3243546844693354658826769)
        ·
          refine ⟨2432660133520015994120077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3243546844693354658826769 2432660133520015994120077)
          ·
            refine ⟨912247550070005997795029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2432660133520015994120077 912247550070005997795029)
            ·
              refine ⟨21380801954765765573321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 912247550070005997795029 21380801954765765573321)
              ·
                rfl

theorem cell21_843189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 7].length) (baseStart_843189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843189 prefixEnd_843189 := by exact prefixLift 843189
  have htrace : WordTrace (prefixWord ++ tailWord_843189) baseStart_843189 baseEnd_843189 := by
    simpa [prefixWord, tailWord_843189, baseEnd_843189] using wordTrace_append hprefix tailTrace_843189
  have hstable : (prefixWord ++ tailWord_843189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843189).length < 2 ^ (prefixWord ++ tailWord_843189).sum := by decide
  have hdescent : baseEnd_843189 < baseStart_843189 := by decide
  rcases family_descends (prefixWord ++ tailWord_843189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843203 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 5]
def baseStart_843203 : Nat := 118140960795 + 843203 * 2 ^ 59
def prefixEnd_843203 : Nat := 4983230072969 + 3 ^ 40 * 843203 * 2
def baseEnd_843203 : Nat := 192430412583630976926527

theorem tailTrace_843203 : CollatzResearch.WordTrace tailWord_843203 prefixEnd_843203 192430412583630976926527 := by
  unfold tailWord_843203
  simp only [CollatzResearch.WordTrace]
  refine ⟨30754139964227013452478263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20502759976151342301652175 30754139964227013452478263)
  ·
    refine ⟨46131209946340520178717395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30754139964227013452478263 46131209946340520178717395)
    ·
      refine ⟨69196814919510780268076093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46131209946340520178717395 69196814919510780268076093)
      ·
        refine ⟨25948805594816542600528535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69196814919510780268076093 25948805594816542600528535)
        ·
          refine ⟨38923208392224813900792803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25948805594816542600528535 38923208392224813900792803)
          ·
            refine ⟨58384812588337220851189205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38923208392224813900792803 58384812588337220851189205)
            ·
              refine ⟨1368394045039153613699747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58384812588337220851189205 1368394045039153613699747)
              ·
                refine ⟨2052591067558730420549621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368394045039153613699747 2052591067558730420549621)
                ·
                  refine ⟨192430412583630976926527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2052591067558730420549621 192430412583630976926527)
                  ·
                    rfl

theorem cell21_843203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 5].length) (baseStart_843203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843203 prefixEnd_843203 := by exact prefixLift 843203
  have htrace : WordTrace (prefixWord ++ tailWord_843203) baseStart_843203 baseEnd_843203 := by
    simpa [prefixWord, tailWord_843203, baseEnd_843203] using wordTrace_append hprefix tailTrace_843203
  have hstable : (prefixWord ++ tailWord_843203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843203).length < 2 ^ (prefixWord ++ tailWord_843203).sum := by decide
  have hdescent : baseEnd_843203 < baseStart_843203 := by decide
  rcases family_descends (prefixWord ++ tailWord_843203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843254 : List Nat := [5, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_843254 : Nat := 118140960795 + 843254 * 2 ^ 59
def prefixEnd_843254 : Nat := 4983230072969 + 3 ^ 40 * 843254 * 2
def baseEnd_843254 : Nat := 192442051478466221576423

theorem tailTrace_843254 : CollatzResearch.WordTrace tailWord_843254 prefixEnd_843254 192442051478466221576423 := by
  unfold tailWord_843254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922250005440140572661551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20504000058028166108389877 1922250005440140572661551)
  ·
    refine ⟨2883375008160210858992327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1922250005440140572661551 2883375008160210858992327)
    ·
      refine ⟨4325062512240316288488491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2883375008160210858992327 4325062512240316288488491)
      ·
        refine ⟨6487593768360474432732737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4325062512240316288488491 6487593768360474432732737)
        ·
          refine ⟨4865695326270355824549553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6487593768360474432732737 4865695326270355824549553)
          ·
            refine ⟨3649271494702766868412165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4865695326270355824549553 3649271494702766868412165)
            ·
              refine ⟨684238405256768787827281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3649271494702766868412165 684238405256768787827281)
              ·
                refine ⟨513178803942576590870461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684238405256768787827281 513178803942576590870461)
                ·
                  refine ⟨192442051478466221576423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513178803942576590870461 192442051478466221576423)
                  ·
                    rfl

theorem cell21_843254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_843254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843254 prefixEnd_843254 := by exact prefixLift 843254
  have htrace : WordTrace (prefixWord ++ tailWord_843254) baseStart_843254 baseEnd_843254 := by
    simpa [prefixWord, tailWord_843254, baseEnd_843254] using wordTrace_append hprefix tailTrace_843254
  have hstable : (prefixWord ++ tailWord_843254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843254).length < 2 ^ (prefixWord ++ tailWord_843254).sum := by decide
  have hdescent : baseEnd_843254 < baseStart_843254 := by decide
  rcases family_descends (prefixWord ++ tailWord_843254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843327 : List Nat := [1, 1, 2, 2, 3, 4, 3, 1, 4]
def baseStart_843327 : Nat := 118140960795 + 843327 * 2 ^ 59
def prefixEnd_843327 : Nat := 4983230072969 + 3 ^ 40 * 843327 * 2
def baseEnd_843327 : Nat := 192458711073034316859607

theorem tailTrace_843327 : CollatzResearch.WordTrace tailWord_843327 prefixEnd_843327 192458711073034316859607 := by
  unfold tailWord_843327
  simp only [CollatzResearch.WordTrace]
  refine ⟨30758662615777782629992235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20505775077185188419994823 30758662615777782629992235)
  ·
    refine ⟨46137993923666673944988353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30758662615777782629992235 46137993923666673944988353)
    ·
      refine ⟨34603495442750005458741265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46137993923666673944988353 34603495442750005458741265)
      ·
        refine ⟨25952621582062504094055949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34603495442750005458741265 25952621582062504094055949)
        ·
          refine ⟨9732233093273439035270981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25952621582062504094055949 9732233093273439035270981)
          ·
            refine ⟨1824793704988769819113309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9732233093273439035270981 1824793704988769819113309)
            ·
              refine ⟨684297639370788682167491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1824793704988769819113309 684297639370788682167491)
              ·
                refine ⟨1026446459056183023251237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684297639370788682167491 1026446459056183023251237)
                ·
                  refine ⟨192458711073034316859607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1026446459056183023251237 192458711073034316859607)
                  ·
                    rfl

theorem cell21_843327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 4].length) (baseStart_843327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843327 prefixEnd_843327 := by exact prefixLift 843327
  have htrace : WordTrace (prefixWord ++ tailWord_843327) baseStart_843327 baseEnd_843327 := by
    simpa [prefixWord, tailWord_843327, baseEnd_843327] using wordTrace_append hprefix tailTrace_843327
  have hstable : (prefixWord ++ tailWord_843327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843327).length < 2 ^ (prefixWord ++ tailWord_843327).sum := by decide
  have hdescent : baseEnd_843327 < baseStart_843327 := by decide
  rcases family_descends (prefixWord ++ tailWord_843327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843369 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 6]
def baseStart_843369 : Nat := 118140960795 + 843369 * 2 ^ 59
def prefixEnd_843369 : Nat := 4983230072969 + 3 ^ 40 * 843369 * 2
def baseEnd_843369 : Nat := 192468296045251577159521

theorem tailTrace_843369 : CollatzResearch.WordTrace tailWord_843369 prefixEnd_843369 192468296045251577159521 := by
  unfold tailWord_843369
  simp only [CollatzResearch.WordTrace]
  refine ⟨30760194481625623803021161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20506796321083749202014107 30760194481625623803021161)
  ·
    refine ⟨23070145861219217852265871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30760194481625623803021161 23070145861219217852265871)
    ·
      refine ⟨34605218791828826778398807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23070145861219217852265871 34605218791828826778398807)
      ·
        refine ⟨51907828187743240167598211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34605218791828826778398807 51907828187743240167598211)
        ·
          refine ⟨77861742281614860251397317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51907828187743240167598211 77861742281614860251397317)
          ·
            refine ⟨14599076677802786297136997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77861742281614860251397317 14599076677802786297136997)
            ·
              refine ⟨2737326877088022430713187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14599076677802786297136997 2737326877088022430713187)
              ·
                refine ⟨4105990315632033646069781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737326877088022430713187 4105990315632033646069781)
                ·
                  refine ⟨192468296045251577159521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4105990315632033646069781 192468296045251577159521)
                  ·
                    rfl

theorem cell21_843369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_843369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843369 prefixEnd_843369 := by exact prefixLift 843369
  have htrace : WordTrace (prefixWord ++ tailWord_843369) baseStart_843369 baseEnd_843369 := by
    simpa [prefixWord, tailWord_843369, baseEnd_843369] using wordTrace_append hprefix tailTrace_843369
  have hstable : (prefixWord ++ tailWord_843369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843369).length < 2 ^ (prefixWord ++ tailWord_843369).sum := by decide
  have hdescent : baseEnd_843369 < baseStart_843369 := by decide
  rcases family_descends (prefixWord ++ tailWord_843369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843423 : List Nat := [1, 1, 2, 7, 1, 2, 2, 2, 3]
def baseStart_843423 : Nat := 118140960795 + 843423 * 2 ^ 59
def prefixEnd_843423 : Nat := 4983230072969 + 3 ^ 40 * 843423 * 2
def baseEnd_843423 : Nat := 192480619580959483259411

theorem tailTrace_843423 : CollatzResearch.WordTrace tailWord_843423 prefixEnd_843423 192480619580959483259411 := by
  unfold tailWord_843423
  simp only [CollatzResearch.WordTrace]
  refine ⟨30762164023429991025486923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20508109348953327350324615 30762164023429991025486923)
  ·
    refine ⟨46143246035144986538230385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30762164023429991025486923 46143246035144986538230385)
    ·
      refine ⟨34607434526358739903672789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46143246035144986538230385 34607434526358739903672789)
      ·
        refine ⟨811111746711532966492331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 34607434526358739903672789 811111746711532966492331)
        ·
          refine ⟨1216667620067299449738497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811111746711532966492331 1216667620067299449738497)
          ·
            refine ⟨912500715050474587303873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1216667620067299449738497 912500715050474587303873)
            ·
              refine ⟨684375536287855940477905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912500715050474587303873 684375536287855940477905)
              ·
                refine ⟨513281652215891955358429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684375536287855940477905 513281652215891955358429)
                ·
                  refine ⟨192480619580959483259411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513281652215891955358429 192480619580959483259411)
                  ·
                    rfl

theorem cell21_843423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 3].length) (baseStart_843423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843423 prefixEnd_843423 := by exact prefixLift 843423
  have htrace : WordTrace (prefixWord ++ tailWord_843423) baseStart_843423 baseEnd_843423 := by
    simpa [prefixWord, tailWord_843423, baseEnd_843423] using wordTrace_append hprefix tailTrace_843423
  have hstable : (prefixWord ++ tailWord_843423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843423).length < 2 ^ (prefixWord ++ tailWord_843423).sum := by decide
  have hdescent : baseEnd_843423 < baseStart_843423 := by decide
  rcases family_descends (prefixWord ++ tailWord_843423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843510 : List Nat := [5, 1, 1, 1, 1, 5, 2, 5]
def baseStart_843510 : Nat := 118140960795 + 843510 * 2 ^ 59
def prefixEnd_843510 : Nat := 4983230072969 + 3 ^ 40 * 843510 * 2
def baseEnd_843510 : Nat := 64166824722088888436411

theorem tailTrace_843510 : CollatzResearch.WordTrace tailWord_843510 prefixEnd_843510 64166824722088888436411 := by
  unfold tailWord_843510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922833573382175305243999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20510224782743203255935989 1922833573382175305243999)
  ·
    refine ⟨2884250360073262957865999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1922833573382175305243999 2884250360073262957865999)
    ·
      refine ⟨4326375540109894436798999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2884250360073262957865999 4326375540109894436798999)
      ·
        refine ⟨6489563310164841655198499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326375540109894436798999 6489563310164841655198499)
        ·
          refine ⟨9734344965247262482797749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6489563310164841655198499 9734344965247262482797749)
          ·
            refine ⟨912594840491930857762289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9734344965247262482797749 912594840491930857762289)
            ·
              refine ⟨684446130368948143321717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912594840491930857762289 684446130368948143321717)
              ·
                refine ⟨64166824722088888436411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 684446130368948143321717 64166824722088888436411)
                ·
                  rfl

theorem cell21_843510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_843510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843510 prefixEnd_843510 := by exact prefixLift 843510
  have htrace : WordTrace (prefixWord ++ tailWord_843510) baseStart_843510 baseEnd_843510 := by
    simpa [prefixWord, tailWord_843510, baseEnd_843510] using wordTrace_append hprefix tailTrace_843510
  have hstable : (prefixWord ++ tailWord_843510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843510).length < 2 ^ (prefixWord ++ tailWord_843510).sum := by decide
  have hdescent : baseEnd_843510 < baseStart_843510 := by decide
  rcases family_descends (prefixWord ++ tailWord_843510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843521 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 6]
def baseStart_843521 : Nat := 118140960795 + 843521 * 2 ^ 59
def prefixEnd_843521 : Nat := 4983230072969 + 3 ^ 40 * 843521 * 2
def baseEnd_843521 : Nat := 192502984516133090625877

theorem tailTrace_843521 : CollatzResearch.WordTrace tailWord_843521 prefixEnd_843521 192502984516133090625877 := by
  unfold tailWord_843521
  simp only [CollatzResearch.WordTrace]
  refine ⟨30765738377074953762554417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20510492251383302508369611 30765738377074953762554417)
  ·
    refine ⟨23074303782806215321915813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30765738377074953762554417 23074303782806215321915813)
    ·
      refine ⟨4326431959276165372859215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23074303782806215321915813 4326431959276165372859215)
      ·
        refine ⟨6489647938914248059288823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326431959276165372859215 6489647938914248059288823)
        ·
          refine ⟨9734471908371372088933235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6489647938914248059288823 9734471908371372088933235)
          ·
            refine ⟨14601707862557058133399853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9734471908371372088933235 14601707862557058133399853)
            ·
              refine ⟨5475640448458896800024945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14601707862557058133399853 5475640448458896800024945)
              ·
                refine ⟨4106730336344172600018709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5475640448458896800024945 4106730336344172600018709)
                ·
                  refine ⟨192502984516133090625877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4106730336344172600018709 192502984516133090625877)
                  ·
                    rfl

theorem cell21_843521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_843521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843521 prefixEnd_843521 := by exact prefixLift 843521
  have htrace : WordTrace (prefixWord ++ tailWord_843521) baseStart_843521 baseEnd_843521 := by
    simpa [prefixWord, tailWord_843521, baseEnd_843521] using wordTrace_append hprefix tailTrace_843521
  have hstable : (prefixWord ++ tailWord_843521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843521).length < 2 ^ (prefixWord ++ tailWord_843521).sum := by decide
  have hdescent : baseEnd_843521 < baseStart_843521 := by decide
  rcases family_descends (prefixWord ++ tailWord_843521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843533 : List Nat := [1, 7, 2, 1, 1, 1, 3, 2, 3]
def baseStart_843533 : Nat := 118140960795 + 843533 * 2 ^ 59
def prefixEnd_843533 : Nat := 4983230072969 + 3 ^ 40 * 843533 * 2
def baseEnd_843533 : Nat := 192505723079623736425853

theorem tailTrace_843533 : CollatzResearch.WordTrace tailWord_843533 prefixEnd_843533 192505723079623736425853 := by
  unfold tailWord_843533
  simp only [CollatzResearch.WordTrace]
  refine ⟨30766176053031479811991253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20510784035354319874660835 30766176053031479811991253)
  ·
    refine ⟨721082251242925308093545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30766176053031479811991253 721082251242925308093545)
    ·
      refine ⟨540811688432193981070159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 721082251242925308093545 540811688432193981070159)
      ·
        refine ⟨811217532648290971605239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540811688432193981070159 811217532648290971605239)
        ·
          refine ⟨1216826298972436457407859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811217532648290971605239 1216826298972436457407859)
          ·
            refine ⟨1825239448458654686111789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216826298972436457407859 1825239448458654686111789)
            ·
              refine ⟨684464793171995507291921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1825239448458654686111789 684464793171995507291921)
              ·
                refine ⟨513348594878996630468941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684464793171995507291921 513348594878996630468941)
                ·
                  refine ⟨192505723079623736425853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513348594878996630468941 192505723079623736425853)
                  ·
                    rfl

theorem cell21_843533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_843533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843533 prefixEnd_843533 := by exact prefixLift 843533
  have htrace : WordTrace (prefixWord ++ tailWord_843533) baseStart_843533 baseEnd_843533 := by
    simpa [prefixWord, tailWord_843533, baseEnd_843533] using wordTrace_append hprefix tailTrace_843533
  have hstable : (prefixWord ++ tailWord_843533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843533).length < 2 ^ (prefixWord ++ tailWord_843533).sum := by decide
  have hdescent : baseEnd_843533 < baseStart_843533 := by decide
  rcases family_descends (prefixWord ++ tailWord_843533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843541 : List Nat := [1, 3, 2, 1, 2, 4, 3, 2, 3]
def baseStart_843541 : Nat := 118140960795 + 843541 * 2 ^ 59
def prefixEnd_843541 : Nat := 4983230072969 + 3 ^ 40 * 843541 * 2
def baseEnd_843541 : Nat := 192507548788617500292503

theorem tailTrace_843541 : CollatzResearch.WordTrace tailWord_843541 prefixEnd_843541 192507548788617500292503 := by
  unfold tailWord_843541
  simp only [CollatzResearch.WordTrace]
  refine ⟨30766467837002497178282477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20510978558001664785521651 30766467837002497178282477)
  ·
    refine ⟨11537425438875936441855929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30766467837002497178282477 11537425438875936441855929)
    ·
      refine ⟨8653069079156952331391947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11537425438875936441855929 8653069079156952331391947)
      ·
        refine ⟨12979603618735428497087921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8653069079156952331391947 12979603618735428497087921)
        ·
          refine ⟨9734702714051571372815941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12979603618735428497087921 9734702714051571372815941)
          ·
            refine ⟨1825256758884669632402989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9734702714051571372815941 1825256758884669632402989)
            ·
              refine ⟨684471284581751112151121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1825256758884669632402989 684471284581751112151121)
              ·
                refine ⟨513353463436313334113341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684471284581751112151121 513353463436313334113341)
                ·
                  refine ⟨192507548788617500292503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513353463436313334113341 192507548788617500292503)
                  ·
                    rfl

theorem cell21_843541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_843541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843541 prefixEnd_843541 := by exact prefixLift 843541
  have htrace : WordTrace (prefixWord ++ tailWord_843541) baseStart_843541 baseEnd_843541 := by
    simpa [prefixWord, tailWord_843541, baseEnd_843541] using wordTrace_append hprefix tailTrace_843541
  have hstable : (prefixWord ++ tailWord_843541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843541).length < 2 ^ (prefixWord ++ tailWord_843541).sum := by decide
  have hdescent : baseEnd_843541 < baseStart_843541 := by decide
  rcases family_descends (prefixWord ++ tailWord_843541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843552 : List Nat := [2, 1, 1, 5, 1, 1, 4, 6]
def baseStart_843552 : Nat := 118140960795 + 843552 * 2 ^ 59
def prefixEnd_843552 : Nat := 4983230072969 + 3 ^ 40 * 843552 * 2
def baseEnd_843552 : Nat := 64170019712827975203049

theorem tailTrace_843552 : CollatzResearch.WordTrace tailWord_843552 prefixEnd_843552 64170019712827975203049 := by
  unfold tailWord_843552
  simp only [CollatzResearch.WordTrace]
  refine ⟨15383434519981323028466455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20511246026641764037955273 15383434519981323028466455)
  ·
    refine ⟨23075151779971984542699683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15383434519981323028466455 23075151779971984542699683)
    ·
      refine ⟨34612727669957976814049525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23075151779971984542699683 34612727669957976814049525)
      ·
        refine ⟨3244943219058560326317143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34612727669957976814049525 3244943219058560326317143)
        ·
          refine ⟨4867414828587840489475715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3244943219058560326317143 4867414828587840489475715)
          ·
            refine ⟨7301122242881760734213573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4867414828587840489475715 7301122242881760734213573)
            ·
              refine ⟨1368960420540330137665045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7301122242881760734213573 1368960420540330137665045)
              ·
                refine ⟨64170019712827975203049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1368960420540330137665045 64170019712827975203049)
                ·
                  rfl

theorem cell21_843552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_843552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843552 prefixEnd_843552 := by exact prefixLift 843552
  have htrace : WordTrace (prefixWord ++ tailWord_843552) baseStart_843552 baseEnd_843552 := by
    simpa [prefixWord, tailWord_843552, baseEnd_843552] using wordTrace_append hprefix tailTrace_843552
  have hstable : (prefixWord ++ tailWord_843552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843552).length < 2 ^ (prefixWord ++ tailWord_843552).sum := by decide
  have hdescent : baseEnd_843552 < baseStart_843552 := by decide
  rcases family_descends (prefixWord ++ tailWord_843552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843673 : List Nat := [1, 2, 1, 2, 1, 3, 2, 5, 4]
def baseStart_843673 : Nat := 118140960795 + 843673 * 2 ^ 59
def prefixEnd_843673 : Nat := 4983230072969 + 3 ^ 40 * 843673 * 2
def baseEnd_843673 : Nat := 192537672987014604092233

theorem tailTrace_843673 : CollatzResearch.WordTrace tailWord_843673 prefixEnd_843673 192537672987014604092233 := by
  unfold tailWord_843673
  simp only [CollatzResearch.WordTrace]
  refine ⟨30771282272524283722087673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20514188181682855814725115 30771282272524283722087673)
  ·
    refine ⟨23078461704393212791565755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30771282272524283722087673 23078461704393212791565755)
    ·
      refine ⟨34617692556589819187348633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23078461704393212791565755 34617692556589819187348633)
      ·
        refine ⟨25963269417442364390511475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34617692556589819187348633 25963269417442364390511475)
        ·
          refine ⟨38944904126163546585767213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25963269417442364390511475 38944904126163546585767213)
          ·
            refine ⟨14604339047311329969662705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38944904126163546585767213 14604339047311329969662705)
            ·
              refine ⟨10953254285483497477247029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14604339047311329969662705 10953254285483497477247029)
              ·
                refine ⟨1026867589264077888491909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10953254285483497477247029 1026867589264077888491909)
                ·
                  refine ⟨192537672987014604092233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1026867589264077888491909 192537672987014604092233)
                  ·
                    rfl

theorem cell21_843673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_843673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843673 prefixEnd_843673 := by exact prefixLift 843673
  have htrace : WordTrace (prefixWord ++ tailWord_843673) baseStart_843673 baseEnd_843673 := by
    simpa [prefixWord, tailWord_843673, baseEnd_843673] using wordTrace_append hprefix tailTrace_843673
  have hstable : (prefixWord ++ tailWord_843673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843673).length < 2 ^ (prefixWord ++ tailWord_843673).sum := by decide
  have hdescent : baseEnd_843673 < baseStart_843673 := by decide
  rcases family_descends (prefixWord ++ tailWord_843673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843769 : List Nat := [1, 2, 1, 3, 1, 6, 2, 2, 3]
def baseStart_843769 : Nat := 118140960795 + 843769 * 2 ^ 59
def prefixEnd_843769 : Nat := 4983230072969 + 3 ^ 40 * 843769 * 2
def baseEnd_843769 : Nat := 192559581494939770492037

theorem tailTrace_843769 : CollatzResearch.WordTrace tailWord_843769 prefixEnd_843769 192559581494939770492037 := by
  unfold tailWord_843769
  simp only [CollatzResearch.WordTrace]
  refine ⟨30774783680176492117582361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20516522453450994745054907 30774783680176492117582361)
  ·
    refine ⟨23081087760132369088186771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30774783680176492117582361 23081087760132369088186771)
    ·
      refine ⟨34621631640198553632280157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23081087760132369088186771 34621631640198553632280157)
      ·
        refine ⟨12983111865074457612105059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34621631640198553632280157 12983111865074457612105059)
        ·
          refine ⟨19474667797611686418157589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12983111865074457612105059 19474667797611686418157589)
          ·
            refine ⟨912875053013047800851137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19474667797611686418157589 912875053013047800851137)
            ·
              refine ⟨684656289759785850638353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912875053013047800851137 684656289759785850638353)
              ·
                refine ⟨513492217319839387978765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684656289759785850638353 513492217319839387978765)
                ·
                  refine ⟨192559581494939770492037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513492217319839387978765 192559581494939770492037)
                  ·
                    rfl

theorem cell21_843769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 3].length) (baseStart_843769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843769 prefixEnd_843769 := by exact prefixLift 843769
  have htrace : WordTrace (prefixWord ++ tailWord_843769) baseStart_843769 baseEnd_843769 := by
    simpa [prefixWord, tailWord_843769, baseEnd_843769] using wordTrace_append hprefix tailTrace_843769
  have hstable : (prefixWord ++ tailWord_843769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843769).length < 2 ^ (prefixWord ++ tailWord_843769).sum := by decide
  have hdescent : baseEnd_843769 < baseStart_843769 := by decide
  rcases family_descends (prefixWord ++ tailWord_843769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843797 : List Nat := [1, 3, 2, 1, 5, 1, 3, 5]
def baseStart_843797 : Nat := 118140960795 + 843797 * 2 ^ 59
def prefixEnd_843797 : Nat := 4983230072969 + 3 ^ 40 * 843797 * 2
def baseEnd_843797 : Nat := 64188657158805981341771

theorem tailTrace_843797 : CollatzResearch.WordTrace tailWord_843797 prefixEnd_843797 64188657158805981341771 := by
  unfold tailWord_843797
  simp only [CollatzResearch.WordTrace]
  refine ⟨30775804924075052899601645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20517203282716701933067763 30775804924075052899601645)
  ·
    refine ⟨11540926846528144837350617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30775804924075052899601645 11540926846528144837350617)
    ·
      refine ⟨8655695134896108628012963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11540926846528144837350617 8655695134896108628012963)
      ·
        refine ⟨12983542702344162942019445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8655695134896108628012963 12983542702344162942019445)
        ·
          refine ⟨1217207128344765275814323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12983542702344162942019445 1217207128344765275814323)
          ·
            refine ⟨1825810692517147913721485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217207128344765275814323 1825810692517147913721485)
            ·
              refine ⟨684679009693930467645557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1825810692517147913721485 684679009693930467645557)
              ·
                refine ⟨64188657158805981341771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 684679009693930467645557 64188657158805981341771)
                ·
                  rfl

theorem cell21_843797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 5].length) (baseStart_843797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843797 prefixEnd_843797 := by exact prefixLift 843797
  have htrace : WordTrace (prefixWord ++ tailWord_843797) baseStart_843797 baseEnd_843797 := by
    simpa [prefixWord, tailWord_843797, baseEnd_843797] using wordTrace_append hprefix tailTrace_843797
  have hstable : (prefixWord ++ tailWord_843797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843797).length < 2 ^ (prefixWord ++ tailWord_843797).sum := by decide
  have hdescent : baseEnd_843797 < baseStart_843797 := by decide
  rcases family_descends (prefixWord ++ tailWord_843797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843825 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 6]
def baseStart_843825 : Nat := 118140960795 + 843825 * 2 ^ 59
def prefixEnd_843825 : Nat := 4983230072969 + 3 ^ 40 * 843825 * 2
def baseEnd_843825 : Nat := 192572361457896117558589

theorem tailTrace_843825 : CollatzResearch.WordTrace tailWord_843825 prefixEnd_843825 192572361457896117558589 := by
  unfold tailWord_843825
  simp only [CollatzResearch.WordTrace]
  refine ⟨30776826167973613681620929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20517884111982409121080619 30776826167973613681620929)
  ·
    refine ⟨23082619625980210261215697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30776826167973613681620929 23082619625980210261215697)
    ·
      refine ⟨17311964719485157695911773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23082619625980210261215697 17311964719485157695911773)
      ·
        refine ⟨6491986769806934135966915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17311964719485157695911773 6491986769806934135966915)
        ·
          refine ⟨9737980154710401203950373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6491986769806934135966915 9737980154710401203950373)
          ·
            refine ⟨1825871279008200225740695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9737980154710401203950373 1825871279008200225740695)
            ·
              refine ⟨2738806918512300338611043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825871279008200225740695 2738806918512300338611043)
              ·
                refine ⟨4108210377768450507916565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2738806918512300338611043 4108210377768450507916565)
                ·
                  refine ⟨192572361457896117558589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4108210377768450507916565 192572361457896117558589)
                  ·
                    rfl

theorem cell21_843825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_843825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843825 prefixEnd_843825 := by exact prefixLift 843825
  have htrace : WordTrace (prefixWord ++ tailWord_843825) baseStart_843825 baseEnd_843825 := by
    simpa [prefixWord, tailWord_843825, baseEnd_843825] using wordTrace_append hprefix tailTrace_843825
  have hstable : (prefixWord ++ tailWord_843825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843825).length < 2 ^ (prefixWord ++ tailWord_843825).sum := by decide
  have hdescent : baseEnd_843825 < baseStart_843825 := by decide
  rcases family_descends (prefixWord ++ tailWord_843825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843862 : List Nat := [5, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_843862 : Nat := 118140960795 + 843862 * 2 ^ 59
def prefixEnd_843862 : Nat := 4983230072969 + 3 ^ 40 * 843862 * 2
def baseEnd_843862 : Nat := 192580805361992275441847

theorem tailTrace_843862 : CollatzResearch.WordTrace tailWord_843862 prefixEnd_843862 192580805361992275441847 := by
  unfold tailWord_843862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923635979302473062544865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20518783779226379333811893 1923635979302473062544865)
  ·
    refine ⟨1442726984476854796908649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1923635979302473062544865 1442726984476854796908649)
    ·
      refine ⟨1082045238357641097681487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1442726984476854796908649 1082045238357641097681487)
      ·
        refine ⟨1623067857536461646522231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082045238357641097681487 1623067857536461646522231)
        ·
          refine ⟨2434601786304692469783347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623067857536461646522231 2434601786304692469783347)
          ·
            refine ⟨3651902679457038704675021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2434601786304692469783347 3651902679457038704675021)
            ·
              refine ⟨1369463504796389514253133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3651902679457038704675021 1369463504796389514253133)
              ·
                refine ⟨513548814298646067844925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1369463504796389514253133 513548814298646067844925)
                ·
                  refine ⟨192580805361992275441847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513548814298646067844925 192580805361992275441847)
                  ·
                    rfl

theorem cell21_843862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_843862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843862 prefixEnd_843862 := by exact prefixLift 843862
  have htrace : WordTrace (prefixWord ++ tailWord_843862) baseStart_843862 baseEnd_843862 := by
    simpa [prefixWord, tailWord_843862, baseEnd_843862] using wordTrace_append hprefix tailTrace_843862
  have hstable : (prefixWord ++ tailWord_843862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843862).length < 2 ^ (prefixWord ++ tailWord_843862).sum := by decide
  have hdescent : baseEnd_843862 < baseStart_843862 := by decide
  rcases family_descends (prefixWord ++ tailWord_843862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843887 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 5]
def baseStart_843887 : Nat := 118140960795 + 843887 * 2 ^ 59
def prefixEnd_843887 : Nat := 4983230072969 + 3 ^ 40 * 843887 * 2
def baseEnd_843887 : Nat := 192586510702597787525129

theorem tailTrace_843887 : CollatzResearch.WordTrace tailWord_843887 prefixEnd_843887 192586510702597787525129 := by
  unfold tailWord_843887
  simp only [CollatzResearch.WordTrace]
  refine ⟨30779087493748998270377915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20519391662499332180251943 30779087493748998270377915)
  ·
    refine ⟨46168631240623497405566873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30779087493748998270377915 46168631240623497405566873)
    ·
      refine ⟨34626473430467623054175155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46168631240623497405566873 34626473430467623054175155)
      ·
        refine ⟨51939710145701434581262733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34626473430467623054175155 51939710145701434581262733)
        ·
          refine ⟨19477391304638037967973525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51939710145701434581262733 19477391304638037967973525)
          ·
            refine ⟨913002717404908029748759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19477391304638037967973525 913002717404908029748759)
            ·
              refine ⟨1369504076107362044623139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913002717404908029748759 1369504076107362044623139)
              ·
                refine ⟨2054256114161043066934709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369504076107362044623139 2054256114161043066934709)
                ·
                  refine ⟨192586510702597787525129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2054256114161043066934709 192586510702597787525129)
                  ·
                    rfl

theorem cell21_843887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 5].length) (baseStart_843887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843887 prefixEnd_843887 := by exact prefixLift 843887
  have htrace : WordTrace (prefixWord ++ tailWord_843887) baseStart_843887 baseEnd_843887 := by
    simpa [prefixWord, tailWord_843887, baseEnd_843887] using wordTrace_append hprefix tailTrace_843887
  have hstable : (prefixWord ++ tailWord_843887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843887).length < 2 ^ (prefixWord ++ tailWord_843887).sum := by decide
  have hdescent : baseEnd_843887 < baseStart_843887 := by decide
  rcases family_descends (prefixWord ++ tailWord_843887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843938 : List Nat := [3, 3, 1, 3, 1, 3, 2, 2, 3]
def baseStart_843938 : Nat := 118140960795 + 843938 * 2 ^ 59
def prefixEnd_843938 : Nat := 4983230072969 + 3 ^ 40 * 843938 * 2
def baseEnd_843938 : Nat := 192598149597433032175025

theorem tailTrace_843938 : CollatzResearch.WordTrace tailWord_843938 prefixEnd_843938 192598149597433032175025 := by
  unfold tailWord_843938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7695236904141058495121117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20520631744376155986989645 7695236904141058495121117)
  ·
    refine ⟨2885713839052896935670419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7695236904141058495121117 2885713839052896935670419)
    ·
      refine ⟨4328570758579345403505629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2885713839052896935670419 4328570758579345403505629)
      ·
        refine ⟨1623214034467254526314611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4328570758579345403505629 1623214034467254526314611)
        ·
          refine ⟨2434821051700881789471917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623214034467254526314611 2434821051700881789471917)
          ·
            refine ⟨913057894387830671051969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2434821051700881789471917 913057894387830671051969)
            ·
              refine ⟨684793420790873003288977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913057894387830671051969 684793420790873003288977)
              ·
                refine ⟨513595065593154752466733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684793420790873003288977 513595065593154752466733)
                ·
                  refine ⟨192598149597433032175025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513595065593154752466733 192598149597433032175025)
                  ·
                    rfl

theorem cell21_843938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_843938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843938 prefixEnd_843938 := by exact prefixLift 843938
  have htrace : WordTrace (prefixWord ++ tailWord_843938) baseStart_843938 baseEnd_843938 := by
    simpa [prefixWord, tailWord_843938, baseEnd_843938] using wordTrace_append hprefix tailTrace_843938
  have hstable : (prefixWord ++ tailWord_843938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843938).length < 2 ^ (prefixWord ++ tailWord_843938).sum := by decide
  have hdescent : baseEnd_843938 < baseStart_843938 := by decide
  rcases family_descends (prefixWord ++ tailWord_843938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843949 : List Nat := [1, 5, 2, 1, 2, 3, 1, 6]
def baseStart_843949 : Nat := 118140960795 + 843949 * 2 ^ 59
def prefixEnd_843949 : Nat := 4983230072969 + 3 ^ 40 * 843949 * 2
def baseEnd_843949 : Nat := 64200219982433152497223

theorem tailTrace_843949 : CollatzResearch.WordTrace tailWord_843949 prefixEnd_843949 64200219982433152497223 := by
  unfold tailWord_843949
  simp only [CollatzResearch.WordTrace]
  refine ⟨30781348819524382859134901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20520899213016255239423267 30781348819524382859134901)
  ·
    refine ⟨2885751451830410893043897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30781348819524382859134901 2885751451830410893043897)
    ·
      refine ⟨2164313588872808169782923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2885751451830410893043897 2164313588872808169782923)
      ·
        refine ⟨3246470383309212254674385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164313588872808169782923 3246470383309212254674385)
        ·
          refine ⟨2434852787481909191005789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3246470383309212254674385 2434852787481909191005789)
          ·
            refine ⟨913069795305715946627171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2434852787481909191005789 913069795305715946627171)
            ·
              refine ⟨1369604692958573919940757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913069795305715946627171 1369604692958573919940757)
              ·
                refine ⟨64200219982433152497223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1369604692958573919940757 64200219982433152497223)
                ·
                  rfl

theorem cell21_843949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 6].length) (baseStart_843949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_843949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_843949 prefixEnd_843949 := by exact prefixLift 843949
  have htrace : WordTrace (prefixWord ++ tailWord_843949) baseStart_843949 baseEnd_843949 := by
    simpa [prefixWord, tailWord_843949, baseEnd_843949] using wordTrace_append hprefix tailTrace_843949
  have hstable : (prefixWord ++ tailWord_843949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843949).length < 2 ^ (prefixWord ++ tailWord_843949).sum := by decide
  have hdescent : baseEnd_843949 < baseStart_843949 := by decide
  rcases family_descends (prefixWord ++ tailWord_843949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844056 : List Nat := [2, 1, 2, 3, 1, 2, 5, 2, 3]
def baseStart_844056 : Nat := 118140960795 + 844056 * 2 ^ 59
def prefixEnd_844056 : Nat := 4983230072969 + 3 ^ 40 * 844056 * 2
def baseEnd_844056 : Nat := 192625078805091049208117

theorem tailTrace_844056 : CollatzResearch.WordTrace tailWord_844056 prefixEnd_844056 192625078805091049208117 := by
  unfold tailWord_844056
  simp only [CollatzResearch.WordTrace]
  refine ⟨15392625715068370066640011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20523500953424493422186681 15392625715068370066640011)
  ·
    refine ⟨23088938572602555099960017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15392625715068370066640011 23088938572602555099960017)
    ·
      refine ⟨17316703929451916324970013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23088938572602555099960017 17316703929451916324970013)
      ·
        refine ⟨6493763973544468621863755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17316703929451916324970013 6493763973544468621863755)
        ·
          refine ⟨9740645960316702932795633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6493763973544468621863755 9740645960316702932795633)
          ·
            refine ⟨7305484470237527199596725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9740645960316702932795633 7305484470237527199596725)
            ·
              refine ⟨684889169084768174962193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7305484470237527199596725 684889169084768174962193)
              ·
                refine ⟨513666876813576131221645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684889169084768174962193 513666876813576131221645)
                ·
                  refine ⟨192625078805091049208117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 513666876813576131221645 192625078805091049208117)
                  ·
                    rfl

theorem cell21_844056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 3].length) (baseStart_844056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844056 prefixEnd_844056 := by exact prefixLift 844056
  have htrace : WordTrace (prefixWord ++ tailWord_844056) baseStart_844056 baseEnd_844056 := by
    simpa [prefixWord, tailWord_844056, baseEnd_844056] using wordTrace_append hprefix tailTrace_844056
  have hstable : (prefixWord ++ tailWord_844056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844056).length < 2 ^ (prefixWord ++ tailWord_844056).sum := by decide
  have hdescent : baseEnd_844056 < baseStart_844056 := by decide
  rcases family_descends (prefixWord ++ tailWord_844056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844067 : List Nat := [1, 1, 1, 4, 2, 2, 4, 6]
def baseStart_844067 : Nat := 118140960795 + 844067 * 2 ^ 59
def prefixEnd_844067 : Nat := 4983230072969 + 3 ^ 40 * 844067 * 2
def baseEnd_844067 : Nat := 64209196384985824841587

theorem tailTrace_844067 : CollatzResearch.WordTrace tailWord_844067 prefixEnd_844067 64209196384985824841587 := by
  unfold tailWord_844067
  simp only [CollatzResearch.WordTrace]
  refine ⟨30785652633096889011930455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20523768422064592674620303 30785652633096889011930455)
  ·
    refine ⟨46178478949645333517895683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30785652633096889011930455 46178478949645333517895683)
    ·
      refine ⟨69267718424468000276843525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46178478949645333517895683 69267718424468000276843525)
      ·
        refine ⟨12987697204587750051908161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69267718424468000276843525 12987697204587750051908161)
        ·
          refine ⟨9740772903440812538931121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12987697204587750051908161 9740772903440812538931121)
          ·
            refine ⟨7305579677580609404198341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9740772903440812538931121 7305579677580609404198341)
            ·
              refine ⟨1369796189546364263287189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7305579677580609404198341 1369796189546364263287189)
              ·
                refine ⟨64209196384985824841587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1369796189546364263287189 64209196384985824841587)
                ·
                  rfl

theorem cell21_844067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 6].length) (baseStart_844067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844067 prefixEnd_844067 := by exact prefixLift 844067
  have htrace : WordTrace (prefixWord ++ tailWord_844067) baseStart_844067 baseEnd_844067 := by
    simpa [prefixWord, tailWord_844067, baseEnd_844067] using wordTrace_append hprefix tailTrace_844067
  have hstable : (prefixWord ++ tailWord_844067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844067).length < 2 ^ (prefixWord ++ tailWord_844067).sum := by decide
  have hdescent : baseEnd_844067 < baseStart_844067 := by decide
  rcases family_descends (prefixWord ++ tailWord_844067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844084 : List Nat := [2, 5, 1, 1, 1, 2, 2, 7]
def baseStart_844084 : Nat := 118140960795 + 844084 * 2 ^ 59
def prefixEnd_844084 : Nat := 4983230072969 + 3 ^ 40 * 844084 * 2
def baseEnd_844084 : Nat := 64210489595523074247131

theorem tailTrace_844084 : CollatzResearch.WordTrace tailWord_844084 prefixEnd_844084 64210489595523074247131 := by
  unfold tailWord_844084
  simp only [CollatzResearch.WordTrace]
  refine ⟨15393136337017650457649653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20524181782690200610199537 15393136337017650457649653)
  ·
    refine ⟨1443106531595404730404655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15393136337017650457649653 1443106531595404730404655)
    ·
      refine ⟨2164659797393107095606983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1443106531595404730404655 2164659797393107095606983)
      ·
        refine ⟨3246989696089660643410475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164659797393107095606983 3246989696089660643410475)
        ·
          refine ⟨4870484544134490965115713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246989696089660643410475 4870484544134490965115713)
          ·
            refine ⟨3652863408100868223836785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4870484544134490965115713 3652863408100868223836785)
            ·
              refine ⟨2739647556075651167877589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3652863408100868223836785 2739647556075651167877589)
              ·
                refine ⟨64210489595523074247131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2739647556075651167877589 64210489595523074247131)
                ·
                  rfl

theorem cell21_844084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_844084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844084 prefixEnd_844084 := by exact prefixLift 844084
  have htrace : WordTrace (prefixWord ++ tailWord_844084) baseStart_844084 baseEnd_844084 := by
    simpa [prefixWord, tailWord_844084, baseEnd_844084] using wordTrace_append hprefix tailTrace_844084
  have hstable : (prefixWord ++ tailWord_844084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844084).length < 2 ^ (prefixWord ++ tailWord_844084).sum := by decide
  have hdescent : baseEnd_844084 < baseStart_844084 := by decide
  rcases family_descends (prefixWord ++ tailWord_844084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844163 : List Nat := [1, 1, 1, 3, 7, 1, 1, 2, 4]
def baseStart_844163 : Nat := 118140960795 + 844163 * 2 ^ 59
def prefixEnd_844163 : Nat := 4983230072969 + 3 ^ 40 * 844163 * 2
def baseEnd_844163 : Nat := 192649497662882640924565

theorem tailTrace_844163 : CollatzResearch.WordTrace tailWord_844163 prefixEnd_844163 192649497662882640924565 := by
  unfold tailWord_844163
  simp only [CollatzResearch.WordTrace]
  refine ⟨30789154040749097407425143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20526102693832731604950095 30789154040749097407425143)
  ·
    refine ⟨46183731061123646111137715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30789154040749097407425143 46183731061123646111137715)
    ·
      refine ⟨69275596591685469166706573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46183731061123646111137715 69275596591685469166706573)
      ·
        refine ⟨25978348721882050937514965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69275596591685469166706573 25978348721882050937514965)
        ·
          refine ⟨608867548169110568848007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 25978348721882050937514965 608867548169110568848007)
          ·
            refine ⟨913301322253665853272011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608867548169110568848007 913301322253665853272011)
            ·
              refine ⟨1369951983380498779908017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913301322253665853272011 1369951983380498779908017)
              ·
                refine ⟨1027463987535374084931013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1369951983380498779908017 1027463987535374084931013)
                ·
                  refine ⟨192649497662882640924565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1027463987535374084931013 192649497662882640924565)
                  ·
                    rfl

theorem cell21_844163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 4].length) (baseStart_844163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844163 prefixEnd_844163 := by exact prefixLift 844163
  have htrace : WordTrace (prefixWord ++ tailWord_844163) baseStart_844163 baseEnd_844163 := by
    simpa [prefixWord, tailWord_844163, baseEnd_844163] using wordTrace_append hprefix tailTrace_844163
  have hstable : (prefixWord ++ tailWord_844163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844163).length < 2 ^ (prefixWord ++ tailWord_844163).sum := by decide
  have hdescent : baseEnd_844163 < baseStart_844163 := by decide
  rcases family_descends (prefixWord ++ tailWord_844163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844236 : List Nat := [2, 2, 1, 4, 3, 1, 2, 6]
def baseStart_844236 : Nat := 118140960795 + 844236 * 2 ^ 59
def prefixEnd_844236 : Nat := 4983230072969 + 3 ^ 40 * 844236 * 2
def baseEnd_844236 : Nat := 64222052419150245402583

theorem tailTrace_844236 : CollatzResearch.WordTrace tailWord_844236 prefixEnd_844236 64222052419150245402583 := by
  unfold tailWord_844236
  simp only [CollatzResearch.WordTrace]
  refine ⟨15395908284742315437416281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20527877712989753916555041 15395908284742315437416281)
  ·
    refine ⟨11546931213556736578062211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15395908284742315437416281 11546931213556736578062211)
    ·
      refine ⟨17320396820335104867093317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11546931213556736578062211 17320396820335104867093317)
      ·
        refine ⟨3247574403812832162579997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17320396820335104867093317 3247574403812832162579997)
        ·
          refine ⟨1217840401429812060967499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3247574403812832162579997 1217840401429812060967499)
          ·
            refine ⟨1826760602144718091451249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217840401429812060967499 1826760602144718091451249)
            ·
              refine ⟨1370070451608538568588437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826760602144718091451249 1370070451608538568588437)
              ·
                refine ⟨64222052419150245402583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1370070451608538568588437 64222052419150245402583)
                ·
                  rfl

theorem cell21_844236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_844236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844236 prefixEnd_844236 := by exact prefixLift 844236
  have htrace : WordTrace (prefixWord ++ tailWord_844236) baseStart_844236 baseEnd_844236 := by
    simpa [prefixWord, tailWord_844236, baseEnd_844236] using wordTrace_append hprefix tailTrace_844236
  have hstable : (prefixWord ++ tailWord_844236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844236).length < 2 ^ (prefixWord ++ tailWord_844236).sum := by decide
  have hdescent : baseEnd_844236 < baseStart_844236 := by decide
  rcases family_descends (prefixWord ++ tailWord_844236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844312 : List Nat := [2, 1, 2, 3, 3, 2, 3, 5]
def baseStart_844312 : Nat := 118140960795 + 844312 * 2 ^ 59
def prefixEnd_844312 : Nat := 4983230072969 + 3 ^ 40 * 844312 * 2
def baseEnd_844312 : Nat := 64227833830963830980309

theorem tailTrace_844312 : CollatzResearch.WordTrace tailWord_844312 prefixEnd_844312 64227833830963830980309 := by
  unfold tailWord_844312
  simp only [CollatzResearch.WordTrace]
  refine ⟨15397294258604647927299595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20529725678139530569732793 15397294258604647927299595)
  ·
    refine ⟨23095941387906971890949393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15397294258604647927299595 23095941387906971890949393)
    ·
      refine ⟨17321956040930228918212045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23095941387906971890949393 17321956040930228918212045)
      ·
        refine ⟨6495733515348835844329517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17321956040930228918212045 6495733515348835844329517)
        ·
          refine ⟨2435900068255813441623569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6495733515348835844329517 2435900068255813441623569)
          ·
            refine ⟨1826925051191860081217677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2435900068255813441623569 1826925051191860081217677)
            ·
              refine ⟨685096894196947530456629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1826925051191860081217677 685096894196947530456629)
              ·
                refine ⟨64227833830963830980309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 685096894196947530456629 64227833830963830980309)
                ·
                  rfl

theorem cell21_844312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 5].length) (baseStart_844312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844312 prefixEnd_844312 := by exact prefixLift 844312
  have htrace : WordTrace (prefixWord ++ tailWord_844312) baseStart_844312 baseEnd_844312 := by
    simpa [prefixWord, tailWord_844312, baseEnd_844312] using wordTrace_append hprefix tailTrace_844312
  have hstable : (prefixWord ++ tailWord_844312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844312).length < 2 ^ (prefixWord ++ tailWord_844312).sum := by decide
  have hdescent : baseEnd_844312 < baseStart_844312 := by decide
  rcases family_descends (prefixWord ++ tailWord_844312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844475 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 10]
def baseStart_844475 : Nat := 118140960795 + 844475 * 2 ^ 59
def prefixEnd_844475 : Nat := 4983230072969 + 3 ^ 40 * 844475 * 2
def baseEnd_844475 : Nat := 192720700313639431723927

theorem tailTrace_844475 : CollatzResearch.WordTrace tailWord_844475 prefixEnd_844475 192720700313639431723927 := by
  unfold tailWord_844475
  simp only [CollatzResearch.WordTrace]
  refine ⟨30800533615618774692782879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20533689077079183128521919 30800533615618774692782879)
  ·
    refine ⟨46200800423428162039174319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30800533615618774692782879 46200800423428162039174319)
    ·
      refine ⟨69301200635142243058761479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46200800423428162039174319 69301200635142243058761479)
      ·
        refine ⟨103951800952713364588142219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69301200635142243058761479 103951800952713364588142219)
        ·
          refine ⟨155927701429070046882213329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103951800952713364588142219 155927701429070046882213329)
          ·
            refine ⟨116945776071802535161659997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155927701429070046882213329 116945776071802535161659997)
            ·
              refine ⟨43854666026925950685622499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116945776071802535161659997 43854666026925950685622499)
              ·
                refine ⟨65781999040388926028433749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43854666026925950685622499 65781999040388926028433749)
                ·
                  refine ⟨192720700313639431723927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 65781999040388926028433749 192720700313639431723927)
                  ·
                    rfl

theorem cell21_844475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_844475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844475 prefixEnd_844475 := by exact prefixLift 844475
  have htrace : WordTrace (prefixWord ++ tailWord_844475) baseStart_844475 baseEnd_844475 := by
    simpa [prefixWord, tailWord_844475, baseEnd_844475] using wordTrace_append hprefix tailTrace_844475
  have hstable : (prefixWord ++ tailWord_844475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844475).length < 2 ^ (prefixWord ++ tailWord_844475).sum := by decide
  have hdescent : baseEnd_844475 < baseStart_844475 := by decide
  rcases family_descends (prefixWord ++ tailWord_844475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844478 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_844478 : Nat := 118140960795 + 844478 * 2 ^ 59
def prefixEnd_844478 : Nat := 4983230072969 + 3 ^ 40 * 844478 * 2
def baseEnd_844478 : Nat := 192721384954512093173921

theorem tailTrace_844478 : CollatzResearch.WordTrace tailWord_844478 prefixEnd_844478 192721384954512093173921 := by
  unfold tailWord_844478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3850080379325988275642761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20533762023071937470094725 3850080379325988275642761)
  ·
    refine ⟨2887560284494491206732071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3850080379325988275642761 2887560284494491206732071)
    ·
      refine ⟨4331340426741736810098107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2887560284494491206732071 4331340426741736810098107)
      ·
        refine ⟨6497010640112605215147161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4331340426741736810098107 6497010640112605215147161)
        ·
          refine ⟨4872757980084453911360371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6497010640112605215147161 4872757980084453911360371)
          ·
            refine ⟨7309136970126680867040557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4872757980084453911360371 7309136970126680867040557)
            ·
              refine ⟨2740926363797505325140209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7309136970126680867040557 2740926363797505325140209)
              ·
                refine ⟨2055694772848128993855157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2740926363797505325140209 2055694772848128993855157)
                ·
                  refine ⟨192721384954512093173921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2055694772848128993855157 192721384954512093173921)
                  ·
                    rfl

theorem cell21_844478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_844478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844478 prefixEnd_844478 := by exact prefixLift 844478
  have htrace : WordTrace (prefixWord ++ tailWord_844478) baseStart_844478 baseEnd_844478 := by
    simpa [prefixWord, tailWord_844478, baseEnd_844478] using wordTrace_append hprefix tailTrace_844478
  have hstable : (prefixWord ++ tailWord_844478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844478).length < 2 ^ (prefixWord ++ tailWord_844478).sum := by decide
  have hdescent : baseEnd_844478 < baseStart_844478 := by decide
  rcases family_descends (prefixWord ++ tailWord_844478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844506 : List Nat := [3, 1, 1, 2, 2, 2, 10]
def baseStart_844506 : Nat := 118140960795 + 844506 * 2 ^ 59
def prefixEnd_844506 : Nat := 4983230072969 + 3 ^ 40 * 844506 * 2
def baseEnd_844506 : Nat := 21414197215110029634133

theorem tailTrace_844506 : CollatzResearch.WordTrace tailWord_844506 prefixEnd_844506 21414197215110029634133 := by
  unfold tailWord_844506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7700416069626616746790343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20534442852337644658107581 7700416069626616746790343)
  ·
    refine ⟨11550624104439925120185515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7700416069626616746790343 11550624104439925120185515)
    ·
      refine ⟨17325936156659887680278273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11550624104439925120185515 17325936156659887680278273)
      ·
        refine ⟨12994452117494915760208705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17325936156659887680278273 12994452117494915760208705)
        ·
          refine ⟨9745839088121186820156529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12994452117494915760208705 9745839088121186820156529)
          ·
            refine ⟨7309379316090890115117397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9745839088121186820156529 7309379316090890115117397)
            ·
              refine ⟨21414197215110029634133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7309379316090890115117397 21414197215110029634133)
              ·
                rfl

theorem cell21_844506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 10].length) (baseStart_844506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844506 prefixEnd_844506 := by exact prefixLift 844506
  have htrace : WordTrace (prefixWord ++ tailWord_844506) baseStart_844506 baseEnd_844506 := by
    simpa [prefixWord, tailWord_844506, baseEnd_844506] using wordTrace_append hprefix tailTrace_844506
  have hstable : (prefixWord ++ tailWord_844506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844506).length < 2 ^ (prefixWord ++ tailWord_844506).sum := by decide
  have hdescent : baseEnd_844506 < baseStart_844506 := by decide
  rcases family_descends (prefixWord ++ tailWord_844506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844526 : List Nat := [4, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_844526 : Nat := 118140960795 + 844526 * 2 ^ 59
def prefixEnd_844526 : Nat := 4983230072969 + 3 ^ 40 * 844526 * 2
def baseEnd_844526 : Nat := 192732339208474676373823

theorem tailTrace_844526 : CollatzResearch.WordTrace tailWord_844526 prefixEnd_844526 192732339208474676373823 := by
  unfold tailWord_844526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3850299217304251300361179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20534929158956006935259621 3850299217304251300361179)
  ·
    refine ⟨5775448825956376950541769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3850299217304251300361179 5775448825956376950541769)
    ·
      refine ⟨4331586619467282712906327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5775448825956376950541769 4331586619467282712906327)
      ·
        refine ⟨6497379929200924069359491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4331586619467282712906327 6497379929200924069359491)
        ·
          refine ⟨9746069893801386104039237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6497379929200924069359491 9746069893801386104039237)
          ·
            refine ⟨1827388105087759894507357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9746069893801386104039237 1827388105087759894507357)
            ·
              refine ⟨685270539407909960440259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1827388105087759894507357 685270539407909960440259)
              ·
                refine ⟨1027905809111864940660389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685270539407909960440259 1027905809111864940660389)
                ·
                  refine ⟨192732339208474676373823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1027905809111864940660389 192732339208474676373823)
                  ·
                    rfl

theorem cell21_844526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_844526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844526 prefixEnd_844526 := by exact prefixLift 844526
  have htrace : WordTrace (prefixWord ++ tailWord_844526) baseStart_844526 baseEnd_844526 := by
    simpa [prefixWord, tailWord_844526, baseEnd_844526] using wordTrace_append hprefix tailTrace_844526
  have hstable : (prefixWord ++ tailWord_844526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844526).length < 2 ^ (prefixWord ++ tailWord_844526).sum := by decide
  have hdescent : baseEnd_844526 < baseStart_844526 := by decide
  rcases family_descends (prefixWord ++ tailWord_844526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844540 : List Nat := [2, 2, 2, 1, 3, 4, 2, 5]
def baseStart_844540 : Nat := 118140960795 + 844540 * 2 ^ 59
def prefixEnd_844540 : Nat := 4983230072969 + 3 ^ 40 * 844540 * 2
def baseEnd_844540 : Nat := 64245178066404587713487

theorem tailTrace_844540 : CollatzResearch.WordTrace tailWord_844540 prefixEnd_844540 64245178066404587713487 := by
  unfold tailWord_844540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15401452180191645396949537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20535269573588860529266049 15401452180191645396949537)
  ·
    refine ⟨11551089135143734047712153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15401452180191645396949537 11551089135143734047712153)
    ·
      refine ⟨8663316851357800535784115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11551089135143734047712153 8663316851357800535784115)
      ·
        refine ⟨12994975277036700803676173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8663316851357800535784115 12994975277036700803676173)
        ·
          refine ⟨4873115728888762801378565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12994975277036700803676173 4873115728888762801378565)
          ·
            refine ⟨913709199166643025258481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4873115728888762801378565 913709199166643025258481)
            ·
              refine ⟨685281899374982268943861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913709199166643025258481 685281899374982268943861)
              ·
                refine ⟨64245178066404587713487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 685281899374982268943861 64245178066404587713487)
                ·
                  rfl

theorem cell21_844540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 5].length) (baseStart_844540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844540 prefixEnd_844540 := by exact prefixLift 844540
  have htrace : WordTrace (prefixWord ++ tailWord_844540) baseStart_844540 baseEnd_844540 := by
    simpa [prefixWord, tailWord_844540, baseEnd_844540] using wordTrace_append hprefix tailTrace_844540
  have hstable : (prefixWord ++ tailWord_844540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844540).length < 2 ^ (prefixWord ++ tailWord_844540).sum := by decide
  have hdescent : baseEnd_844540 < baseStart_844540 := by decide
  rcases family_descends (prefixWord ++ tailWord_844540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844568 : List Nat := [2, 1, 2, 3, 1, 1, 1, 6, 4]
def baseStart_844568 : Nat := 118140960795 + 844568 * 2 ^ 59
def prefixEnd_844568 : Nat := 4983230072969 + 3 ^ 40 * 844568 * 2
def baseEnd_844568 : Nat := 192741924180691936673737

theorem tailTrace_844568 : CollatzResearch.WordTrace tailWord_844568 prefixEnd_844568 192741924180691936673737 := by
  unfold tailWord_844568
  simp only [CollatzResearch.WordTrace]
  refine ⟨15401962802140925787959179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20535950402854567717278905 15401962802140925787959179)
  ·
    refine ⟨23102944203211388681938769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15401962802140925787959179 23102944203211388681938769)
    ·
      refine ⟨17327208152408541511454077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23102944203211388681938769 17327208152408541511454077)
      ·
        refine ⟨6497703057153203066795279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17327208152408541511454077 6497703057153203066795279)
        ·
          refine ⟨9746554585729804600192919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6497703057153203066795279 9746554585729804600192919)
          ·
            refine ⟨14619831878594706900289379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9746554585729804600192919 14619831878594706900289379)
            ·
              refine ⟨21929747817892060350434069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14619831878594706900289379 21929747817892060350434069)
              ·
                refine ⟨1027956928963690328926597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21929747817892060350434069 1027956928963690328926597)
                ·
                  refine ⟨192741924180691936673737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1027956928963690328926597 192741924180691936673737)
                  ·
                    rfl

theorem cell21_844568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_844568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844568 prefixEnd_844568 := by exact prefixLift 844568
  have htrace : WordTrace (prefixWord ++ tailWord_844568) baseStart_844568 baseEnd_844568 := by
    simpa [prefixWord, tailWord_844568, baseEnd_844568] using wordTrace_append hprefix tailTrace_844568
  have hstable : (prefixWord ++ tailWord_844568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844568).length < 2 ^ (prefixWord ++ tailWord_844568).sum := by decide
  have hdescent : baseEnd_844568 < baseStart_844568 := by decide
  rcases family_descends (prefixWord ++ tailWord_844568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844627 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 6]
def baseStart_844627 : Nat := 118140960795 + 844627 * 2 ^ 59
def prefixEnd_844627 : Nat := 4983230072969 + 3 ^ 40 * 844627 * 2
def baseEnd_844627 : Nat := 192755388784520945190283

theorem tailTrace_844627 : CollatzResearch.WordTrace tailWord_844627 prefixEnd_844627 192755388784520945190283 := by
  unfold tailWord_844627
  simp only [CollatzResearch.WordTrace]
  refine ⟨30806077511068104652316135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20537385007378736434877423 30806077511068104652316135)
  ·
    refine ⟨46209116266602156978474203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30806077511068104652316135 46209116266602156978474203)
    ·
      refine ⟨69313674399903235467711305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46209116266602156978474203 69313674399903235467711305)
      ·
        refine ⟨51985255799927426600783479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69313674399903235467711305 51985255799927426600783479)
        ·
          refine ⟨77977883699891139901175219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51985255799927426600783479 77977883699891139901175219)
          ·
            refine ⟨116966825549836709851762829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77977883699891139901175219 116966825549836709851762829)
            ·
              refine ⟨43862559581188766194411061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116966825549836709851762829 43862559581188766194411061)
              ·
                refine ⟨4112114960736446830726037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43862559581188766194411061 4112114960736446830726037)
                ·
                  refine ⟨192755388784520945190283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4112114960736446830726037 192755388784520945190283)
                  ·
                    rfl

theorem cell21_844627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_844627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844627 prefixEnd_844627 := by exact prefixLift 844627
  have htrace : WordTrace (prefixWord ++ tailWord_844627) baseStart_844627 baseEnd_844627 := by
    simpa [prefixWord, tailWord_844627, baseEnd_844627] using wordTrace_append hprefix tailTrace_844627
  have hstable : (prefixWord ++ tailWord_844627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844627).length < 2 ^ (prefixWord ++ tailWord_844627).sum := by decide
  have hdescent : baseEnd_844627 < baseStart_844627 := by decide
  rcases family_descends (prefixWord ++ tailWord_844627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844658 : List Nat := [3, 2, 1, 2, 1, 1, 2, 9]
def baseStart_844658 : Nat := 118140960795 + 844658 * 2 ^ 59
def prefixEnd_844658 : Nat := 4983230072969 + 3 ^ 40 * 844658 * 2
def baseEnd_844658 : Nat := 64254154468957260057851

theorem tailTrace_844658 : CollatzResearch.WordTrace tailWord_844658 prefixEnd_844658 64254154468957260057851 := by
  unfold tailWord_844658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7701802043488949236673657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20538138782637197964463085 7701802043488949236673657)
  ·
    refine ⟨5776351532616711927505243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7701802043488949236673657 5776351532616711927505243)
    ·
      refine ⟨8664527298925067891257865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5776351532616711927505243 8664527298925067891257865)
      ·
        refine ⟨6498395474193800918443399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8664527298925067891257865 6498395474193800918443399)
        ·
          refine ⟨9747593211290701377665099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6498395474193800918443399 9747593211290701377665099)
          ·
            refine ⟨14621389816936052066497649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9747593211290701377665099 14621389816936052066497649)
            ·
              refine ⟨10966042362702039049873237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14621389816936052066497649 10966042362702039049873237)
              ·
                refine ⟨64254154468957260057851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10966042362702039049873237 64254154468957260057851)
                ·
                  rfl

theorem cell21_844658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_844658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844658 prefixEnd_844658 := by exact prefixLift 844658
  have htrace : WordTrace (prefixWord ++ tailWord_844658) baseStart_844658 baseEnd_844658 := by
    simpa [prefixWord, tailWord_844658, baseEnd_844658] using wordTrace_append hprefix tailTrace_844658
  have hstable : (prefixWord ++ tailWord_844658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844658).length < 2 ^ (prefixWord ++ tailWord_844658).sum := by decide
  have hdescent : baseEnd_844658 < baseStart_844658 := by decide
  rcases family_descends (prefixWord ++ tailWord_844658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844706 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_844706 : Nat := 118140960795 + 844706 * 2 ^ 59
def prefixEnd_844706 : Nat := 4983230072969 + 3 ^ 40 * 844706 * 2
def baseEnd_844706 : Nat := 192773417660834363373455

theorem tailTrace_844706 : CollatzResearch.WordTrace tailWord_844706 prefixEnd_844706 192773417660834363373455 := by
  unfold tailWord_844706
  simp only [CollatzResearch.WordTrace]
  refine ⟨7702239719445475286110493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20539305918521267429627981 7702239719445475286110493)
  ·
    refine ⟨2888339894792053232291435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7702239719445475286110493 2888339894792053232291435)
    ·
      refine ⟨4332509842188079848437153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2888339894792053232291435 4332509842188079848437153)
      ·
        refine ⟨3249382381641059886327865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4332509842188079848437153 3249382381641059886327865)
        ·
          refine ⟨2437036786230794914745899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3249382381641059886327865 2437036786230794914745899)
          ·
            refine ⟨3655555179346192372118849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437036786230794914745899 3655555179346192372118849)
            ·
              refine ⟨2741666384509644279089137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3655555179346192372118849 2741666384509644279089137)
              ·
                refine ⟨2056249788382233209316853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2741666384509644279089137 2056249788382233209316853)
                ·
                  refine ⟨192773417660834363373455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2056249788382233209316853 192773417660834363373455)
                  ·
                    rfl

theorem cell21_844706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_844706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844706 prefixEnd_844706 := by exact prefixLift 844706
  have htrace : WordTrace (prefixWord ++ tailWord_844706) baseStart_844706 baseEnd_844706 := by
    simpa [prefixWord, tailWord_844706, baseEnd_844706] using wordTrace_append hprefix tailTrace_844706
  have hstable : (prefixWord ++ tailWord_844706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844706).length < 2 ^ (prefixWord ++ tailWord_844706).sum := by decide
  have hdescent : baseEnd_844706 < baseStart_844706 := by decide
  rcases family_descends (prefixWord ++ tailWord_844706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844726 : List Nat := [5, 1, 4, 1, 1, 2, 7]
def baseStart_844726 : Nat := 118140960795 + 844726 * 2 ^ 59
def prefixEnd_844726 : Nat := 4983230072969 + 3 ^ 40 * 844726 * 2
def baseEnd_844726 : Nat := 21419775770368752560009

theorem tailTrace_844726 : CollatzResearch.WordTrace tailWord_844726 prefixEnd_844726 21419775770368752560009 := by
  unfold tailWord_844726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1925605521106840285010627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20539792225139629706780021 1925605521106840285010627)
  ·
    refine ⟨2888408281660260427515941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1925605521106840285010627 2888408281660260427515941)
    ·
      refine ⟨541576552811298830159239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2888408281660260427515941 541576552811298830159239)
      ·
        refine ⟨812364829216948245238859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541576552811298830159239 812364829216948245238859)
        ·
          refine ⟨1218547243825422367858289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812364829216948245238859 1218547243825422367858289)
          ·
            refine ⟨913910432869066775893717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218547243825422367858289 913910432869066775893717)
            ·
              refine ⟨21419775770368752560009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 913910432869066775893717 21419775770368752560009)
              ·
                rfl

theorem cell21_844726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 7].length) (baseStart_844726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844726 prefixEnd_844726 := by exact prefixLift 844726
  have htrace : WordTrace (prefixWord ++ tailWord_844726) baseStart_844726 baseEnd_844726 := by
    simpa [prefixWord, tailWord_844726, baseEnd_844726] using wordTrace_append hprefix tailTrace_844726
  have hstable : (prefixWord ++ tailWord_844726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844726).length < 2 ^ (prefixWord ++ tailWord_844726).sum := by decide
  have hdescent : baseEnd_844726 < baseStart_844726 := by decide
  rcases family_descends (prefixWord ++ tailWord_844726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844740 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 5]
def baseStart_844740 : Nat := 118140960795 + 844740 * 2 ^ 59
def prefixEnd_844740 : Nat := 4983230072969 + 3 ^ 40 * 844740 * 2
def baseEnd_844740 : Nat := 192781176924057859806719

theorem tailTrace_844740 : CollatzResearch.WordTrace tailWord_844740 prefixEnd_844740 192781176924057859806719 := by
  unfold tailWord_844740
  simp only [CollatzResearch.WordTrace]
  refine ⟨15405099479829362475589837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20540132639772483300786449 15405099479829362475589837)
  ·
    refine ⟨5776912304936010928346189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15405099479829362475589837 5776912304936010928346189)
    ·
      refine ⟨2166342114351004098129821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5776912304936010928346189 2166342114351004098129821)
      ·
        refine ⟨812378292881626536798683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2166342114351004098129821 812378292881626536798683)
        ·
          refine ⟨1218567439322439805198025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812378292881626536798683 1218567439322439805198025)
          ·
            refine ⟨913925579491829853898519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218567439322439805198025 913925579491829853898519)
            ·
              refine ⟨1370888369237744780847779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913925579491829853898519 1370888369237744780847779)
              ·
                refine ⟨2056332553856617171271669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370888369237744780847779 2056332553856617171271669)
                ·
                  refine ⟨192781176924057859806719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2056332553856617171271669 192781176924057859806719)
                  ·
                    rfl

theorem cell21_844740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_844740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844740 prefixEnd_844740 := by exact prefixLift 844740
  have htrace : WordTrace (prefixWord ++ tailWord_844740) baseStart_844740 baseEnd_844740 := by
    simpa [prefixWord, tailWord_844740, baseEnd_844740] using wordTrace_append hprefix tailTrace_844740
  have hstable : (prefixWord ++ tailWord_844740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844740).length < 2 ^ (prefixWord ++ tailWord_844740).sum := by decide
  have hdescent : baseEnd_844740 < baseStart_844740 := by decide
  rcases family_descends (prefixWord ++ tailWord_844740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844754 : List Nat := [3, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_844754 : Nat := 118140960795 + 844754 * 2 ^ 59
def prefixEnd_844754 : Nat := 4983230072969 + 3 ^ 40 * 844754 * 2
def baseEnd_844754 : Nat := 192784371914796946573357

theorem tailTrace_844754 : CollatzResearch.WordTrace tailWord_844754 prefixEnd_844754 192784371914796946573357 := by
  unfold tailWord_844754
  simp only [CollatzResearch.WordTrace]
  refine ⟨7702677395402001335547329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20540473054405336894792877 7702677395402001335547329)
  ·
    refine ⟨5777008046551501001660497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7702677395402001335547329 5777008046551501001660497)
    ·
      refine ⟨4332756034913625751245373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5777008046551501001660497 4332756034913625751245373)
      ·
        refine ⟨1624783513092609656717015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4332756034913625751245373 1624783513092609656717015)
        ·
          refine ⟨2437175269638914485075523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624783513092609656717015 2437175269638914485075523)
          ·
            refine ⟨3655762904458371727613285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437175269638914485075523 3655762904458371727613285)
            ·
              refine ⟨685455544585944698927491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3655762904458371727613285 685455544585944698927491)
              ·
                refine ⟨1028183316878917048391237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685455544585944698927491 1028183316878917048391237)
                ·
                  refine ⟨192784371914796946573357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028183316878917048391237 192784371914796946573357)
                  ·
                    rfl

theorem cell21_844754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_844754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844754 prefixEnd_844754 := by exact prefixLift 844754
  have htrace : WordTrace (prefixWord ++ tailWord_844754) baseStart_844754 baseEnd_844754 := by
    simpa [prefixWord, tailWord_844754, baseEnd_844754] using wordTrace_append hprefix tailTrace_844754
  have hstable : (prefixWord ++ tailWord_844754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844754).length < 2 ^ (prefixWord ++ tailWord_844754).sum := by decide
  have hdescent : baseEnd_844754 < baseStart_844754 := by decide
  rcases family_descends (prefixWord ++ tailWord_844754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844796 : List Nat := [2, 2, 2, 1, 2, 3, 1, 4, 4]
def baseStart_844796 : Nat := 118140960795 + 844796 * 2 ^ 59
def prefixEnd_844796 : Nat := 4983230072969 + 3 ^ 40 * 844796 * 2
def baseEnd_844796 : Nat := 192793956887014206873271

theorem tailTrace_844796 : CollatzResearch.WordTrace tailWord_844796 prefixEnd_844796 192793956887014206873271 := by
  unfold tailWord_844796
  simp only [CollatzResearch.WordTrace]
  refine ⟨15406120723727923257609121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20541494298303897676812161 15406120723727923257609121)
  ·
    refine ⟨11554590542795942443206841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15406120723727923257609121 11554590542795942443206841)
    ·
      refine ⟨8665942907096956832405131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11554590542795942443206841 8665942907096956832405131)
      ·
        refine ⟨12998914360645435248607697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8665942907096956832405131 12998914360645435248607697)
        ·
          refine ⟨9749185770484076436455773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12998914360645435248607697 9749185770484076436455773)
          ·
            refine ⟨3655944663931528663670915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9749185770484076436455773 3655944663931528663670915)
            ·
              refine ⟨5483916995897292995506373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655944663931528663670915 5483916995897292995506373)
              ·
                refine ⟨1028234436730742436657445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5483916995897292995506373 1028234436730742436657445)
                ·
                  refine ⟨192793956887014206873271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028234436730742436657445 192793956887014206873271)
                  ·
                    rfl

theorem cell21_844796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_844796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844796 prefixEnd_844796 := by exact prefixLift 844796
  have htrace : WordTrace (prefixWord ++ tailWord_844796) baseStart_844796 baseEnd_844796 := by
    simpa [prefixWord, tailWord_844796, baseEnd_844796] using wordTrace_append hprefix tailTrace_844796
  have hstable : (prefixWord ++ tailWord_844796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844796).length < 2 ^ (prefixWord ++ tailWord_844796).sum := by decide
  have hdescent : baseEnd_844796 < baseStart_844796 := by decide
  rcases family_descends (prefixWord ++ tailWord_844796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844802 : List Nat := [3, 4, 1, 3, 2, 1, 1, 6]
def baseStart_844802 : Nat := 118140960795 + 844802 * 2 ^ 59
def prefixEnd_844802 : Nat := 4983230072969 + 3 ^ 40 * 844802 * 2
def baseEnd_844802 : Nat := 64265108722919843257753

theorem tailTrace_844802 : CollatzResearch.WordTrace tailWord_844802 prefixEnd_844802 64265108722919843257753 := by
  unfold tailWord_844802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7703115071358527384984165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20541640190289406359957773 7703115071358527384984165)
  ·
    refine ⟨1444334075879723884684531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7703115071358527384984165 1444334075879723884684531)
    ·
      refine ⟨2166501113819585827026797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1444334075879723884684531 2166501113819585827026797)
      ·
        refine ⟨812437917682344685135049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2166501113819585827026797 812437917682344685135049)
        ·
          refine ⟨609328438261758513851287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812437917682344685135049 609328438261758513851287)
          ·
            refine ⟨913992657392637770776931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609328438261758513851287 913992657392637770776931)
            ·
              refine ⟨1370988986088956656165397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913992657392637770776931 1370988986088956656165397)
              ·
                refine ⟨64265108722919843257753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1370988986088956656165397 64265108722919843257753)
                ·
                  rfl

theorem cell21_844802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_844802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844802 prefixEnd_844802 := by exact prefixLift 844802
  have htrace : WordTrace (prefixWord ++ tailWord_844802) baseStart_844802 baseEnd_844802 := by
    simpa [prefixWord, tailWord_844802, baseEnd_844802] using wordTrace_append hprefix tailTrace_844802
  have hstable : (prefixWord ++ tailWord_844802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844802).length < 2 ^ (prefixWord ++ tailWord_844802).sum := by decide
  have hdescent : baseEnd_844802 < baseStart_844802 := by decide
  rcases family_descends (prefixWord ++ tailWord_844802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844858 : List Nat := [3, 1, 1, 1, 3, 1, 4, 4, 3]
def baseStart_844858 : Nat := 118140960795 + 844858 * 2 ^ 59
def prefixEnd_844858 : Nat := 4983230072969 + 3 ^ 40 * 844858 * 2
def baseEnd_844858 : Nat := 192808106131715876839811

theorem tailTrace_844858 : CollatzResearch.WordTrace tailWord_844858 prefixEnd_844858 192808106131715876839811 := by
  unfold tailWord_844858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7703625693307807775993807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20543001848820820735983485 7703625693307807775993807)
  ·
    refine ⟨11555438539961711663990711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7703625693307807775993807 11555438539961711663990711)
    ·
      refine ⟨17333157809942567495986067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11555438539961711663990711 17333157809942567495986067)
      ·
        refine ⟨25999736714913851243979101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17333157809942567495986067 25999736714913851243979101)
        ·
          refine ⟨9749901268092694216492163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25999736714913851243979101 9749901268092694216492163)
          ·
            refine ⟨14624851902139041324738245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9749901268092694216492163 14624851902139041324738245)
            ·
              refine ⟨2742159731651070248388421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14624851902139041324738245 2742159731651070248388421)
              ·
                refine ⟨514154949684575671572829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2742159731651070248388421 514154949684575671572829)
                ·
                  refine ⟨192808106131715876839811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514154949684575671572829 192808106131715876839811)
                  ·
                    rfl

theorem cell21_844858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_844858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844858 prefixEnd_844858 := by exact prefixLift 844858
  have htrace : WordTrace (prefixWord ++ tailWord_844858) baseStart_844858 baseEnd_844858 := by
    simpa [prefixWord, tailWord_844858, baseEnd_844858] using wordTrace_append hprefix tailTrace_844858
  have hstable : (prefixWord ++ tailWord_844858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844858).length < 2 ^ (prefixWord ++ tailWord_844858).sum := by decide
  have hdescent : baseEnd_844858 < baseStart_844858 := by decide
  rcases family_descends (prefixWord ++ tailWord_844858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844962 : List Nat := [3, 3, 1, 3, 11]
def baseStart_844962 : Nat := 118140960795 + 844962 * 2 ^ 59
def prefixEnd_844962 : Nat := 4983230072969 + 3 ^ 40 * 844962 * 2
def baseEnd_844962 : Nat := 2380640004304133421065

theorem tailTrace_844962 : CollatzResearch.WordTrace tailWord_844962 prefixEnd_844962 2380640004304133421065 := by
  unfold tailWord_844962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7704573991213614216440285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20545530643236304577174093 7704573991213614216440285)
  ·
    refine ⟨2889215246705105331165107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7704573991213614216440285 2889215246705105331165107)
    ·
      refine ⟨4333822870057657996747661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2889215246705105331165107 4333822870057657996747661)
      ·
        refine ⟨1625183576271621748780373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4333822870057657996747661 1625183576271621748780373)
        ·
          refine ⟨2380640004304133421065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1625183576271621748780373 2380640004304133421065)
          ·
            rfl

theorem cell21_844962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 11].length) (baseStart_844962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844962 prefixEnd_844962 := by exact prefixLift 844962
  have htrace : WordTrace (prefixWord ++ tailWord_844962) baseStart_844962 baseEnd_844962 := by
    simpa [prefixWord, tailWord_844962, baseEnd_844962] using wordTrace_append hprefix tailTrace_844962
  have hstable : (prefixWord ++ tailWord_844962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844962).length < 2 ^ (prefixWord ++ tailWord_844962).sum := by decide
  have hdescent : baseEnd_844962 < baseStart_844962 := by decide
  rcases family_descends (prefixWord ++ tailWord_844962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844996 : List Nat := [2, 3, 3, 1, 3, 1, 3, 5]
def baseStart_844996 : Nat := 118140960795 + 844996 * 2 ^ 59
def prefixEnd_844996 : Nat := 4983230072969 + 3 ^ 40 * 844996 * 2
def baseEnd_844996 : Nat := 64279866537286101179843

theorem tailTrace_844996 : CollatzResearch.WordTrace tailWord_844996 prefixEnd_844996 64279866537286101179843 := by
  unfold tailWord_844996
  simp only [CollatzResearch.WordTrace]
  refine ⟨15409768023365640336249421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20546357364487520448332561 15409768023365640336249421)
  ·
    refine ⟨5778663008762115126093533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15409768023365640336249421 5778663008762115126093533)
    ·
      refine ⟨2166998628285793172285075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5778663008762115126093533 2166998628285793172285075)
      ·
        refine ⟨3250497942428689758427613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2166998628285793172285075 3250497942428689758427613)
        ·
          refine ⟨1218936728410758659410355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3250497942428689758427613 1218936728410758659410355)
          ·
            refine ⟨1828405092616137989115533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218936728410758659410355 1828405092616137989115533)
            ·
              refine ⟨685651909731051745918325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1828405092616137989115533 685651909731051745918325)
              ·
                refine ⟨64279866537286101179843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 685651909731051745918325 64279866537286101179843)
                ·
                  rfl

theorem cell21_844996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 5].length) (baseStart_844996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_844996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_844996 prefixEnd_844996 := by exact prefixLift 844996
  have htrace : WordTrace (prefixWord ++ tailWord_844996) baseStart_844996 baseEnd_844996 := by
    simpa [prefixWord, tailWord_844996, baseEnd_844996] using wordTrace_append hprefix tailTrace_844996
  have hstable : (prefixWord ++ tailWord_844996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844996).length < 2 ^ (prefixWord ++ tailWord_844996).sum := by decide
  have hdescent : baseEnd_844996 < baseStart_844996 := by decide
  rcases family_descends (prefixWord ++ tailWord_844996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845024 : List Nat := [2, 1, 1, 3, 1, 4, 3, 2, 4]
def baseStart_845024 : Nat := 118140960795 + 845024 * 2 ^ 59
def prefixEnd_845024 : Nat := 4983230072969 + 3 ^ 40 * 845024 * 2
def baseEnd_845024 : Nat := 192845989593336477072805

theorem tailTrace_845024 : CollatzResearch.WordTrace tailWord_845024 prefixEnd_845024 192845989593336477072805 := by
  unfold tailWord_845024
  simp only [CollatzResearch.WordTrace]
  refine ⟨15410278645314920727259063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20547038193753227636345417 15410278645314920727259063)
  ·
    refine ⟨23115417967972381090888595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15410278645314920727259063 23115417967972381090888595)
    ·
      refine ⟨34673126951958571636332893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23115417967972381090888595 34673126951958571636332893)
      ·
        refine ⟨13002422606984464363624835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34673126951958571636332893 13002422606984464363624835)
        ·
          refine ⟨19503633910476696545437253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13002422606984464363624835 19503633910476696545437253)
          ·
            refine ⟨3656931358214380602269485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19503633910476696545437253 3656931358214380602269485)
            ·
              refine ⟨1371349259330392725851057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3656931358214380602269485 1371349259330392725851057)
              ·
                refine ⟨1028511944497794544388293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371349259330392725851057 1028511944497794544388293)
                ·
                  refine ⟨192845989593336477072805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028511944497794544388293 192845989593336477072805)
                  ·
                    rfl

theorem cell21_845024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_845024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_845024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_845024 prefixEnd_845024 := by exact prefixLift 845024
  have htrace : WordTrace (prefixWord ++ tailWord_845024) baseStart_845024 baseEnd_845024 := by
    simpa [prefixWord, tailWord_845024, baseEnd_845024] using wordTrace_append hprefix tailTrace_845024
  have hstable : (prefixWord ++ tailWord_845024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845024).length < 2 ^ (prefixWord ++ tailWord_845024).sum := by decide
  have hdescent : baseEnd_845024 < baseStart_845024 := by decide
  rcases family_descends (prefixWord ++ tailWord_845024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845055 : List Nat := [1, 1, 2, 2, 1, 7, 2, 5]
def baseStart_845055 : Nat := 118140960795 + 845055 * 2 ^ 59
def prefixEnd_845055 : Nat := 4983230072969 + 3 ^ 40 * 845055 * 2
def baseEnd_845055 : Nat := 64284354738562437352025

theorem tailTrace_845055 : CollatzResearch.WordTrace tailWord_845055 prefixEnd_845055 64284354738562437352025 := by
  unfold tailWord_845055
  simp only [CollatzResearch.WordTrace]
  refine ⟨30821687953517533748896619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20547791969011689165931079 30821687953517533748896619)
  ·
    refine ⟨46232531930276300623344929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30821687953517533748896619 46232531930276300623344929)
    ·
      refine ⟨34674398947707225467508697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46232531930276300623344929 34674398947707225467508697)
      ·
        refine ⟨26005799210780419100631523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34674398947707225467508697 26005799210780419100631523)
        ·
          refine ⟨39008698816170628650947285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26005799210780419100631523 39008698816170628650947285)
          ·
            refine ⟨914266378503999109006577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 39008698816170628650947285 914266378503999109006577)
            ·
              refine ⟨685699783877999331754933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914266378503999109006577 685699783877999331754933)
              ·
                refine ⟨64284354738562437352025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 685699783877999331754933 64284354738562437352025)
                ·
                  rfl

theorem cell21_845055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 5].length) (baseStart_845055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_845055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_845055 prefixEnd_845055 := by exact prefixLift 845055
  have htrace : WordTrace (prefixWord ++ tailWord_845055) baseStart_845055 baseEnd_845055 := by
    simpa [prefixWord, tailWord_845055, baseEnd_845055] using wordTrace_append hprefix tailTrace_845055
  have hstable : (prefixWord ++ tailWord_845055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845055).length < 2 ^ (prefixWord ++ tailWord_845055).sum := by decide
  have hdescent : baseEnd_845055 < baseStart_845055 := by decide
  rcases family_descends (prefixWord ++ tailWord_845055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845083 : List Nat := [1, 1, 1, 1, 1, 1, 5, 6, 4]
def baseStart_845083 : Nat := 118140960795 + 845083 * 2 ^ 59
def prefixEnd_845083 : Nat := 4983230072969 + 3 ^ 40 * 845083 * 2
def baseEnd_845083 : Nat := 192859454197165485589351

theorem tailTrace_845083 : CollatzResearch.WordTrace tailWord_845083 prefixEnd_845083 192859454197165485589351 := by
  unfold tailWord_845083
  simp only [CollatzResearch.WordTrace]
  refine ⟨30822709197416094530915903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20548472798277396353943935 30822709197416094530915903)
  ·
    refine ⟨46234063796124141796373855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30822709197416094530915903 46234063796124141796373855)
    ·
      refine ⟨69351095694186212694560783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46234063796124141796373855 69351095694186212694560783)
      ·
        refine ⟨104026643541279319041841175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69351095694186212694560783 104026643541279319041841175)
        ·
          refine ⟨156039965311918978562761763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104026643541279319041841175 156039965311918978562761763)
          ·
            refine ⟨234059947967878467844142645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156039965311918978562761763 234059947967878467844142645)
            ·
              refine ⟨21943120121988606360388373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 234059947967878467844142645 21943120121988606360388373)
              ·
                refine ⟨1028583755718215923143205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21943120121988606360388373 1028583755718215923143205)
                ·
                  refine ⟨192859454197165485589351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028583755718215923143205 192859454197165485589351)
                  ·
                    rfl

theorem cell21_845083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 4].length) (baseStart_845083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_845083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_845083 prefixEnd_845083 := by exact prefixLift 845083
  have htrace : WordTrace (prefixWord ++ tailWord_845083) baseStart_845083 baseEnd_845083 := by
    simpa [prefixWord, tailWord_845083, baseEnd_845083] using wordTrace_append hprefix tailTrace_845083
  have hstable : (prefixWord ++ tailWord_845083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845083).length < 2 ^ (prefixWord ++ tailWord_845083).sum := by decide
  have hdescent : baseEnd_845083 < baseStart_845083 := by decide
  rcases family_descends (prefixWord ++ tailWord_845083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845162 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_845162 : Nat := 118140960795 + 845162 * 2 ^ 59
def prefixEnd_845162 : Nat := 4983230072969 + 3 ^ 40 * 845162 * 2
def baseEnd_845162 : Nat := 192877483073478903772523

theorem tailTrace_845162 : CollatzResearch.WordTrace tailWord_845162 prefixEnd_845162 192877483073478903772523 := by
  unfold tailWord_845162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7706397641032472755760435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20550393709419927348694493 7706397641032472755760435)
  ·
    refine ⟨11559596461548709133640653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7706397641032472755760435 11559596461548709133640653)
    ·
      refine ⟨4334848673080765925115245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11559596461548709133640653 4334848673080765925115245)
      ·
        refine ⟨1625568252405287221918217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4334848673080765925115245 1625568252405287221918217)
        ·
          refine ⟨1219176189303965416438663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1625568252405287221918217 1219176189303965416438663)
          ·
            refine ⟨1828764283955948124657995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219176189303965416438663 1828764283955948124657995)
            ·
              refine ⟨2743146425933922186986993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828764283955948124657995 2743146425933922186986993)
              ·
                refine ⟨2057359819450441640240245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2743146425933922186986993 2057359819450441640240245)
                ·
                  refine ⟨192877483073478903772523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2057359819450441640240245 192877483073478903772523)
                  ·
                    rfl

theorem cell21_845162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_845162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_845162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_845162 prefixEnd_845162 := by exact prefixLift 845162
  have htrace : WordTrace (prefixWord ++ tailWord_845162) baseStart_845162 baseEnd_845162 := by
    simpa [prefixWord, tailWord_845162, baseEnd_845162] using wordTrace_append hprefix tailTrace_845162
  have hstable : (prefixWord ++ tailWord_845162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845162).length < 2 ^ (prefixWord ++ tailWord_845162).sum := by decide
  have hdescent : baseEnd_845162 < baseStart_845162 := by decide
  rcases family_descends (prefixWord ++ tailWord_845162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845193 : List Nat := [1, 2, 1, 1, 7, 2, 1, 2, 4]
def baseStart_845193 : Nat := 118140960795 + 845193 * 2 ^ 59
def prefixEnd_845193 : Nat := 4983230072969 + 3 ^ 40 * 845193 * 2
def baseEnd_845193 : Nat := 192884557695829738755793

theorem tailTrace_845193 : CollatzResearch.WordTrace tailWord_845193 prefixEnd_845193 192884557695829738755793 := by
  unfold tailWord_845193
  simp only [CollatzResearch.WordTrace]
  refine ⟨30826721227017583317420233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20551147484678388878280155 30826721227017583317420233)
  ·
    refine ⟨23120040920263187488065175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30826721227017583317420233 23120040920263187488065175)
    ·
      refine ⟨34680061380394781232097763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23120040920263187488065175 34680061380394781232097763)
      ·
        refine ⟨52020092070592171848146645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34680061380394781232097763 52020092070592171848146645)
        ·
          refine ⟨1219220907904504027690937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 52020092070592171848146645 1219220907904504027690937)
          ·
            refine ⟨914415680928378020768203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219220907904504027690937 914415680928378020768203)
            ·
              refine ⟨1371623521392567031152305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914415680928378020768203 1371623521392567031152305)
              ·
                refine ⟨1028717641044425273364229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371623521392567031152305 1028717641044425273364229)
                ·
                  refine ⟨192884557695829738755793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028717641044425273364229 192884557695829738755793)
                  ·
                    rfl

theorem cell21_845193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_845193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_845193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_845193 prefixEnd_845193 := by exact prefixLift 845193
  have htrace : WordTrace (prefixWord ++ tailWord_845193) baseStart_845193 baseEnd_845193 := by
    simpa [prefixWord, tailWord_845193, baseEnd_845193] using wordTrace_append hprefix tailTrace_845193
  have hstable : (prefixWord ++ tailWord_845193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845193).length < 2 ^ (prefixWord ++ tailWord_845193).sum := by decide
  have hdescent : baseEnd_845193 < baseStart_845193 := by decide
  rcases family_descends (prefixWord ++ tailWord_845193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845252 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 6]
def baseStart_845252 : Nat := 118140960795 + 845252 * 2 ^ 59
def prefixEnd_845252 : Nat := 4983230072969 + 3 ^ 40 * 845252 * 2
def baseEnd_845252 : Nat := 192898022299658747272339

theorem tailTrace_845252 : CollatzResearch.WordTrace tailWord_845252 prefixEnd_845252 192898022299658747272339 := by
  unfold tailWord_845252
  simp only [CollatzResearch.WordTrace]
  refine ⟨15414436566901918196909005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20552582089202557595878673 15414436566901918196909005)
  ·
    refine ⟨5780413712588219323840877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15414436566901918196909005 5780413712588219323840877)
    ·
      refine ⟨2167655142220582246440329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5780413712588219323840877 2167655142220582246440329)
      ·
        refine ⟨1625741356665436684830247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2167655142220582246440329 1625741356665436684830247)
        ·
          refine ⟨2438612034998155027245371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1625741356665436684830247 2438612034998155027245371)
          ·
            refine ⟨3657918052497232540868057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438612034998155027245371 3657918052497232540868057)
            ·
              refine ⟨2743438539372924405651043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3657918052497232540868057 2743438539372924405651043)
              ·
                refine ⟨4115157809059386608476565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743438539372924405651043 4115157809059386608476565)
                ·
                  refine ⟨192898022299658747272339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4115157809059386608476565 192898022299658747272339)
                  ·
                    rfl

theorem cell21_845252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_845252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_845252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_845252 prefixEnd_845252 := by exact prefixLift 845252
  have htrace : WordTrace (prefixWord ++ tailWord_845252) baseStart_845252 baseEnd_845252 := by
    simpa [prefixWord, tailWord_845252, baseEnd_845252] using wordTrace_append hprefix tailTrace_845252
  have hstable : (prefixWord ++ tailWord_845252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845252).length < 2 ^ (prefixWord ++ tailWord_845252).sum := by decide
  have hdescent : baseEnd_845252 < baseStart_845252 := by decide
  rcases family_descends (prefixWord ++ tailWord_845252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845418 : List Nat := [3, 1, 3, 2, 1, 4, 7]
def baseStart_845418 : Nat := 118140960795 + 845418 * 2 ^ 59
def prefixEnd_845418 : Nat := 4983230072969 + 3 ^ 40 * 845418 * 2
def baseEnd_845418 : Nat := 21437322862364371945037

theorem tailTrace_845418 : CollatzResearch.WordTrace tailWord_845418 prefixEnd_845418 21437322862364371945037 := by
  unfold tailWord_845418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7708731912800611686090227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20556618434134964496240605 7708731912800611686090227)
  ·
    refine ⟨11563097869200917529135341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7708731912800611686090227 11563097869200917529135341)
    ·
      refine ⟨4336161700950344073425753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11563097869200917529135341 4336161700950344073425753)
      ·
        refine ⟨3252121275712758055069315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4336161700950344073425753 3252121275712758055069315)
        ·
          refine ⟨4878181913569137082603973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3252121275712758055069315 4878181913569137082603973)
          ·
            refine ⟨914659108794213202988245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4878181913569137082603973 914659108794213202988245)
            ·
              refine ⟨21437322862364371945037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 914659108794213202988245 21437322862364371945037)
              ·
                rfl

theorem cell21_845418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 7].length) (baseStart_845418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_845418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_845418 prefixEnd_845418 := by exact prefixLift 845418
  have htrace : WordTrace (prefixWord ++ tailWord_845418) baseStart_845418 baseEnd_845418 := by
    simpa [prefixWord, tailWord_845418, baseEnd_845418] using wordTrace_append hprefix tailTrace_845418
  have hstable : (prefixWord ++ tailWord_845418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845418).length < 2 ^ (prefixWord ++ tailWord_845418).sum := by decide
  have hdescent : baseEnd_845418 < baseStart_845418 := by decide
  rcases family_descends (prefixWord ++ tailWord_845418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845570 : List Nat := [3, 4, 1, 1, 1, 1, 3, 7]
def baseStart_845570 : Nat := 118140960795 + 845570 * 2 ^ 59
def prefixEnd_845570 : Nat := 4983230072969 + 3 ^ 40 * 845570 * 2
def baseEnd_845570 : Nat := 64323531410720286990563

theorem tailTrace_845570 : CollatzResearch.WordTrace tailWord_845570 prefixEnd_845570 64323531410720286990563 := by
  unfold tailWord_845570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7710117886662944175973541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20560314364434517802596109 7710117886662944175973541)
  ·
    refine ⟨1445647103749302032995039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7710117886662944175973541 1445647103749302032995039)
    ·
      refine ⟨2168470655623953049492559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1445647103749302032995039 2168470655623953049492559)
      ·
        refine ⟨3252705983435929574238839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2168470655623953049492559 3252705983435929574238839)
        ·
          refine ⟨4879058975153894361358259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3252705983435929574238839 4879058975153894361358259)
          ·
            refine ⟨7318588462730841542037389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879058975153894361358259 7318588462730841542037389)
            ·
              refine ⟨2744470673524065578264021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7318588462730841542037389 2744470673524065578264021)
              ·
                refine ⟨64323531410720286990563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2744470673524065578264021 64323531410720286990563)
                ·
                  rfl

theorem cell21_845570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_845570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_845570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_845570 prefixEnd_845570 := by exact prefixLift 845570
  have htrace : WordTrace (prefixWord ++ tailWord_845570) baseStart_845570 baseEnd_845570 := by
    simpa [prefixWord, tailWord_845570, baseEnd_845570] using wordTrace_append hprefix tailTrace_845570
  have hstable : (prefixWord ++ tailWord_845570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845570).length < 2 ^ (prefixWord ++ tailWord_845570).sum := by decide
  have hdescent : baseEnd_845570 < baseStart_845570 := by decide
  rcases family_descends (prefixWord ++ tailWord_845570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845601 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 5]
def baseStart_845601 : Nat := 118140960795 + 845601 * 2 ^ 59
def prefixEnd_845601 : Nat := 4983230072969 + 3 ^ 40 * 845601 * 2
def baseEnd_845601 : Nat := 192977668854511695954959

theorem tailTrace_845601 : CollatzResearch.WordTrace tailWord_845601 prefixEnd_845601 192977668854511695954959 := by
  unfold tailWord_845601
  simp only [CollatzResearch.WordTrace]
  refine ⟨30841602209539468998272657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20561068139692979332181771 30841602209539468998272657)
  ·
    refine ⟨23131201657154601748704493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30841602209539468998272657 23131201657154601748704493)
    ·
      refine ⟨8674200621432975655764185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23131201657154601748704493 8674200621432975655764185)
      ·
        refine ⟨6505650466074731741823139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8674200621432975655764185 6505650466074731741823139)
        ·
          refine ⟨9758475699112097612734709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6505650466074731741823139 9758475699112097612734709)
          ·
            refine ⟨914857096791759151193879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9758475699112097612734709 914857096791759151193879)
            ·
              refine ⟨1372285645187638726790819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914857096791759151193879 1372285645187638726790819)
              ·
                refine ⟨2058428467781458090186229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372285645187638726790819 2058428467781458090186229)
                ·
                  refine ⟨192977668854511695954959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2058428467781458090186229 192977668854511695954959)
                  ·
                    rfl

theorem cell21_845601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_845601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_845601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_845601 prefixEnd_845601 := by exact prefixLift 845601
  have htrace : WordTrace (prefixWord ++ tailWord_845601) baseStart_845601 baseEnd_845601 := by
    simpa [prefixWord, tailWord_845601, baseEnd_845601] using wordTrace_append hprefix tailTrace_845601
  have hstable : (prefixWord ++ tailWord_845601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845601).length < 2 ^ (prefixWord ++ tailWord_845601).sum := by decide
  have hdescent : baseEnd_845601 < baseStart_845601 := by decide
  rcases family_descends (prefixWord ++ tailWord_845601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845781 : List Nat := [1, 3, 2, 3, 2, 1, 1, 8]
def baseStart_845781 : Nat := 118140960795 + 845781 * 2 ^ 59
def prefixEnd_845781 : Nat := 4983230072969 + 3 ^ 40 * 845781 * 2
def baseEnd_845781 : Nat := 64339582435623794318197

theorem tailTrace_845781 : CollatzResearch.WordTrace tailWord_845781 prefixEnd_845781 64339582435623794318197 := by
  unfold tailWord_845781
  simp only [CollatzResearch.WordTrace]
  refine ⟨30848167348887359739825197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20565444899258239826550131 30848167348887359739825197)
  ·
    refine ⟨11568062755832759902434449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30848167348887359739825197 11568062755832759902434449)
    ·
      refine ⟨8676047066874569926825837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11568062755832759902434449 8676047066874569926825837)
      ·
        refine ⟨3253517650077963722559689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8676047066874569926825837 3253517650077963722559689)
        ·
          refine ⟨2440138237558472791919767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3253517650077963722559689 2440138237558472791919767)
          ·
            refine ⟨3660207356337709187879651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440138237558472791919767 3660207356337709187879651)
            ·
              refine ⟨5490311034506563781819477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3660207356337709187879651 5490311034506563781819477)
              ·
                refine ⟨64339582435623794318197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5490311034506563781819477 64339582435623794318197)
                ·
                  rfl

theorem cell21_845781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 8].length) (baseStart_845781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_845781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_845781 prefixEnd_845781 := by exact prefixLift 845781
  have htrace : WordTrace (prefixWord ++ tailWord_845781) baseStart_845781 baseEnd_845781 := by
    simpa [prefixWord, tailWord_845781, baseEnd_845781] using wordTrace_append hprefix tailTrace_845781
  have hstable : (prefixWord ++ tailWord_845781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845781).length < 2 ^ (prefixWord ++ tailWord_845781).sum := by decide
  have hdescent : baseEnd_845781 < baseStart_845781 := by decide
  rcases family_descends (prefixWord ++ tailWord_845781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845829 : List Nat := [1, 3, 1, 1, 2, 5, 1, 4, 3]
def baseStart_845829 : Nat := 118140960795 + 845829 * 2 ^ 59
def prefixEnd_845829 : Nat := 4983230072969 + 3 ^ 40 * 845829 * 2
def baseEnd_845829 : Nat := 193029701560833966154493

theorem tailTrace_845829 : CollatzResearch.WordTrace tailWord_845829 prefixEnd_845829 193029701560833966154493 := by
  unfold tailWord_845829
  simp only [CollatzResearch.WordTrace]
  refine ⟨30849918052713463937572541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20566612035142309291715027 30849918052713463937572541)
  ·
    refine ⟨11568719269767548976589703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30849918052713463937572541 11568719269767548976589703)
    ·
      refine ⟨17353078904651323464884555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11568719269767548976589703 17353078904651323464884555)
      ·
        refine ⟨26029618356976985197326833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17353078904651323464884555 26029618356976985197326833)
        ·
          refine ⟨19522213767732738897995125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26029618356976985197326833 19522213767732738897995125)
          ·
            refine ⟨1830207540724944271687043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19522213767732738897995125 1830207540724944271687043)
            ·
              refine ⟨2745311311087416407530565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830207540724944271687043 2745311311087416407530565)
              ·
                refine ⟨514745870828890576411981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2745311311087416407530565 514745870828890576411981)
                ·
                  refine ⟨193029701560833966154493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514745870828890576411981 193029701560833966154493)
                  ·
                    rfl

theorem cell21_845829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_845829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_845829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_845829 prefixEnd_845829 := by exact prefixLift 845829
  have htrace : WordTrace (prefixWord ++ tailWord_845829) baseStart_845829 baseEnd_845829 := by
    simpa [prefixWord, tailWord_845829, baseEnd_845829] using wordTrace_append hprefix tailTrace_845829
  have hstable : (prefixWord ++ tailWord_845829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845829).length < 2 ^ (prefixWord ++ tailWord_845829).sum := by decide
  have hdescent : baseEnd_845829 < baseStart_845829 := by decide
  rcases family_descends (prefixWord ++ tailWord_845829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845863 : List Nat := [1, 1, 7, 1, 2, 1, 2, 3, 3]
def baseStart_845863 : Nat := 118140960795 + 845863 * 2 ^ 59
def prefixEnd_845863 : Nat := 4983230072969 + 3 ^ 40 * 845863 * 2
def baseEnd_845863 : Nat := 193037460824057462587757

theorem tailTrace_845863 : CollatzResearch.WordTrace tailWord_845863 prefixEnd_845863 193037460824057462587757 := by
  unfold tailWord_845863
  simp only [CollatzResearch.WordTrace]
  refine ⟨30851158134590287744310243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20567438756393525162873495 30851158134590287744310243)
  ·
    refine ⟨46276737201885431616465365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30851158134590287744310243 46276737201885431616465365)
    ·
      refine ⟨1084611028169189803510907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 46276737201885431616465365 1084611028169189803510907)
      ·
        refine ⟨1626916542253784705266361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084611028169189803510907 1626916542253784705266361)
        ·
          refine ⟨1220187406690338528949771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1626916542253784705266361 1220187406690338528949771)
          ·
            refine ⟨1830281110035507793424657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220187406690338528949771 1830281110035507793424657)
            ·
              refine ⟨1372710832526630845068493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830281110035507793424657 1372710832526630845068493)
              ·
                refine ⟨514766562197486566900685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1372710832526630845068493 514766562197486566900685)
                ·
                  refine ⟨193037460824057462587757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514766562197486566900685 193037460824057462587757)
                  ·
                    rfl

theorem cell21_845863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 3].length) (baseStart_845863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_845863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_845863 prefixEnd_845863 := by exact prefixLift 845863
  have htrace : WordTrace (prefixWord ++ tailWord_845863) baseStart_845863 baseEnd_845863 := by
    simpa [prefixWord, tailWord_845863, baseEnd_845863] using wordTrace_append hprefix tailTrace_845863
  have hstable : (prefixWord ++ tailWord_845863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845863).length < 2 ^ (prefixWord ++ tailWord_845863).sum := by decide
  have hdescent : baseEnd_845863 < baseStart_845863 := by decide
  rcases family_descends (prefixWord ++ tailWord_845863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845888 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 5]
def baseStart_845888 : Nat := 118140960795 + 845888 * 2 ^ 59
def prefixEnd_845888 : Nat := 4983230072969 + 3 ^ 40 * 845888 * 2
def baseEnd_845888 : Nat := 193043166164662974671039

theorem tailTrace_845888 : CollatzResearch.WordTrace tailWord_845888 prefixEnd_845888 193043166164662974671039 := by
  unfold tailWord_845888
  simp only [CollatzResearch.WordTrace]
  refine ⟨15426034979749858506985159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20568046639666478009313545 15426034979749858506985159)
  ·
    refine ⟨23139052469624787760477739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15426034979749858506985159 23139052469624787760477739)
    ·
      refine ⟨34708578704437181640716609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23139052469624787760477739 34708578704437181640716609)
      ·
        refine ⟨26031434028327886230537457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34708578704437181640716609 26031434028327886230537457)
        ·
          refine ⟨19523575521245914672903093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26031434028327886230537457 19523575521245914672903093)
          ·
            refine ⟨1830335205116804500584665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19523575521245914672903093 1830335205116804500584665)
            ·
              refine ⟨1372751403837603375438499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830335205116804500584665 1372751403837603375438499)
              ·
                refine ⟨2059127105756405063157749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372751403837603375438499 2059127105756405063157749)
                ·
                  refine ⟨193043166164662974671039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2059127105756405063157749 193043166164662974671039)
                  ·
                    rfl

theorem cell21_845888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_845888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_845888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_845888 prefixEnd_845888 := by exact prefixLift 845888
  have htrace : WordTrace (prefixWord ++ tailWord_845888) baseStart_845888 baseEnd_845888 := by
    simpa [prefixWord, tailWord_845888, baseEnd_845888] using wordTrace_append hprefix tailTrace_845888
  have hstable : (prefixWord ++ tailWord_845888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845888).length < 2 ^ (prefixWord ++ tailWord_845888).sum := by decide
  have hdescent : baseEnd_845888 < baseStart_845888 := by decide
  rcases family_descends (prefixWord ++ tailWord_845888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845953 : List Nat := [1, 2, 4, 2, 3, 2, 2, 1, 4]
def baseStart_845953 : Nat := 118140960795 + 845953 * 2 ^ 59
def prefixEnd_845953 : Nat := 4983230072969 + 3 ^ 40 * 845953 * 2
def baseEnd_845953 : Nat := 193058000050237306087573

theorem tailTrace_845953 : CollatzResearch.WordTrace tailWord_845953 prefixEnd_845953 193058000050237306087573 := by
  unfold tailWord_845953
  simp only [CollatzResearch.WordTrace]
  refine ⟨30854440704264233115086513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20569627136176155410057675 30854440704264233115086513)
  ·
    refine ⟨23140830528198174836314885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30854440704264233115086513 23140830528198174836314885)
    ·
      refine ⟨4338905724037157781809041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23140830528198174836314885 4338905724037157781809041)
      ·
        refine ⟨3254179293027868336356781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4338905724037157781809041 3254179293027868336356781)
        ·
          refine ⟨1220317234885450626133793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3254179293027868336356781 1220317234885450626133793)
          ·
            refine ⟨915237926164087969600345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1220317234885450626133793 915237926164087969600345)
            ·
              refine ⟨686428444623065977200259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915237926164087969600345 686428444623065977200259)
              ·
                refine ⟨1029642666934598965800389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686428444623065977200259 1029642666934598965800389)
                ·
                  refine ⟨193058000050237306087573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1029642666934598965800389 193058000050237306087573)
                  ·
                    rfl

theorem cell21_845953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_845953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_845953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_845953 prefixEnd_845953 := by exact prefixLift 845953
  have htrace : WordTrace (prefixWord ++ tailWord_845953) baseStart_845953 baseEnd_845953 := by
    simpa [prefixWord, tailWord_845953, baseEnd_845953] using wordTrace_append hprefix tailTrace_845953
  have hstable : (prefixWord ++ tailWord_845953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845953).length < 2 ^ (prefixWord ++ tailWord_845953).sum := by decide
  have hdescent : baseEnd_845953 < baseStart_845953 := by decide
  rcases family_descends (prefixWord ++ tailWord_845953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846116 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 5]
def baseStart_846116 : Nat := 118140960795 + 846116 * 2 ^ 59
def prefixEnd_846116 : Nat := 4983230072969 + 3 ^ 40 * 846116 * 2
def baseEnd_846116 : Nat := 193095198870985244870573

theorem tailTrace_846116 : CollatzResearch.WordTrace tailWord_846116 prefixEnd_846116 193095198870985244870573 := by
  unfold tailWord_846116
  simp only [CollatzResearch.WordTrace]
  refine ⟨15430192901336855976635101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20573590535115807968846801 15430192901336855976635101)
  ·
    refine ⟨5786322338001320991238163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15430192901336855976635101 5786322338001320991238163)
    ·
      refine ⟨8679483507001981486857245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5786322338001320991238163 8679483507001981486857245)
      ·
        refine ⟨3254806315125743057571467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8679483507001981486857245 3254806315125743057571467)
        ·
          refine ⟨4882209472688614586357201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3254806315125743057571467 4882209472688614586357201)
          ·
            refine ⟨3661657104516460939767901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4882209472688614586357201 3661657104516460939767901)
            ·
              refine ⟨1373121414193672852412963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3661657104516460939767901 1373121414193672852412963)
              ·
                refine ⟨2059682121290509278619445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373121414193672852412963 2059682121290509278619445)
                ·
                  refine ⟨193095198870985244870573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2059682121290509278619445 193095198870985244870573)
                  ·
                    rfl

theorem cell21_846116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_846116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846116 prefixEnd_846116 := by exact prefixLift 846116
  have htrace : WordTrace (prefixWord ++ tailWord_846116) baseStart_846116 baseEnd_846116 := by
    simpa [prefixWord, tailWord_846116, baseEnd_846116] using wordTrace_append hprefix tailTrace_846116
  have hstable : (prefixWord ++ tailWord_846116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846116).length < 2 ^ (prefixWord ++ tailWord_846116).sum := by decide
  have hdescent : baseEnd_846116 < baseStart_846116 := by decide
  rcases family_descends (prefixWord ++ tailWord_846116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846122 : List Nat := [3, 1, 4, 2, 3, 1, 2, 1, 4]
def baseStart_846122 : Nat := 118140960795 + 846122 * 2 ^ 59
def prefixEnd_846122 : Nat := 4983230072969 + 3 ^ 40 * 846122 * 2
def baseEnd_846122 : Nat := 193096568152730567770561

theorem tailTrace_846122 : CollatzResearch.WordTrace tailWord_846122 prefixEnd_846122 193096568152730567770561 := by
  unfold tailWord_846122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7715151160162993744497155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20573736427101316651992413 7715151160162993744497155)
  ·
    refine ⟨11572726740244490616745733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7715151160162993744497155 11572726740244490616745733)
    ·
      refine ⟨2169886263795841990639825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11572726740244490616745733 2169886263795841990639825)
      ·
        refine ⟨1627414697846881492979869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2169886263795841990639825 1627414697846881492979869)
        ·
          refine ⟨610280511692580559867451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1627414697846881492979869 610280511692580559867451)
          ·
            refine ⟨915420767538870839801177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610280511692580559867451 915420767538870839801177)
            ·
              refine ⟨686565575654153129850883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915420767538870839801177 686565575654153129850883)
              ·
                refine ⟨1029848363481229694776325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686565575654153129850883 1029848363481229694776325)
                ·
                  refine ⟨193096568152730567770561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1029848363481229694776325 193096568152730567770561)
                  ·
                    rfl

theorem cell21_846122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_846122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846122 prefixEnd_846122 := by exact prefixLift 846122
  have htrace : WordTrace (prefixWord ++ tailWord_846122) baseStart_846122 baseEnd_846122 := by
    simpa [prefixWord, tailWord_846122, baseEnd_846122] using wordTrace_append hprefix tailTrace_846122
  have hstable : (prefixWord ++ tailWord_846122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846122).length < 2 ^ (prefixWord ++ tailWord_846122).sum := by decide
  have hdescent : baseEnd_846122 < baseStart_846122 := by decide
  rcases family_descends (prefixWord ++ tailWord_846122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846178 : List Nat := [3, 3, 2, 1, 1, 4, 1, 6]
def baseStart_846178 : Nat := 118140960795 + 846178 * 2 ^ 59
def prefixEnd_846178 : Nat := 4983230072969 + 3 ^ 40 * 846178 * 2
def baseEnd_846178 : Nat := 64369782705228971612371

theorem tailTrace_846178 : CollatzResearch.WordTrace tailWord_846178 prefixEnd_846178 64369782705228971612371 := by
  unfold tailWord_846178
  simp only [CollatzResearch.WordTrace]
  refine ⟨7715661782112274135506797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20575098085632731028018125 7715661782112274135506797)
  ·
    refine ⟨2893373168292102800815049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7715661782112274135506797 2893373168292102800815049)
    ·
      refine ⟨2170029876219077100611287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2893373168292102800815049 2170029876219077100611287)
      ·
        refine ⟨3255044814328615650916931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2170029876219077100611287 3255044814328615650916931)
        ·
          refine ⟨4882567221492923476375397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3255044814328615650916931 4882567221492923476375397)
          ·
            refine ⟨915481354029923151820387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4882567221492923476375397 915481354029923151820387)
            ·
              refine ⟨1373222031044884727730581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915481354029923151820387 1373222031044884727730581)
              ·
                refine ⟨64369782705228971612371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1373222031044884727730581 64369782705228971612371)
                ·
                  rfl

theorem cell21_846178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_846178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846178 prefixEnd_846178 := by exact prefixLift 846178
  have htrace : WordTrace (prefixWord ++ tailWord_846178) baseStart_846178 baseEnd_846178 := by
    simpa [prefixWord, tailWord_846178, baseEnd_846178] using wordTrace_append hprefix tailTrace_846178
  have hstable : (prefixWord ++ tailWord_846178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846178).length < 2 ^ (prefixWord ++ tailWord_846178).sum := by decide
  have hdescent : baseEnd_846178 < baseStart_846178 := by decide
  rcases family_descends (prefixWord ++ tailWord_846178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846209 : List Nat := [1, 2, 4, 3, 1, 1, 1, 5, 3]
def baseStart_846209 : Nat := 118140960795 + 846209 * 2 ^ 59
def prefixEnd_846209 : Nat := 4983230072969 + 3 ^ 40 * 846209 * 2
def baseEnd_846209 : Nat := 193116422738037749820383

theorem tailTrace_846209 : CollatzResearch.WordTrace tailWord_846209 prefixEnd_846209 193116422738037749820383 := by
  unfold tailWord_846209
  simp only [CollatzResearch.WordTrace]
  refine ⟨30863777791336788836405681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20575851860891192557603787 30863777791336788836405681)
  ·
    refine ⟨23147833343502591627304261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30863777791336788836405681 23147833343502591627304261)
    ·
      refine ⟨4340218751906735930119549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23147833343502591627304261 4340218751906735930119549)
      ·
        refine ⟨1627582031965025973794831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4340218751906735930119549 1627582031965025973794831)
        ·
          refine ⟨2441373047947538960692247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627582031965025973794831 2441373047947538960692247)
          ·
            refine ⟨3662059571921308441038371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441373047947538960692247 3662059571921308441038371)
            ·
              refine ⟨5493089357881962661557557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3662059571921308441038371 5493089357881962661557557)
              ·
                refine ⟨514977127301433999521021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5493089357881962661557557 514977127301433999521021)
                ·
                  refine ⟨193116422738037749820383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514977127301433999521021 193116422738037749820383)
                  ·
                    rfl

theorem cell21_846209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 3].length) (baseStart_846209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846209 prefixEnd_846209 := by exact prefixLift 846209
  have htrace : WordTrace (prefixWord ++ tailWord_846209) baseStart_846209 baseEnd_846209 := by
    simpa [prefixWord, tailWord_846209, baseEnd_846209] using wordTrace_append hprefix tailTrace_846209
  have hstable : (prefixWord ++ tailWord_846209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846209).length < 2 ^ (prefixWord ++ tailWord_846209).sum := by decide
  have hdescent : baseEnd_846209 < baseStart_846209 := by decide
  rcases family_descends (prefixWord ++ tailWord_846209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846220 : List Nat := [2, 2, 1, 2, 1, 5, 8]
def baseStart_846220 : Nat := 118140960795 + 846220 * 2 ^ 59
def prefixEnd_846220 : Nat := 4983230072969 + 3 ^ 40 * 846220 * 2
def baseEnd_846220 : Nat := 21457659231989352793003

theorem tailTrace_846220 : CollatzResearch.WordTrace tailWord_846220 prefixEnd_846220 21457659231989352793003 := by
  unfold tailWord_846220
  simp only [CollatzResearch.WordTrace]
  refine ⟨15432089497148468857528057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20576119329531291810037409 15432089497148468857528057)
  ·
    refine ⟨11574067122861351643146043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15432089497148468857528057 11574067122861351643146043)
    ·
      refine ⟨17361100684292027464719065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11574067122861351643146043 17361100684292027464719065)
      ·
        refine ⟨13020825513219020598539299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17361100684292027464719065 13020825513219020598539299)
        ·
          refine ⟨19531238269828530897808949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13020825513219020598539299 19531238269828530897808949)
          ·
            refine ⟨1831053587796424771669589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19531238269828530897808949 1831053587796424771669589)
            ·
              refine ⟨21457659231989352793003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1831053587796424771669589 21457659231989352793003)
              ·
                rfl

theorem cell21_846220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 8].length) (baseStart_846220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846220 prefixEnd_846220 := by exact prefixLift 846220
  have htrace : WordTrace (prefixWord ++ tailWord_846220) baseStart_846220 baseEnd_846220 := by
    simpa [prefixWord, tailWord_846220, baseEnd_846220] using wordTrace_append hprefix tailTrace_846220
  have hstable : (prefixWord ++ tailWord_846220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846220).length < 2 ^ (prefixWord ++ tailWord_846220).sum := by decide
  have hdescent : baseEnd_846220 < baseStart_846220 := by decide
  rcases family_descends (prefixWord ++ tailWord_846220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846260 : List Nat := [2, 5, 2, 2, 1, 2, 1, 3, 3]
def baseStart_846260 : Nat := 118140960795 + 846260 * 2 ^ 59
def prefixEnd_846260 : Nat := 4983230072969 + 3 ^ 40 * 846260 * 2
def baseEnd_846260 : Nat := 193128061632872994470279

theorem tailTrace_846260 : CollatzResearch.WordTrace tailWord_846260 prefixEnd_846260 193128061632872994470279 := by
  unfold tailWord_846260
  simp only [CollatzResearch.WordTrace]
  refine ⟨15432818957076012273256117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20577091942768016364341489 15432818957076012273256117)
  ·
    refine ⟨1446826777225876150617761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15432818957076012273256117 1446826777225876150617761)
    ·
      refine ⟨1085120082919407112963321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1446826777225876150617761 1085120082919407112963321)
      ·
        refine ⟨813840062189555334722491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1085120082919407112963321 813840062189555334722491)
        ·
          refine ⟨1220760093284333002083737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813840062189555334722491 1220760093284333002083737)
          ·
            refine ⟨915570069963249751562803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1220760093284333002083737 915570069963249751562803)
            ·
              refine ⟨1373355104944874627344205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915570069963249751562803 1373355104944874627344205)
              ·
                refine ⟨515008164354327985254077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1373355104944874627344205 515008164354327985254077)
                ·
                  refine ⟨193128061632872994470279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515008164354327985254077 193128061632872994470279)
                  ·
                    rfl

theorem cell21_846260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_846260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846260 prefixEnd_846260 := by exact prefixLift 846260
  have htrace : WordTrace (prefixWord ++ tailWord_846260) baseStart_846260 baseEnd_846260 := by
    simpa [prefixWord, tailWord_846260, baseEnd_846260] using wordTrace_append hprefix tailTrace_846260
  have hstable : (prefixWord ++ tailWord_846260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846260).length < 2 ^ (prefixWord ++ tailWord_846260).sum := by decide
  have hdescent : baseEnd_846260 < baseStart_846260 := by decide
  rcases family_descends (prefixWord ++ tailWord_846260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846282 : List Nat := [3, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_846282 : Nat := 118140960795 + 846282 * 2 ^ 59
def prefixEnd_846282 : Nat := 4983230072969 + 3 ^ 40 * 846282 * 2
def baseEnd_846282 : Nat := 193133082332605845103567

theorem tailTrace_846282 : CollatzResearch.WordTrace tailWord_846282 prefixEnd_846282 193133082332605845103567 := by
  unfold tailWord_846282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7716610080018080575953275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20577626880048214869208733 7716610080018080575953275)
  ·
    refine ⟨11574915120027120863929913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7716610080018080575953275 11574915120027120863929913)
    ·
      refine ⟨8681186340020340647947435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11574915120027120863929913 8681186340020340647947435)
      ·
        refine ⟨13021779510030510971921153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8681186340020340647947435 13021779510030510971921153)
        ·
          refine ⟨9766334632522883228940865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13021779510030510971921153 9766334632522883228940865)
          ·
            refine ⟨7324750974392162421705649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9766334632522883228940865 7324750974392162421705649)
            ·
              refine ⟨5493563230794121816279237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7324750974392162421705649 5493563230794121816279237)
              ·
                refine ⟨1030043105773897840552357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5493563230794121816279237 1030043105773897840552357)
                ·
                  refine ⟨193133082332605845103567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030043105773897840552357 193133082332605845103567)
                  ·
                    rfl

theorem cell21_846282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_846282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846282 prefixEnd_846282 := by exact prefixLift 846282
  have htrace : WordTrace (prefixWord ++ tailWord_846282) baseStart_846282 baseEnd_846282 := by
    simpa [prefixWord, tailWord_846282, baseEnd_846282] using wordTrace_append hprefix tailTrace_846282
  have hstable : (prefixWord ++ tailWord_846282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846282).length < 2 ^ (prefixWord ++ tailWord_846282).sum := by decide
  have hdescent : baseEnd_846282 < baseStart_846282 := by decide
  rcases family_descends (prefixWord ++ tailWord_846282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846341 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 6]
def baseStart_846341 : Nat := 118140960795 + 846341 * 2 ^ 59
def prefixEnd_846341 : Nat := 4983230072969 + 3 ^ 40 * 846341 * 2
def baseEnd_846341 : Nat := 193146546936434853620113

theorem tailTrace_846341 : CollatzResearch.WordTrace tailWord_846341 prefixEnd_846341 193146546936434853620113 := by
  unfold tailWord_846341
  simp only [CollatzResearch.WordTrace]
  refine ⟨30868592226858575380210877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20579061484572383586807251 30868592226858575380210877)
  ·
    refine ⟨11575722085071965767579079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30868592226858575380210877 11575722085071965767579079)
    ·
      refine ⟨17363583127607948651368619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11575722085071965767579079 17363583127607948651368619)
      ·
        refine ⟨26045374691411922977052929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17363583127607948651368619 26045374691411922977052929)
        ·
          refine ⟨19534031018558942232789697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26045374691411922977052929 19534031018558942232789697)
          ·
            refine ⟨14650523263919206674592273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19534031018558942232789697 14650523263919206674592273)
            ·
              refine ⟨10987892447939405005944205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14650523263919206674592273 10987892447939405005944205)
              ·
                refine ⟨4120459667977276877229077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10987892447939405005944205 4120459667977276877229077)
                ·
                  refine ⟨193146546936434853620113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4120459667977276877229077 193146546936434853620113)
                  ·
                    rfl

theorem cell21_846341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_846341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846341 prefixEnd_846341 := by exact prefixLift 846341
  have htrace : WordTrace (prefixWord ++ tailWord_846341) baseStart_846341 baseEnd_846341 := by
    simpa [prefixWord, tailWord_846341, baseEnd_846341] using wordTrace_append hprefix tailTrace_846341
  have hstable : (prefixWord ++ tailWord_846341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846341).length < 2 ^ (prefixWord ++ tailWord_846341).sum := by decide
  have hdescent : baseEnd_846341 < baseStart_846341 := by decide
  rcases family_descends (prefixWord ++ tailWord_846341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846454 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_846454 : Nat := 118140960795 + 846454 * 2 ^ 59
def prefixEnd_846454 : Nat := 4983230072969 + 3 ^ 40 * 846454 * 2
def baseEnd_846454 : Nat := 193172335075971768236549

theorem tailTrace_846454 : CollatzResearch.WordTrace tailWord_846454 prefixEnd_846454 193172335075971768236549 := by
  unfold tailWord_846454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1929544604715574729942151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20581809116966130452716277 1929544604715574729942151)
  ·
    refine ⟨2894316907073362094913227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1929544604715574729942151 2894316907073362094913227)
    ·
      refine ⟨4341475360610043142369841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2894316907073362094913227 4341475360610043142369841)
      ·
        refine ⟨3256106520457532356777381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4341475360610043142369841 3256106520457532356777381)
        ·
          refine ⟨610519972585787316895759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3256106520457532356777381 610519972585787316895759)
          ·
            refine ⟨915779958878680975343639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610519972585787316895759 915779958878680975343639)
            ·
              refine ⟨1373669938318021463015459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915779958878680975343639 1373669938318021463015459)
              ·
                refine ⟨2060504907477032194523189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373669938318021463015459 2060504907477032194523189)
                ·
                  refine ⟨193172335075971768236549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2060504907477032194523189 193172335075971768236549)
                  ·
                    rfl

theorem cell21_846454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_846454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846454 prefixEnd_846454 := by exact prefixLift 846454
  have htrace : WordTrace (prefixWord ++ tailWord_846454) baseStart_846454 baseEnd_846454 := by
    simpa [prefixWord, tailWord_846454, baseEnd_846454] using wordTrace_append hprefix tailTrace_846454
  have hstable : (prefixWord ++ tailWord_846454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846454).length < 2 ^ (prefixWord ++ tailWord_846454).sum := by decide
  have hdescent : baseEnd_846454 < baseStart_846454 := by decide
  rcases family_descends (prefixWord ++ tailWord_846454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846468 : List Nat := [2, 3, 2, 1, 3, 3, 2, 1, 4]
def baseStart_846468 : Nat := 118140960795 + 846468 * 2 ^ 59
def prefixEnd_846468 : Nat := 4983230072969 + 3 ^ 40 * 846468 * 2
def baseEnd_846468 : Nat := 193175530066710855003187

theorem tailTrace_846468 : CollatzResearch.WordTrace tailWord_846468 prefixEnd_846468 193175530066710855003187 := by
  unfold tailWord_846468
  simp only [CollatzResearch.WordTrace]
  refine ⟨15436612148699238035042029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20582149531598984046722705 15436612148699238035042029)
  ·
    refine ⟨5788729555762214263140761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15436612148699238035042029 5788729555762214263140761)
    ·
      refine ⟨4341547166821660697355571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5788729555762214263140761 4341547166821660697355571)
      ·
        refine ⟨6512320750232491046033357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4341547166821660697355571 6512320750232491046033357)
        ·
          refine ⟨2442120281337184142262509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6512320750232491046033357 2442120281337184142262509)
          ·
            refine ⟨915795105501444053348441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2442120281337184142262509 915795105501444053348441)
            ·
              refine ⟨686846329126083040011331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915795105501444053348441 686846329126083040011331)
              ·
                refine ⟨1030269493689124560016997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686846329126083040011331 1030269493689124560016997)
                ·
                  refine ⟨193175530066710855003187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030269493689124560016997 193175530066710855003187)
                  ·
                    rfl

theorem cell21_846468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_846468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846468 prefixEnd_846468 := by exact prefixLift 846468
  have htrace : WordTrace (prefixWord ++ tailWord_846468) baseStart_846468 baseEnd_846468 := by
    simpa [prefixWord, tailWord_846468, baseEnd_846468] using wordTrace_append hprefix tailTrace_846468
  have hstable : (prefixWord ++ tailWord_846468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846468).length < 2 ^ (prefixWord ++ tailWord_846468).sum := by decide
  have hdescent : baseEnd_846468 < baseStart_846468 := by decide
  rcases family_descends (prefixWord ++ tailWord_846468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846493 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 8]
def baseStart_846493 : Nat := 118140960795 + 846493 * 2 ^ 59
def prefixEnd_846493 : Nat := 4983230072969 + 3 ^ 40 * 846493 * 2
def baseEnd_846493 : Nat := 193181235407316367086469

theorem tailTrace_846493 : CollatzResearch.WordTrace tailWord_846493 prefixEnd_846493 193181235407316367086469 := by
  unfold tailWord_846493
  simp only [CollatzResearch.WordTrace]
  refine ⟨30874136122307905339744133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20582757414871936893162755 30874136122307905339744133)
  ·
    refine ⟨5788900522932732251202025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30874136122307905339744133 5788900522932732251202025)
    ·
      refine ⟨4341675392199549188401519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5788900522932732251202025 4341675392199549188401519)
      ·
        refine ⟨6512513088299323782602279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4341675392199549188401519 6512513088299323782602279)
        ·
          refine ⟨9768769632448985673903419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6512513088299323782602279 9768769632448985673903419)
          ·
            refine ⟨14653154448673478510855129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9768769632448985673903419 14653154448673478510855129)
            ·
              refine ⟨10989865836505108883141347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14653154448673478510855129 10989865836505108883141347)
              ·
                refine ⟨16484798754757663324712021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10989865836505108883141347 16484798754757663324712021)
                ·
                  refine ⟨193181235407316367086469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16484798754757663324712021 193181235407316367086469)
                  ·
                    rfl

theorem cell21_846493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_846493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846493 prefixEnd_846493 := by exact prefixLift 846493
  have htrace : WordTrace (prefixWord ++ tailWord_846493) baseStart_846493 baseEnd_846493 := by
    simpa [prefixWord, tailWord_846493, baseEnd_846493] using wordTrace_append hprefix tailTrace_846493
  have hstable : (prefixWord ++ tailWord_846493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846493).length < 2 ^ (prefixWord ++ tailWord_846493).sum := by decide
  have hdescent : baseEnd_846493 < baseStart_846493 := by decide
  rcases family_descends (prefixWord ++ tailWord_846493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846583 : List Nat := [1, 1, 3, 1, 1, 1, 3, 10]
def baseStart_846583 : Nat := 118140960795 + 846583 * 2 ^ 59
def prefixEnd_846583 : Nat := 4983230072969 + 3 ^ 40 * 846583 * 2
def baseEnd_846583 : Nat := 64400591544498736862095

theorem tailTrace_846583 : CollatzResearch.WordTrace tailWord_846583 prefixEnd_846583 64400591544498736862095 := by
  unfold tailWord_846583
  simp only [CollatzResearch.WordTrace]
  refine ⟨30877418691981850710520403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20584945794654567140346935 30877418691981850710520403)
  ·
    refine ⟨46316128037972776065780605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30877418691981850710520403 46316128037972776065780605)
    ·
      refine ⟨17368548014239791024667727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46316128037972776065780605 17368548014239791024667727)
      ·
        refine ⟨26052822021359686537001591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17368548014239791024667727 26052822021359686537001591)
        ·
          refine ⟨39079233032039529805502387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26052822021359686537001591 39079233032039529805502387)
          ·
            refine ⟨58618849548059294708253581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39079233032039529805502387 58618849548059294708253581)
            ·
              refine ⟨21982068580522235515595093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58618849548059294708253581 21982068580522235515595093)
              ·
                refine ⟨64400591544498736862095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21982068580522235515595093 64400591544498736862095)
                ·
                  rfl

theorem cell21_846583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 10].length) (baseStart_846583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846583 prefixEnd_846583 := by exact prefixLift 846583
  have htrace : WordTrace (prefixWord ++ tailWord_846583) baseStart_846583 baseEnd_846583 := by
    simpa [prefixWord, tailWord_846583, baseEnd_846583] using wordTrace_append hprefix tailTrace_846583
  have hstable : (prefixWord ++ tailWord_846583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846583).length < 2 ^ (prefixWord ++ tailWord_846583).sum := by decide
  have hdescent : baseEnd_846583 < baseStart_846583 := by decide
  rcases family_descends (prefixWord ++ tailWord_846583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846600 : List Nat := [2, 1, 3, 2, 2, 3, 1, 7]
def baseStart_846600 : Nat := 118140960795 + 846600 * 2 ^ 59
def prefixEnd_846600 : Nat := 4983230072969 + 3 ^ 40 * 846600 * 2
def baseEnd_846600 : Nat := 64401884755035986267639

theorem tailTrace_846600 : CollatzResearch.WordTrace tailWord_846600 prefixEnd_846600 64401884755035986267639 := by
  unfold tailWord_846600
  simp only [CollatzResearch.WordTrace]
  refine ⟨15439019366460131306944627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20585359155280175075926169 15439019366460131306944627)
  ·
    refine ⟨23158529049690196960416941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15439019366460131306944627 23158529049690196960416941)
    ·
      refine ⟨8684448393633823860156353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23158529049690196960416941 8684448393633823860156353)
      ·
        refine ⟨6513336295225367895117265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8684448393633823860156353 6513336295225367895117265)
        ·
          refine ⟨4885002221419025921337949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6513336295225367895117265 4885002221419025921337949)
          ·
            refine ⟨1831875833032134720501731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4885002221419025921337949 1831875833032134720501731)
            ·
              refine ⟨2747813749548202080752597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831875833032134720501731 2747813749548202080752597)
              ·
                refine ⟨64401884755035986267639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2747813749548202080752597 64401884755035986267639)
                ·
                  rfl

theorem cell21_846600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_846600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846600 prefixEnd_846600 := by exact prefixLift 846600
  have htrace : WordTrace (prefixWord ++ tailWord_846600) baseStart_846600 baseEnd_846600 := by
    simpa [prefixWord, tailWord_846600, baseEnd_846600] using wordTrace_append hprefix tailTrace_846600
  have hstable : (prefixWord ++ tailWord_846600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846600).length < 2 ^ (prefixWord ++ tailWord_846600).sum := by decide
  have hdescent : baseEnd_846600 < baseStart_846600 := by decide
  rcases family_descends (prefixWord ++ tailWord_846600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846634 : List Nat := [3, 1, 4, 3, 1, 1, 2, 6]
def baseStart_846634 : Nat := 118140960795 + 846634 * 2 ^ 59
def prefixEnd_846634 : Nat := 4983230072969 + 3 ^ 40 * 846634 * 2
def baseEnd_846634 : Nat := 64404471176110485078727

theorem tailTrace_846634 : CollatzResearch.WordTrace tailWord_846634 prefixEnd_846634 64404471176110485078727 := by
  unfold tailWord_846634
  simp only [CollatzResearch.WordTrace]
  refine ⟨7719819703699271605156739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20586185876531390947084637 7719819703699271605156739)
  ·
    refine ⟨11579729555548907407735109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7719819703699271605156739 11579729555548907407735109)
    ·
      refine ⟨2171199291665420138950333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11579729555548907407735109 2171199291665420138950333)
      ·
        refine ⟨814199734374532552106375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2171199291665420138950333 814199734374532552106375)
        ·
          refine ⟨1221299601561798828159563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814199734374532552106375 1221299601561798828159563)
          ·
            refine ⟨1831949402342698242239345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221299601561798828159563 1831949402342698242239345)
            ·
              refine ⟨1373962051757023681679509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831949402342698242239345 1373962051757023681679509)
              ·
                refine ⟨64404471176110485078727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1373962051757023681679509 64404471176110485078727)
                ·
                  rfl

theorem cell21_846634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_846634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846634 prefixEnd_846634 := by exact prefixLift 846634
  have htrace : WordTrace (prefixWord ++ tailWord_846634) baseStart_846634 baseEnd_846634 := by
    simpa [prefixWord, tailWord_846634, baseEnd_846634] using wordTrace_append hprefix tailTrace_846634
  have hstable : (prefixWord ++ tailWord_846634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846634).length < 2 ^ (prefixWord ++ tailWord_846634).sum := by decide
  have hdescent : baseEnd_846634 < baseStart_846634 := by decide
  rcases family_descends (prefixWord ++ tailWord_846634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846659 : List Nat := [1, 1, 1, 3, 1, 4, 1, 9]
def baseStart_846659 : Nat := 118140960795 + 846659 * 2 ^ 59
def prefixEnd_846659 : Nat := 4983230072969 + 3 ^ 40 * 846659 * 2
def baseEnd_846659 : Nat := 64406372956312322439821

theorem tailTrace_846659 : CollatzResearch.WordTrace tailWord_846659 prefixEnd_846659 64406372956312322439821 := by
  unfold tailWord_846659
  simp only [CollatzResearch.WordTrace]
  refine ⟨30880190639706515690287031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20586793759804343793524687 30880190639706515690287031)
  ·
    refine ⟨46320285959559773535430547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30880190639706515690287031 46320285959559773535430547)
    ·
      refine ⟨69480428939339660303145821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46320285959559773535430547 69480428939339660303145821)
      ·
        refine ⟨26055160852252372613679683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69480428939339660303145821 26055160852252372613679683)
        ·
          refine ⟨39082741278378558920519525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26055160852252372613679683 39082741278378558920519525)
          ·
            refine ⟨7328013989695979797597411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39082741278378558920519525 7328013989695979797597411)
            ·
              refine ⟨10992020984543969696396117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7328013989695979797597411 10992020984543969696396117)
              ·
                refine ⟨64406372956312322439821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10992020984543969696396117 64406372956312322439821)
                ·
                  rfl

theorem cell21_846659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 9].length) (baseStart_846659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846659 prefixEnd_846659 := by exact prefixLift 846659
  have htrace : WordTrace (prefixWord ++ tailWord_846659) baseStart_846659 baseEnd_846659 := by
    simpa [prefixWord, tailWord_846659, baseEnd_846659] using wordTrace_append hprefix tailTrace_846659
  have hstable : (prefixWord ++ tailWord_846659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846659).length < 2 ^ (prefixWord ++ tailWord_846659).sum := by decide
  have hdescent : baseEnd_846659 < baseStart_846659 := by decide
  rcases family_descends (prefixWord ++ tailWord_846659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846676 : List Nat := [2, 4, 1, 1, 4, 9]
def baseStart_846676 : Nat := 118140960795 + 846676 * 2 ^ 59
def prefixEnd_846676 : Nat := 4983230072969 + 3 ^ 40 * 846676 * 2
def baseEnd_846676 : Nat := 7156407351872174649485

theorem tailTrace_846676 : CollatzResearch.WordTrace tailWord_846676 prefixEnd_846676 7156407351872174649485 := by
  unfold tailWord_846676
  simp only [CollatzResearch.WordTrace]
  refine ⟨15440405340322463796827941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20587207120429951729103921 15440405340322463796827941)
  ·
    refine ⟨2895076001310461961905239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15440405340322463796827941 2895076001310461961905239)
    ·
      refine ⟨4342614001965692942857859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2895076001310461961905239 4342614001965692942857859)
      ·
        refine ⟨6513921002948539414286789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4342614001965692942857859 6513921002948539414286789)
        ·
          refine ⟨1221360188052851140178773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6513921002948539414286789 1221360188052851140178773)
          ·
            refine ⟨7156407351872174649485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1221360188052851140178773 7156407351872174649485)
            ·
              rfl

theorem cell21_846676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 9].length) (baseStart_846676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846676 prefixEnd_846676 := by exact prefixLift 846676
  have htrace : WordTrace (prefixWord ++ tailWord_846676) baseStart_846676 baseEnd_846676 := by
    simpa [prefixWord, tailWord_846676, baseEnd_846676] using wordTrace_append hprefix tailTrace_846676
  have hstable : (prefixWord ++ tailWord_846676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846676).length < 2 ^ (prefixWord ++ tailWord_846676).sum := by decide
  have hdescent : baseEnd_846676 < baseStart_846676 := by decide
  rcases family_descends (prefixWord ++ tailWord_846676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846710 : List Nat := [5, 1, 1, 3, 1, 2, 3, 5]
def baseStart_846710 : Nat := 118140960795 + 846710 * 2 ^ 59
def prefixEnd_846710 : Nat := 4983230072969 + 3 ^ 40 * 846710 * 2
def baseEnd_846710 : Nat := 64410252587924070656453

theorem tailTrace_846710 : CollatzResearch.WordTrace tailWord_846710 prefixEnd_846710 64410252587924070656453 := by
  unfold tailWord_846710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1930128172657609462524599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20588033841681167600262389 1930128172657609462524599)
  ·
    refine ⟨2895192258986414193786899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1930128172657609462524599 2895192258986414193786899)
    ·
      refine ⟨4342788388479621290680349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2895192258986414193786899 4342788388479621290680349)
      ·
        refine ⟨1628545645679857984005131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4342788388479621290680349 1628545645679857984005131)
        ·
          refine ⟨2442818468519786976007697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628545645679857984005131 2442818468519786976007697)
          ·
            refine ⟨1832113851389840232005773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2442818468519786976007697 1832113851389840232005773)
            ·
              refine ⟨687042694271190087002165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1832113851389840232005773 687042694271190087002165)
              ·
                refine ⟨64410252587924070656453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 687042694271190087002165 64410252587924070656453)
                ·
                  rfl

theorem cell21_846710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_846710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846710 prefixEnd_846710 := by exact prefixLift 846710
  have htrace : WordTrace (prefixWord ++ tailWord_846710) baseStart_846710 baseEnd_846710 := by
    simpa [prefixWord, tailWord_846710, baseEnd_846710] using wordTrace_append hprefix tailTrace_846710
  have hstable : (prefixWord ++ tailWord_846710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846710).length < 2 ^ (prefixWord ++ tailWord_846710).sum := by decide
  have hdescent : baseEnd_846710 < baseStart_846710 := by decide
  rcases family_descends (prefixWord ++ tailWord_846710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846783 : List Nat := [1, 1, 2, 2, 2, 1, 2, 7, 3]
def baseStart_846783 : Nat := 118140960795 + 846783 * 2 ^ 59
def prefixEnd_846783 : Nat := 4983230072969 + 3 ^ 40 * 846783 * 2
def baseEnd_846783 : Nat := 193247417358340307252543

theorem tailTrace_846783 : CollatzResearch.WordTrace tailWord_846783 prefixEnd_846783 193247417358340307252543 := by
  unfold tailWord_846783
  simp only [CollatzResearch.WordTrace]
  refine ⟨30884713291257284867801003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20589808860838189911867335 30884713291257284867801003)
  ·
    refine ⟨46327069936885927301701505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30884713291257284867801003 46327069936885927301701505)
    ·
      refine ⟨34745302452664445476276129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46327069936885927301701505 34745302452664445476276129)
      ·
        refine ⟨26058976839498334107207097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34745302452664445476276129 26058976839498334107207097)
        ·
          refine ⟨19544232629623750580405323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26058976839498334107207097 19544232629623750580405323)
          ·
            refine ⟨29316348944435625870607985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19544232629623750580405323 29316348944435625870607985)
            ·
              refine ⟨21987261708326719402955989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29316348944435625870607985 21987261708326719402955989)
              ·
                refine ⟨515326446288907486006781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21987261708326719402955989 515326446288907486006781)
                ·
                  refine ⟨193247417358340307252543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515326446288907486006781 193247417358340307252543)
                  ·
                    rfl

theorem cell21_846783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 3].length) (baseStart_846783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846783 prefixEnd_846783 := by exact prefixLift 846783
  have htrace : WordTrace (prefixWord ++ tailWord_846783) baseStart_846783 baseEnd_846783 := by
    simpa [prefixWord, tailWord_846783, baseEnd_846783] using wordTrace_append hprefix tailTrace_846783
  have hstable : (prefixWord ++ tailWord_846783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846783).length < 2 ^ (prefixWord ++ tailWord_846783).sum := by decide
  have hdescent : baseEnd_846783 < baseStart_846783 := by decide
  rcases family_descends (prefixWord ++ tailWord_846783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846873 : List Nat := [1, 2, 1, 2, 1, 1, 6, 3, 4]
def baseStart_846873 : Nat := 118140960795 + 846873 * 2 ^ 59
def prefixEnd_846873 : Nat := 4983230072969 + 3 ^ 40 * 846873 * 2
def baseEnd_846873 : Nat := 193267956584520150752359

theorem tailTrace_846873 : CollatzResearch.WordTrace tailWord_846873 prefixEnd_846873 193267956584520150752359 := by
  unfold tailWord_846873
  simp only [CollatzResearch.WordTrace]
  refine ⟨30887995860931230238577273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20591997240620820159051515 30887995860931230238577273)
  ·
    refine ⟨23165996895698422678932955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30887995860931230238577273 23165996895698422678932955)
    ·
      refine ⟨34748995343547634018399433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23165996895698422678932955 34748995343547634018399433)
      ·
        refine ⟨26061746507660725513799575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34748995343547634018399433 26061746507660725513799575)
        ·
          refine ⟨39092619761491088270699363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26061746507660725513799575 39092619761491088270699363)
          ·
            refine ⟨58638929642236632406049045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39092619761491088270699363 58638929642236632406049045)
            ·
              refine ⟨2748699826979842144033549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58638929642236632406049045 2748699826979842144033549)
              ·
                refine ⟨1030762435117440804012581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2748699826979842144033549 1030762435117440804012581)
                ·
                  refine ⟨193267956584520150752359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030762435117440804012581 193267956584520150752359)
                  ·
                    rfl

theorem cell21_846873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_846873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846873 prefixEnd_846873 := by exact prefixLift 846873
  have htrace : WordTrace (prefixWord ++ tailWord_846873) baseStart_846873 baseEnd_846873 := by
    simpa [prefixWord, tailWord_846873, baseEnd_846873] using wordTrace_append hprefix tailTrace_846873
  have hstable : (prefixWord ++ tailWord_846873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846873).length < 2 ^ (prefixWord ++ tailWord_846873).sum := by decide
  have hdescent : baseEnd_846873 < baseStart_846873 := by decide
  rcases family_descends (prefixWord ++ tailWord_846873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846966 : List Nat := [5, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_846966 : Nat := 118140960795 + 846966 * 2 ^ 59
def prefixEnd_846966 : Nat := 4983230072969 + 3 ^ 40 * 846966 * 2
def baseEnd_846966 : Nat := 193289180451572655702169

theorem tailTrace_846966 : CollatzResearch.WordTrace tailWord_846966 prefixEnd_846966 193289180451572655702169 := by
  unfold tailWord_846966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1930711740599644195107047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20594258566396204747808501 1930711740599644195107047)
  ·
    refine ⟨2896067610899466292660571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1930711740599644195107047 2896067610899466292660571)
    ·
      refine ⟨4344101416349199438990857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2896067610899466292660571 4344101416349199438990857)
      ·
        refine ⟨3258076062261899579243143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4344101416349199438990857 3258076062261899579243143)
        ·
          refine ⟨4887114093392849368864715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3258076062261899579243143 4887114093392849368864715)
          ·
            refine ⟨7330671140089274053297073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887114093392849368864715 7330671140089274053297073)
            ·
              refine ⟨5498003355066955539972805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7330671140089274053297073 5498003355066955539972805)
              ·
                refine ⟨1030875629075054163744901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5498003355066955539972805 1030875629075054163744901)
                ·
                  refine ⟨193289180451572655702169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030875629075054163744901 193289180451572655702169)
                  ·
                    rfl

theorem cell21_846966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_846966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846966 prefixEnd_846966 := by exact prefixLift 846966
  have htrace : WordTrace (prefixWord ++ tailWord_846966) baseStart_846966 baseEnd_846966 := by
    simpa [prefixWord, tailWord_846966, baseEnd_846966] using wordTrace_append hprefix tailTrace_846966
  have hstable : (prefixWord ++ tailWord_846966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846966).length < 2 ^ (prefixWord ++ tailWord_846966).sum := by decide
  have hdescent : baseEnd_846966 < baseStart_846966 := by decide
  rcases family_descends (prefixWord ++ tailWord_846966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846969 : List Nat := [1, 2, 1, 3, 5, 1, 3, 2, 3]
def baseStart_846969 : Nat := 118140960795 + 846969 * 2 ^ 59
def prefixEnd_846969 : Nat := 4983230072969 + 3 ^ 40 * 846969 * 2
def baseEnd_846969 : Nat := 193289865092445317152163

theorem tailTrace_846969 : CollatzResearch.WordTrace tailWord_846969 prefixEnd_846969 193289865092445317152163 := by
  unfold tailWord_846969
  simp only [CollatzResearch.WordTrace]
  refine ⟨30891497268583438634071961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20594331512388959089381307 30891497268583438634071961)
  ·
    refine ⟨23168622951437578975553971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30891497268583438634071961 23168622951437578975553971)
    ·
      refine ⟨34752934427156368463330957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23168622951437578975553971 34752934427156368463330957)
      ·
        refine ⟨13032350410183638173749109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34752934427156368463330957 13032350410183638173749109)
        ·
          refine ⟨1221782850954716078788979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13032350410183638173749109 1221782850954716078788979)
          ·
            refine ⟨1832674276432074118183469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221782850954716078788979 1832674276432074118183469)
            ·
              refine ⟨687252853662027794318801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1832674276432074118183469 687252853662027794318801)
              ·
                refine ⟨515439640246520845739101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687252853662027794318801 515439640246520845739101)
                ·
                  refine ⟨193289865092445317152163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515439640246520845739101 193289865092445317152163)
                  ·
                    rfl

theorem cell21_846969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 3].length) (baseStart_846969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846969 prefixEnd_846969 := by exact prefixLift 846969
  have htrace : WordTrace (prefixWord ++ tailWord_846969) baseStart_846969 baseEnd_846969 := by
    simpa [prefixWord, tailWord_846969, baseEnd_846969] using wordTrace_append hprefix tailTrace_846969
  have hstable : (prefixWord ++ tailWord_846969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846969).length < 2 ^ (prefixWord ++ tailWord_846969).sum := by decide
  have hdescent : baseEnd_846969 < baseStart_846969 := by decide
  rcases family_descends (prefixWord ++ tailWord_846969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846980 : List Nat := [2, 3, 2, 1, 2, 3, 2, 6]
def baseStart_846980 : Nat := 118140960795 + 846980 * 2 ^ 59
def prefixEnd_846980 : Nat := 4983230072969 + 3 ^ 40 * 846980 * 2
def baseEnd_846980 : Nat := 64430791814103914156269

theorem tailTrace_846980 : CollatzResearch.WordTrace tailWord_846980 prefixEnd_846980 64430791814103914156269 := by
  unfold tailWord_846980
  simp only [CollatzResearch.WordTrace]
  refine ⟨15445949235771793756361197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20594598981029058341814929 15445949235771793756361197)
  ·
    refine ⟨5792230963414422658635449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15445949235771793756361197 5792230963414422658635449)
    ·
      refine ⟨4344173222560816993976587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5792230963414422658635449 4344173222560816993976587)
      ·
        refine ⟨6516259833841225490964881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4344173222560816993976587 6516259833841225490964881)
        ·
          refine ⟨4887194875380919118223661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6516259833841225490964881 4887194875380919118223661)
          ·
            refine ⟨1832698078267844669333873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4887194875380919118223661 1832698078267844669333873)
            ·
              refine ⟨1374523558700883502000405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832698078267844669333873 1374523558700883502000405)
              ·
                refine ⟨64430791814103914156269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1374523558700883502000405 64430791814103914156269)
                ·
                  rfl

theorem cell21_846980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_846980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_846980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_846980 prefixEnd_846980 := by exact prefixLift 846980
  have htrace : WordTrace (prefixWord ++ tailWord_846980) baseStart_846980 baseEnd_846980 := by
    simpa [prefixWord, tailWord_846980, baseEnd_846980] using wordTrace_append hprefix tailTrace_846980
  have hstable : (prefixWord ++ tailWord_846980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846980).length < 2 ^ (prefixWord ++ tailWord_846980).sum := by decide
  have hdescent : baseEnd_846980 < baseStart_846980 := by decide
  rcases family_descends (prefixWord ++ tailWord_846980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847039 : List Nat := [1, 1, 2, 2, 2, 2, 5, 6]
def baseStart_847039 : Nat := 118140960795 + 847039 * 2 ^ 59
def prefixEnd_847039 : Nat := 4983230072969 + 3 ^ 40 * 847039 * 2
def baseEnd_847039 : Nat := 64435280015380250328451

theorem tailTrace_847039 : CollatzResearch.WordTrace tailWord_847039 prefixEnd_847039 64435280015380250328451 := by
  unfold tailWord_847039
  simp only [CollatzResearch.WordTrace]
  refine ⟨30894050378329840589120171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20596033585553227059413447 30894050378329840589120171)
  ·
    refine ⟨46341075567494760883680257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30894050378329840589120171 46341075567494760883680257)
    ·
      refine ⟨34755806675621070662760193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46341075567494760883680257 34755806675621070662760193)
      ·
        refine ⟨26066855006715802997070145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34755806675621070662760193 26066855006715802997070145)
        ·
          refine ⟨19550141255036852247802609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26066855006715802997070145 19550141255036852247802609)
          ·
            refine ⟨14662605941277639185851957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19550141255036852247802609 14662605941277639185851957)
            ·
              refine ⟨1374619306994778673673621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14662605941277639185851957 1374619306994778673673621)
              ·
                refine ⟨64435280015380250328451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1374619306994778673673621 64435280015380250328451)
                ·
                  rfl

theorem cell21_847039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 6].length) (baseStart_847039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847039 prefixEnd_847039 := by exact prefixLift 847039
  have htrace : WordTrace (prefixWord ++ tailWord_847039) baseStart_847039 baseEnd_847039 := by
    simpa [prefixWord, tailWord_847039, baseEnd_847039] using wordTrace_append hprefix tailTrace_847039
  have hstable : (prefixWord ++ tailWord_847039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847039).length < 2 ^ (prefixWord ++ tailWord_847039).sum := by decide
  have hdescent : baseEnd_847039 < baseStart_847039 := by decide
  rcases family_descends (prefixWord ++ tailWord_847039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847062 : List Nat := [5, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_847062 : Nat := 118140960795 + 847062 * 2 ^ 59
def prefixEnd_847062 : Nat := 4983230072969 + 3 ^ 40 * 847062 * 2
def baseEnd_847062 : Nat := 193311088959497822101973

theorem tailTrace_847062 : CollatzResearch.WordTrace tailWord_847062 prefixEnd_847062 193311088959497822101973 := by
  unfold tailWord_847062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1930930578577907219825465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20596592838164343678138293 1930930578577907219825465)
  ·
    refine ⟨1448197933933430414869099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1930930578577907219825465 1448197933933430414869099)
    ·
      refine ⟨2172296900900145622303649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1448197933933430414869099 2172296900900145622303649)
      ·
        refine ⟨1629222675675109216727737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2172296900900145622303649 1629222675675109216727737)
        ·
          refine ⟨1221917006756331912545803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1629222675675109216727737 1221917006756331912545803)
          ·
            refine ⟨1832875510134497868818705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221917006756331912545803 1832875510134497868818705)
            ·
              refine ⟨1374656632600873401614029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832875510134497868818705 1374656632600873401614029)
              ·
                refine ⟨515496237225327525605261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1374656632600873401614029 515496237225327525605261)
                ·
                  refine ⟨193311088959497822101973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515496237225327525605261 193311088959497822101973)
                  ·
                    rfl

theorem cell21_847062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_847062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847062 prefixEnd_847062 := by exact prefixLift 847062
  have htrace : WordTrace (prefixWord ++ tailWord_847062) baseStart_847062 baseEnd_847062 := by
    simpa [prefixWord, tailWord_847062, baseEnd_847062] using wordTrace_append hprefix tailTrace_847062
  have hstable : (prefixWord ++ tailWord_847062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847062).length < 2 ^ (prefixWord ++ tailWord_847062).sum := by decide
  have hdescent : baseEnd_847062 < baseStart_847062 := by decide
  rcases family_descends (prefixWord ++ tailWord_847062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847087 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 5]
def baseStart_847087 : Nat := 118140960795 + 847087 * 2 ^ 59
def prefixEnd_847087 : Nat := 4983230072969 + 3 ^ 40 * 847087 * 2
def baseEnd_847087 : Nat := 193316794300103334185255

theorem tailTrace_847087 : CollatzResearch.WordTrace tailWord_847087 prefixEnd_847087 193316794300103334185255 := by
  unfold tailWord_847087
  simp only [CollatzResearch.WordTrace]
  refine ⟨30895801082155944786867515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20597200721437296524578343 30895801082155944786867515)
  ·
    refine ⟨46343701623233917180301273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30895801082155944786867515 46343701623233917180301273)
    ·
      refine ⟨34757776217425437885225955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46343701623233917180301273 34757776217425437885225955)
      ·
        refine ⟨52136664326138156827838933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34757776217425437885225955 52136664326138156827838933)
        ·
          refine ⟨1221953070143863050652475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 52136664326138156827838933 1221953070143863050652475)
          ·
            refine ⟨1832929605215794575978713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221953070143863050652475 1832929605215794575978713)
            ·
              refine ⟨1374697203911845931984035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832929605215794575978713 1374697203911845931984035)
              ·
                refine ⟨2062045805867768897976053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374697203911845931984035 2062045805867768897976053)
                ·
                  refine ⟨193316794300103334185255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2062045805867768897976053 193316794300103334185255)
                  ·
                    rfl

theorem cell21_847087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 5].length) (baseStart_847087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847087 prefixEnd_847087 := by exact prefixLift 847087
  have htrace : WordTrace (prefixWord ++ tailWord_847087) baseStart_847087 baseEnd_847087 := by
    simpa [prefixWord, tailWord_847087, baseEnd_847087] using wordTrace_append hprefix tailTrace_847087
  have hstable : (prefixWord ++ tailWord_847087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847087).length < 2 ^ (prefixWord ++ tailWord_847087).sum := by decide
  have hdescent : baseEnd_847087 < baseStart_847087 := by decide
  rcases family_descends (prefixWord ++ tailWord_847087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847115 : List Nat := [1, 1, 1, 1, 5, 4, 1, 7]
def baseStart_847115 : Nat := 118140960795 + 847115 * 2 ^ 59
def prefixEnd_847115 : Nat := 4983230072969 + 3 ^ 40 * 847115 * 2
def baseEnd_847115 : Nat := 64441061427193835906177

theorem tailTrace_847115 : CollatzResearch.WordTrace tailWord_847115 prefixEnd_847115 64441061427193835906177 := by
  unfold tailWord_847115
  simp only [CollatzResearch.WordTrace]
  refine ⟨30896822326054505568886799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20597881550703003712591199 30896822326054505568886799)
  ·
    refine ⟨46345233489081758353330199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30896822326054505568886799 46345233489081758353330199)
    ·
      refine ⟨69517850233622637529995299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46345233489081758353330199 69517850233622637529995299)
      ·
        refine ⟨104276775350433956294992949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69517850233622637529995299 104276775350433956294992949)
        ·
          refine ⟨9775947689103183402655589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104276775350433956294992949 9775947689103183402655589)
          ·
            refine ⟨1832990191706846887997923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9775947689103183402655589 1832990191706846887997923)
            ·
              refine ⟨2749485287560270331996885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832990191706846887997923 2749485287560270331996885)
              ·
                refine ⟨64441061427193835906177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2749485287560270331996885 64441061427193835906177)
                ·
                  rfl

theorem cell21_847115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 7].length) (baseStart_847115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847115 prefixEnd_847115 := by exact prefixLift 847115
  have htrace : WordTrace (prefixWord ++ tailWord_847115) baseStart_847115 baseEnd_847115 := by
    simpa [prefixWord, tailWord_847115, baseEnd_847115] using wordTrace_append hprefix tailTrace_847115
  have hstable : (prefixWord ++ tailWord_847115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847115).length < 2 ^ (prefixWord ++ tailWord_847115).sum := by decide
  have hdescent : baseEnd_847115 < baseStart_847115 := by decide
  rcases family_descends (prefixWord ++ tailWord_847115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847149 : List Nat := [1, 5, 3, 1, 1, 2, 2, 6]
def baseStart_847149 : Nat := 118140960795 + 847149 * 2 ^ 59
def prefixEnd_847149 : Nat := 4983230072969 + 3 ^ 40 * 847149 * 2
def baseEnd_847149 : Nat := 64443647848268334717265

theorem tailTrace_847149 : CollatzResearch.WordTrace tailWord_847149 prefixEnd_847149 64443647848268334717265 := by
  unfold tailWord_847149
  simp only [CollatzResearch.WordTrace]
  refine ⟨30898062407931329375624501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20598708271954219583749667 30898062407931329375624501)
  ·
    refine ⟨2896693350743562128964797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30898062407931329375624501 2896693350743562128964797)
    ·
      refine ⟨1086260006528835798361799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2896693350743562128964797 1086260006528835798361799)
      ·
        refine ⟨1629390009793253697542699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086260006528835798361799 1629390009793253697542699)
        ·
          refine ⟨2444085014689880546314049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629390009793253697542699 2444085014689880546314049)
          ·
            refine ⟨1833063761017410409735537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2444085014689880546314049 1833063761017410409735537)
            ·
              refine ⟨1374797820763057807301653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1833063761017410409735537 1374797820763057807301653)
              ·
                refine ⟨64443647848268334717265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1374797820763057807301653 64443647848268334717265)
                ·
                  rfl

theorem cell21_847149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 6].length) (baseStart_847149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847149 prefixEnd_847149 := by exact prefixLift 847149
  have htrace : WordTrace (prefixWord ++ tailWord_847149) baseStart_847149 baseEnd_847149 := by
    simpa [prefixWord, tailWord_847149, baseEnd_847149] using wordTrace_append hprefix tailTrace_847149
  have hstable : (prefixWord ++ tailWord_847149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847149).length < 2 ^ (prefixWord ++ tailWord_847149).sum := by decide
  have hdescent : baseEnd_847149 < baseStart_847149 := by decide
  rcases family_descends (prefixWord ++ tailWord_847149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847239 : List Nat := [1, 1, 4, 2, 2, 2, 1, 5, 3]
def baseStart_847239 : Nat := 118140960795 + 847239 * 2 ^ 59
def prefixEnd_847239 : Nat := 4983230072969 + 3 ^ 40 * 847239 * 2
def baseEnd_847239 : Nat := 193351482770984847651611

theorem tailTrace_847239 : CollatzResearch.WordTrace tailWord_847239 prefixEnd_847239 193351482770984847651611 := by
  unfold tailWord_847239
  simp only [CollatzResearch.WordTrace]
  refine ⟨30901344977605274746400771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20600896651736849830933847 30901344977605274746400771)
  ·
    refine ⟨46352017466407912119601157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30901344977605274746400771 46352017466407912119601157)
    ·
      refine ⟨8691003274951483522425217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46352017466407912119601157 8691003274951483522425217)
      ·
        refine ⟨6518252456213612641818913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8691003274951483522425217 6518252456213612641818913)
        ·
          refine ⟨4888689342160209481364185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6518252456213612641818913 4888689342160209481364185)
          ·
            refine ⟨3666517006620157111023139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4888689342160209481364185 3666517006620157111023139)
            ·
              refine ⟨5499775509930235666534709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3666517006620157111023139 5499775509930235666534709)
              ·
                refine ⟨515603954055959593737629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5499775509930235666534709 515603954055959593737629)
                ·
                  refine ⟨193351482770984847651611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515603954055959593737629 193351482770984847651611)
                  ·
                    rfl

theorem cell21_847239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 3].length) (baseStart_847239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847239 prefixEnd_847239 := by exact prefixLift 847239
  have htrace : WordTrace (prefixWord ++ tailWord_847239) baseStart_847239 baseEnd_847239 := by
    simpa [prefixWord, tailWord_847239, baseEnd_847239] using wordTrace_append hprefix tailTrace_847239
  have hstable : (prefixWord ++ tailWord_847239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847239).length < 2 ^ (prefixWord ++ tailWord_847239).sum := by decide
  have hdescent : baseEnd_847239 < baseStart_847239 := by decide
  rcases family_descends (prefixWord ++ tailWord_847239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847253 : List Nat := [1, 3, 2, 1, 1, 2, 5, 2, 4]
def baseStart_847253 : Nat := 118140960795 + 847253 * 2 ^ 59
def prefixEnd_847253 : Nat := 4983230072969 + 3 ^ 40 * 847253 * 2
def baseEnd_847253 : Nat := 193354677761723934418249

theorem tailTrace_847253 : CollatzResearch.WordTrace tailWord_847253 prefixEnd_847253 193354677761723934418249 := by
  unfold tailWord_847253
  simp only [CollatzResearch.WordTrace]
  refine ⟨30901855599554555137410413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20601237066369703424940275 30901855599554555137410413)
  ·
    refine ⟨11588195849832958176528905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30901855599554555137410413 11588195849832958176528905)
    ·
      refine ⟨8691146887374718632396679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11588195849832958176528905 8691146887374718632396679)
      ·
        refine ⟨13036720331062077948595019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8691146887374718632396679 13036720331062077948595019)
        ·
          refine ⟨19555080496593116922892529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13036720331062077948595019 19555080496593116922892529)
          ·
            refine ⟨14666310372444837692169397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19555080496593116922892529 14666310372444837692169397)
            ·
              refine ⟨1374966597416703533640881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14666310372444837692169397 1374966597416703533640881)
              ·
                refine ⟨1031224948062527650230661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1374966597416703533640881 1031224948062527650230661)
                ·
                  refine ⟨193354677761723934418249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1031224948062527650230661 193354677761723934418249)
                  ·
                    rfl

theorem cell21_847253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_847253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847253 prefixEnd_847253 := by exact prefixLift 847253
  have htrace : WordTrace (prefixWord ++ tailWord_847253) baseStart_847253 baseEnd_847253 := by
    simpa [prefixWord, tailWord_847253, baseEnd_847253] using wordTrace_append hprefix tailTrace_847253
  have hstable : (prefixWord ++ tailWord_847253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847253).length < 2 ^ (prefixWord ++ tailWord_847253).sum := by decide
  have hdescent : baseEnd_847253 < baseStart_847253 := by decide
  rcases family_descends (prefixWord ++ tailWord_847253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847329 : List Nat := [1, 2, 3, 1, 2, 4, 1, 3, 4]
def baseStart_847329 : Nat := 118140960795 + 847329 * 2 ^ 59
def prefixEnd_847329 : Nat := 4983230072969 + 3 ^ 40 * 847329 * 2
def baseEnd_847329 : Nat := 193372021997164691151427

theorem tailTrace_847329 : CollatzResearch.WordTrace tailWord_847329 prefixEnd_847329 193372021997164691151427 := by
  unfold tailWord_847329
  simp only [CollatzResearch.WordTrace]
  refine ⟨30904627547279220117177041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20603085031519480078118027 30904627547279220117177041)
  ·
    refine ⟨23178470660459415087882781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30904627547279220117177041 23178470660459415087882781)
    ·
      refine ⟨8691926497672280657956043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23178470660459415087882781 8691926497672280657956043)
      ·
        refine ⟨13037889746508420986934065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8691926497672280657956043 13037889746508420986934065)
        ·
          refine ⟨9778417309881315740200549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13037889746508420986934065 9778417309881315740200549)
          ·
            refine ⟨1833453245602746701287603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9778417309881315740200549 1833453245602746701287603)
            ·
              refine ⟨2750179868404120051931405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833453245602746701287603 2750179868404120051931405)
              ·
                refine ⟨1031317450651545019474277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2750179868404120051931405 1031317450651545019474277)
                ·
                  refine ⟨193372021997164691151427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1031317450651545019474277 193372021997164691151427)
                  ·
                    rfl

theorem cell21_847329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_847329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847329 prefixEnd_847329 := by exact prefixLift 847329
  have htrace : WordTrace (prefixWord ++ tailWord_847329) baseStart_847329 baseEnd_847329 := by
    simpa [prefixWord, tailWord_847329, baseEnd_847329] using wordTrace_append hprefix tailTrace_847329
  have hstable : (prefixWord ++ tailWord_847329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847329).length < 2 ^ (prefixWord ++ tailWord_847329).sum := by decide
  have hdescent : baseEnd_847329 < baseStart_847329 := by decide
  rcases family_descends (prefixWord ++ tailWord_847329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847453 : List Nat := [1, 4, 4, 2, 1, 1, 1, 7]
def baseStart_847453 : Nat := 118140960795 + 847453 * 2 ^ 59
def prefixEnd_847453 : Nat := 4983230072969 + 3 ^ 40 * 847453 * 2
def baseEnd_847453 : Nat := 64466773495522677028169

theorem tailTrace_847453 : CollatzResearch.WordTrace tailWord_847453 prefixEnd_847453 64466773495522677028169 := by
  unfold tailWord_847453
  simp only [CollatzResearch.WordTrace]
  refine ⟨30909150198829989294691013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20606100132553326196460675 30909150198829989294691013)
  ·
    refine ⟨5795465662280622992754565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30909150198829989294691013 5795465662280622992754565)
    ·
      refine ⟨1086649811677616811141481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5795465662280622992754565 1086649811677616811141481)
      ·
        refine ⟨814987358758212608356111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1086649811677616811141481 814987358758212608356111)
        ·
          refine ⟨1222481038137318912534167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814987358758212608356111 1222481038137318912534167)
          ·
            refine ⟨1833721557205978368801251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222481038137318912534167 1833721557205978368801251)
            ·
              refine ⟨2750582335808967553201877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833721557205978368801251 2750582335808967553201877)
              ·
                refine ⟨64466773495522677028169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2750582335808967553201877 64466773495522677028169)
                ·
                  rfl

theorem cell21_847453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 7].length) (baseStart_847453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847453 prefixEnd_847453 := by exact prefixLift 847453
  have htrace : WordTrace (prefixWord ++ tailWord_847453) baseStart_847453 baseEnd_847453 := by
    simpa [prefixWord, tailWord_847453, baseEnd_847453] using wordTrace_append hprefix tailTrace_847453
  have hstable : (prefixWord ++ tailWord_847453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847453).length < 2 ^ (prefixWord ++ tailWord_847453).sum := by decide
  have hdescent : baseEnd_847453 < baseStart_847453 := by decide
  rcases family_descends (prefixWord ++ tailWord_847453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847495 : List Nat := [1, 1, 4, 2, 1, 4, 2, 6]
def baseStart_847495 : Nat := 118140960795 + 847495 * 2 ^ 59
def prefixEnd_847495 : Nat := 4983230072969 + 3 ^ 40 * 847495 * 2
def baseEnd_847495 : Nat := 64469968486261763794807

theorem tailTrace_847495 : CollatzResearch.WordTrace tailWord_847495 prefixEnd_847495 64469968486261763794807 := by
  unfold tailWord_847495
  simp only [CollatzResearch.WordTrace]
  refine ⟨30910682064677830467719939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20607121376451886978479959 30910682064677830467719939)
  ·
    refine ⟨46366023097016745701579909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30910682064677830467719939 46366023097016745701579909)
    ·
      refine ⟨8693629330690639819046233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46366023097016745701579909 8693629330690639819046233)
      ·
        refine ⟨6520221998017979864284675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8693629330690639819046233 6520221998017979864284675)
        ·
          refine ⟨9780332997026969796427013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6520221998017979864284675 9780332997026969796427013)
          ·
            refine ⟨1833812436942556836830065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9780332997026969796427013 1833812436942556836830065)
            ·
              refine ⟨1375359327706917627622549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1833812436942556836830065 1375359327706917627622549)
              ·
                refine ⟨64469968486261763794807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1375359327706917627622549 64469968486261763794807)
                ·
                  rfl

theorem cell21_847495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 6].length) (baseStart_847495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847495 prefixEnd_847495 := by exact prefixLift 847495
  have htrace : WordTrace (prefixWord ++ tailWord_847495) baseStart_847495 baseEnd_847495 := by
    simpa [prefixWord, tailWord_847495, baseEnd_847495] using wordTrace_append hprefix tailTrace_847495
  have hstable : (prefixWord ++ tailWord_847495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847495).length < 2 ^ (prefixWord ++ tailWord_847495).sum := by decide
  have hdescent : baseEnd_847495 < baseStart_847495 := by decide
  rcases family_descends (prefixWord ++ tailWord_847495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847498 : List Nat := [3, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_847498 : Nat := 118140960795 + 847498 * 2 ^ 59
def prefixEnd_847498 : Nat := 4983230072969 + 3 ^ 40 * 847498 * 2
def baseEnd_847498 : Nat := 193410590099657952834415

theorem tailTrace_847498 : CollatzResearch.WordTrace tailWord_847498 prefixEnd_847498 193410590099657952834415 := by
  unfold tailWord_847498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7727697870916740495019787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20607194322444641320052765 7727697870916740495019787)
  ·
    refine ⟨11591546806375110742529681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7727697870916740495019787 11591546806375110742529681)
    ·
      refine ⟨8693660104781333056897261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11591546806375110742529681 8693660104781333056897261)
      ·
        refine ⟨3260122539292999896336473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8693660104781333056897261 3260122539292999896336473)
        ·
          refine ⟨2445091904469749922252355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3260122539292999896336473 2445091904469749922252355)
          ·
            refine ⟨3667637856704624883378533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445091904469749922252355 3667637856704624883378533)
            ·
              refine ⟨687682098132117165633475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3667637856704624883378533 687682098132117165633475)
              ·
                refine ⟨1031523147198175748450213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687682098132117165633475 1031523147198175748450213)
                ·
                  refine ⟨193410590099657952834415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1031523147198175748450213 193410590099657952834415)
                  ·
                    rfl

theorem cell21_847498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_847498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847498 prefixEnd_847498 := by exact prefixLift 847498
  have htrace : WordTrace (prefixWord ++ tailWord_847498) baseStart_847498 baseEnd_847498 := by
    simpa [prefixWord, tailWord_847498, baseEnd_847498] using wordTrace_append hprefix tailTrace_847498
  have hstable : (prefixWord ++ tailWord_847498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847498).length < 2 ^ (prefixWord ++ tailWord_847498).sum := by decide
  have hdescent : baseEnd_847498 < baseStart_847498 := by decide
  rcases family_descends (prefixWord ++ tailWord_847498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847509 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 5]
def baseStart_847509 : Nat := 118140960795 + 847509 * 2 ^ 59
def prefixEnd_847509 : Nat := 4983230072969 + 3 ^ 40 * 847509 * 2
def baseEnd_847509 : Nat := 193413100449524378151059

theorem tailTrace_847509 : CollatzResearch.WordTrace tailWord_847509 prefixEnd_847509 193413100449524378151059 := by
  unfold tailWord_847509
  simp only [CollatzResearch.WordTrace]
  refine ⟨30911192686627110858729581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20607461791084740572486387 30911192686627110858729581)
  ·
    refine ⟨11591697257485166572023593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30911192686627110858729581 11591697257485166572023593)
    ·
      refine ⟨8693772943113874929017695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11591697257485166572023593 8693772943113874929017695)
      ·
        refine ⟨13040659414670812393526543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8693772943113874929017695 13040659414670812393526543)
        ·
          refine ⟨19560989122006218590289815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13040659414670812393526543 19560989122006218590289815)
          ·
            refine ⟨29341483683009327885434723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19560989122006218590289815 29341483683009327885434723)
            ·
              refine ⟨44012225524513991828152085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29341483683009327885434723 44012225524513991828152085)
              ·
                refine ⟨2063073071461593366944629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44012225524513991828152085 2063073071461593366944629)
                ·
                  refine ⟨193413100449524378151059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2063073071461593366944629 193413100449524378151059)
                  ·
                    rfl

theorem cell21_847509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_847509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847509 prefixEnd_847509 := by exact prefixLift 847509
  have htrace : WordTrace (prefixWord ++ tailWord_847509) baseStart_847509 baseEnd_847509 := by
    simpa [prefixWord, tailWord_847509, baseEnd_847509] using wordTrace_append hprefix tailTrace_847509
  have hstable : (prefixWord ++ tailWord_847509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847509).length < 2 ^ (prefixWord ++ tailWord_847509).sum := by decide
  have hdescent : baseEnd_847509 < baseStart_847509 := by decide
  rcases family_descends (prefixWord ++ tailWord_847509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847543 : List Nat := [1, 1, 3, 1, 5, 2, 1, 4, 3]
def baseStart_847543 : Nat := 118140960795 + 847543 * 2 ^ 59
def prefixEnd_847543 : Nat := 4983230072969 + 3 ^ 40 * 847543 * 2
def baseEnd_847543 : Nat := 193420859712747874584323

theorem tailTrace_847543 : CollatzResearch.WordTrace tailWord_847543 prefixEnd_847543 193420859712747874584323 := by
  unfold tailWord_847543
  simp only [CollatzResearch.WordTrace]
  refine ⟨30912432768503934665467283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20608288512335956443644855 30912432768503934665467283)
  ·
    refine ⟨46368649152755901998200925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30912432768503934665467283 46368649152755901998200925)
    ·
      refine ⟨17388243432283463249325347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46368649152755901998200925 17388243432283463249325347)
      ·
        refine ⟨26082365148425194873988021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17388243432283463249325347 26082365148425194873988021)
        ·
          refine ⟨2445221732664862019436377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26082365148425194873988021 2445221732664862019436377)
          ·
            refine ⟨1833916299498646514577283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2445221732664862019436377 1833916299498646514577283)
            ·
              refine ⟨2750874449247969771865925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833916299498646514577283 2750874449247969771865925)
              ·
                refine ⟨515788959233994332224861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2750874449247969771865925 515788959233994332224861)
                ·
                  refine ⟨193420859712747874584323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515788959233994332224861 193420859712747874584323)
                  ·
                    rfl

theorem cell21_847543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 3].length) (baseStart_847543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847543 prefixEnd_847543 := by exact prefixLift 847543
  have htrace : WordTrace (prefixWord ++ tailWord_847543) baseStart_847543 baseEnd_847543 := by
    simpa [prefixWord, tailWord_847543, baseEnd_847543] using wordTrace_append hprefix tailTrace_847543
  have hstable : (prefixWord ++ tailWord_847543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847543).length < 2 ^ (prefixWord ++ tailWord_847543).sum := by decide
  have hdescent : baseEnd_847543 < baseStart_847543 := by decide
  rcases family_descends (prefixWord ++ tailWord_847543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847591 : List Nat := [1, 1, 5, 4, 1, 2, 1, 2, 4]
def baseStart_847591 : Nat := 118140960795 + 847591 * 2 ^ 59
def prefixEnd_847591 : Nat := 4983230072969 + 3 ^ 40 * 847591 * 2
def baseEnd_847591 : Nat := 193431813966710457784225

theorem tailTrace_847591 : CollatzResearch.WordTrace tailWord_847591 prefixEnd_847591 193431813966710457784225 := by
  unfold tailWord_847591
  simp only [CollatzResearch.WordTrace]
  refine ⟨30914183472330038863214627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20609455648220025908809751 30914183472330038863214627)
  ·
    refine ⟨46371275208495058294821941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30914183472330038863214627 46371275208495058294821941)
    ·
      refine ⟨4347307050796411715139557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46371275208495058294821941 4347307050796411715139557)
      ·
        refine ⟨815120072024327196588667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4347307050796411715139557 815120072024327196588667)
        ·
          refine ⟨1222680108036490794883001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815120072024327196588667 1222680108036490794883001)
          ·
            refine ⟨917010081027368096162251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1222680108036490794883001 917010081027368096162251)
            ·
              refine ⟨1375515121541052144243377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917010081027368096162251 1375515121541052144243377)
              ·
                refine ⟨1031636341155789108182533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1375515121541052144243377 1031636341155789108182533)
                ·
                  refine ⟨193431813966710457784225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1031636341155789108182533 193431813966710457784225)
                  ·
                    rfl

theorem cell21_847591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 4].length) (baseStart_847591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847591 prefixEnd_847591 := by exact prefixLift 847591
  have htrace : WordTrace (prefixWord ++ tailWord_847591) baseStart_847591 baseEnd_847591 := by
    simpa [prefixWord, tailWord_847591, baseEnd_847591] using wordTrace_append hprefix tailTrace_847591
  have hstable : (prefixWord ++ tailWord_847591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847591).length < 2 ^ (prefixWord ++ tailWord_847591).sum := by decide
  have hdescent : baseEnd_847591 < baseStart_847591 := by decide
  rcases family_descends (prefixWord ++ tailWord_847591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847602 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_847602 : Nat := 118140960795 + 847602 * 2 ^ 59
def prefixEnd_847602 : Nat := 4983230072969 + 3 ^ 40 * 847602 * 2
def baseEnd_847602 : Nat := 193434324316576883100869

theorem tailTrace_847602 : CollatzResearch.WordTrace tailWord_847602 prefixEnd_847602 193434324316576883100869 := by
  unfold tailWord_847602
  simp only [CollatzResearch.WordTrace]
  refine ⟨7728646168822546935466265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20609723116860125161243373 7728646168822546935466265)
  ·
    refine ⟨5796484626616910201599699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7728646168822546935466265 5796484626616910201599699)
    ·
      refine ⟨8694726939925365302399549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5796484626616910201599699 8694726939925365302399549)
      ·
        refine ⟨3260522602472011988399831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8694726939925365302399549 3260522602472011988399831)
        ·
          refine ⟨4890783903708017982599747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3260522602472011988399831 4890783903708017982599747)
          ·
            refine ⟨7336175855562026973899621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4890783903708017982599747 7336175855562026973899621)
            ·
              refine ⟨1375532972917880057606179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7336175855562026973899621 1375532972917880057606179)
              ·
                refine ⟨2063299459376820086409269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375532972917880057606179 2063299459376820086409269)
                ·
                  refine ⟨193434324316576883100869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2063299459376820086409269 193434324316576883100869)
                  ·
                    rfl

theorem cell21_847602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_847602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847602 prefixEnd_847602 := by exact prefixLift 847602
  have htrace : WordTrace (prefixWord ++ tailWord_847602) baseStart_847602 baseEnd_847602 := by
    simpa [prefixWord, tailWord_847602, baseEnd_847602] using wordTrace_append hprefix tailTrace_847602
  have hstable : (prefixWord ++ tailWord_847602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847602).length < 2 ^ (prefixWord ++ tailWord_847602).sum := by decide
  have hdescent : baseEnd_847602 < baseStart_847602 := by decide
  rcases family_descends (prefixWord ++ tailWord_847602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847667 : List Nat := [1, 1, 1, 2, 8, 1, 2, 1, 4]
def baseStart_847667 : Nat := 118140960795 + 847667 * 2 ^ 59
def prefixEnd_847667 : Nat := 4983230072969 + 3 ^ 40 * 847667 * 2
def baseEnd_847667 : Nat := 193449158202151214517403

theorem tailTrace_847667 : CollatzResearch.WordTrace tailWord_847667 prefixEnd_847667 193449158202151214517403 := by
  unfold tailWord_847667
  simp only [CollatzResearch.WordTrace]
  refine ⟨30916955420054703842981255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20611303613369802561987503 30916955420054703842981255)
  ·
    refine ⟨46375433130082055764471883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30916955420054703842981255 46375433130082055764471883)
    ·
      refine ⟨69563149695123083646707825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46375433130082055764471883 69563149695123083646707825)
      ·
        refine ⟨52172362271342312735030869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69563149695123083646707825 52172362271342312735030869)
        ·
          refine ⟨611394870367292727363643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 52172362271342312735030869 611394870367292727363643)
          ·
            refine ⟨917092305550939091045465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611394870367292727363643 917092305550939091045465)
            ·
              refine ⟨687819229163204318284099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917092305550939091045465 687819229163204318284099)
              ·
                refine ⟨1031728843744806477426149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687819229163204318284099 1031728843744806477426149)
                ·
                  refine ⟨193449158202151214517403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1031728843744806477426149 193449158202151214517403)
                  ·
                    rfl

theorem cell21_847667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 4].length) (baseStart_847667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847667 prefixEnd_847667 := by exact prefixLift 847667
  have htrace : WordTrace (prefixWord ++ tailWord_847667) baseStart_847667 baseEnd_847667 := by
    simpa [prefixWord, tailWord_847667, baseEnd_847667] using wordTrace_append hprefix tailTrace_847667
  have hstable : (prefixWord ++ tailWord_847667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847667).length < 2 ^ (prefixWord ++ tailWord_847667).sum := by decide
  have hdescent : baseEnd_847667 < baseStart_847667 := by decide
  rcases family_descends (prefixWord ++ tailWord_847667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847712 : List Nat := [2, 1, 1, 3, 3, 4, 2, 2, 3]
def baseStart_847712 : Nat := 118140960795 + 847712 * 2 ^ 59
def prefixEnd_847712 : Nat := 4983230072969 + 3 ^ 40 * 847712 * 2
def baseEnd_847712 : Nat := 193459427815241136267311

theorem tailTrace_847712 : CollatzResearch.WordTrace tailWord_847712 prefixEnd_847712 193459427815241136267311 := by
  unfold tailWord_847712
  simp only [CollatzResearch.WordTrace]
  refine ⟨15459298352445838264184695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20612397803261117685579593 15459298352445838264184695)
  ·
    refine ⟨23188947528668757396277043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15459298352445838264184695 23188947528668757396277043)
    ·
      refine ⟨34783421293003136094415565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23188947528668757396277043 34783421293003136094415565)
      ·
        refine ⟨13043782984876176035405837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34783421293003136094415565 13043782984876176035405837)
        ·
          refine ⟨4891418619328566013277189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13043782984876176035405837 4891418619328566013277189)
          ·
            refine ⟨917140991124106127489473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4891418619328566013277189 917140991124106127489473)
            ·
              refine ⟨687855743343079595617105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917140991124106127489473 687855743343079595617105)
              ·
                refine ⟨515891807507309696712829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687855743343079595617105 515891807507309696712829)
                ·
                  refine ⟨193459427815241136267311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515891807507309696712829 193459427815241136267311)
                  ·
                    rfl

theorem cell21_847712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 3].length) (baseStart_847712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847712 prefixEnd_847712 := by exact prefixLift 847712
  have htrace : WordTrace (prefixWord ++ tailWord_847712) baseStart_847712 baseEnd_847712 := by
    simpa [prefixWord, tailWord_847712, baseEnd_847712] using wordTrace_append hprefix tailTrace_847712
  have hstable : (prefixWord ++ tailWord_847712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847712).length < 2 ^ (prefixWord ++ tailWord_847712).sum := by decide
  have hdescent : baseEnd_847712 < baseStart_847712 := by decide
  rcases family_descends (prefixWord ++ tailWord_847712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847737 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 5]
def baseStart_847737 : Nat := 118140960795 + 847737 * 2 ^ 59
def prefixEnd_847737 : Nat := 4983230072969 + 3 ^ 40 * 847737 * 2
def baseEnd_847737 : Nat := 193465133155846648350593

theorem tailTrace_847737 : CollatzResearch.WordTrace tailWord_847737 prefixEnd_847737 193465133155846648350593 := by
  unfold tailWord_847737
  simp only [CollatzResearch.WordTrace]
  refine ⟨30919508529801105798029465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20613005686534070532019643 30919508529801105798029465)
  ·
    refine ⟨23189631397350829348522099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30919508529801105798029465 23189631397350829348522099)
    ·
      refine ⟨34784447096026244022783149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23189631397350829348522099 34784447096026244022783149)
      ·
        refine ⟨13044167661009841508543681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34784447096026244022783149 13044167661009841508543681)
        ·
          refine ⟨9783125745757381131407761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13044167661009841508543681 9783125745757381131407761)
          ·
            refine ⟨7337344309318035848555821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9783125745757381131407761 7337344309318035848555821)
            ·
              refine ⟨2751504115994263443208433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7337344309318035848555821 2751504115994263443208433)
              ·
                refine ⟨2063628086995697582406325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2751504115994263443208433 2063628086995697582406325)
                ·
                  refine ⟨193465133155846648350593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2063628086995697582406325 193465133155846648350593)
                  ·
                    rfl

theorem cell21_847737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_847737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847737 prefixEnd_847737 := by exact prefixLift 847737
  have htrace : WordTrace (prefixWord ++ tailWord_847737) baseStart_847737 baseEnd_847737 := by
    simpa [prefixWord, tailWord_847737, baseEnd_847737] using wordTrace_append hprefix tailTrace_847737
  have hstable : (prefixWord ++ tailWord_847737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847737).length < 2 ^ (prefixWord ++ tailWord_847737).sum := by decide
  have hdescent : baseEnd_847737 < baseStart_847737 := by decide
  rcases family_descends (prefixWord ++ tailWord_847737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847844 : List Nat := [2, 3, 1, 1, 1, 1, 5, 3, 4]
def baseStart_847844 : Nat := 118140960795 + 847844 * 2 ^ 59
def prefixEnd_847844 : Nat := 4983230072969 + 3 ^ 40 * 847844 * 2
def baseEnd_847844 : Nat := 193489552013638240067041

theorem tailTrace_847844 : CollatzResearch.WordTrace tailWord_847844 prefixEnd_847844 193489552013638240067041 := by
  unfold tailWord_847844
  simp only [CollatzResearch.WordTrace]
  refine ⟨15461705570206731536087293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20615607426942308714783057 15461705570206731536087293)
  ·
    refine ⟨5798139588827524326032735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15461705570206731536087293 5798139588827524326032735)
    ·
      refine ⟨8697209383241286489049103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5798139588827524326032735 8697209383241286489049103)
      ·
        refine ⟨13045814074861929733573655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8697209383241286489049103 13045814074861929733573655)
        ·
          refine ⟨19568721112292894600360483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13045814074861929733573655 19568721112292894600360483)
          ·
            refine ⟨29353081668439341900540725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19568721112292894600360483 29353081668439341900540725)
            ·
              refine ⟨2751851406416188303175693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29353081668439341900540725 2751851406416188303175693)
              ·
                refine ⟨1031944277406070613690885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2751851406416188303175693 1031944277406070613690885)
                ·
                  refine ⟨193489552013638240067041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1031944277406070613690885 193489552013638240067041)
                  ·
                    rfl

theorem cell21_847844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_847844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847844 prefixEnd_847844 := by exact prefixLift 847844
  have htrace : WordTrace (prefixWord ++ tailWord_847844) baseStart_847844 baseEnd_847844 := by
    simpa [prefixWord, tailWord_847844, baseEnd_847844] using wordTrace_append hprefix tailTrace_847844
  have hstable : (prefixWord ++ tailWord_847844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847844).length < 2 ^ (prefixWord ++ tailWord_847844).sum := by decide
  have hdescent : baseEnd_847844 < baseStart_847844 := by decide
  rcases family_descends (prefixWord ++ tailWord_847844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847872 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 9]
def baseStart_847872 : Nat := 118140960795 + 847872 * 2 ^ 59
def prefixEnd_847872 : Nat := 4983230072969 + 3 ^ 40 * 847872 * 2
def baseEnd_847872 : Nat := 193495941995116413600317

theorem tailTrace_847872 : CollatzResearch.WordTrace tailWord_847872 prefixEnd_847872 193495941995116413600317 := by
  unfold tailWord_847872
  simp only [CollatzResearch.WordTrace]
  refine ⟨15462216192156011927096935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20616288256208015902795913 15462216192156011927096935)
  ·
    refine ⟨23193324288234017890645403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15462216192156011927096935 23193324288234017890645403)
    ·
      refine ⟨34789986432351026835968105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23193324288234017890645403 34789986432351026835968105)
      ·
        refine ⟨26092489824263270126976079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34789986432351026835968105 26092489824263270126976079)
        ·
          refine ⟨39138734736394905190464119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26092489824263270126976079 39138734736394905190464119)
          ·
            refine ⟨58708102104592357785696179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39138734736394905190464119 58708102104592357785696179)
            ·
              refine ⟨88062153156888536678544269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58708102104592357785696179 88062153156888536678544269)
              ·
                refine ⟨33023307433833201254454101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88062153156888536678544269 33023307433833201254454101)
                ·
                  refine ⟨193495941995116413600317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33023307433833201254454101 193495941995116413600317)
                  ·
                    rfl

theorem cell21_847872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_847872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847872 prefixEnd_847872 := by exact prefixLift 847872
  have htrace : WordTrace (prefixWord ++ tailWord_847872) baseStart_847872 baseEnd_847872 := by
    simpa [prefixWord, tailWord_847872, baseEnd_847872] using wordTrace_append hprefix tailTrace_847872
  have hstable : (prefixWord ++ tailWord_847872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847872).length < 2 ^ (prefixWord ++ tailWord_847872).sum := by decide
  have hdescent : baseEnd_847872 < baseStart_847872 := by decide
  rcases family_descends (prefixWord ++ tailWord_847872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847937 : List Nat := [1, 2, 5, 1, 2, 1, 3, 2, 4]
def baseStart_847937 : Nat := 118140960795 + 847937 * 2 ^ 59
def prefixEnd_847937 : Nat := 4983230072969 + 3 ^ 40 * 847937 * 2
def baseEnd_847937 : Nat := 193510775880690745016851

theorem tailTrace_847937 : CollatzResearch.WordTrace tailWord_847937 prefixEnd_847937 193510775880690745016851 := by
  unfold tailWord_847937
  simp only [CollatzResearch.WordTrace]
  refine ⟨30926803129076539955310065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20617868752717693303540043 30926803129076539955310065)
  ·
    refine ⟨23195102346807404966482549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30926803129076539955310065 23195102346807404966482549)
    ·
      refine ⟨2174540845013194215607739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23195102346807404966482549 2174540845013194215607739)
      ·
        refine ⟨3261811267519791323411609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2174540845013194215607739 3261811267519791323411609)
        ·
          refine ⟨2446358450639843492558707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3261811267519791323411609 2446358450639843492558707)
          ·
            refine ⟨3669537675959765238838061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446358450639843492558707 3669537675959765238838061)
            ·
              refine ⟨1376076628484911964564273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3669537675959765238838061 1376076628484911964564273)
              ·
                refine ⟨1032057471363683973423205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1376076628484911964564273 1032057471363683973423205)
                ·
                  refine ⟨193510775880690745016851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1032057471363683973423205 193510775880690745016851)
                  ·
                    rfl

theorem cell21_847937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_847937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847937 prefixEnd_847937 := by exact prefixLift 847937
  have htrace : WordTrace (prefixWord ++ tailWord_847937) baseStart_847937 baseEnd_847937 := by
    simpa [prefixWord, tailWord_847937, baseEnd_847937] using wordTrace_append hprefix tailTrace_847937
  have hstable : (prefixWord ++ tailWord_847937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847937).length < 2 ^ (prefixWord ++ tailWord_847937).sum := by decide
  have hdescent : baseEnd_847937 < baseStart_847937 := by decide
  rcases family_descends (prefixWord ++ tailWord_847937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847954 : List Nat := [3, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_847954 : Nat := 118140960795 + 847954 * 2 ^ 59
def prefixEnd_847954 : Nat := 4983230072969 + 3 ^ 40 * 847954 * 2
def baseEnd_847954 : Nat := 193514655512302493233483

theorem tailTrace_847954 : CollatzResearch.WordTrace tailWord_847954 prefixEnd_847954 193514655512302493233483 := by
  unfold tailWord_847954
  simp only [CollatzResearch.WordTrace]
  refine ⟨7731855792503737964669729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20618282113343301239119277 7731855792503737964669729)
  ·
    refine ⟨5798891844377803473502297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7731855792503737964669729 5798891844377803473502297)
    ·
      refine ⟨4349168883283352605126723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5798891844377803473502297 4349168883283352605126723)
      ·
        refine ⟨6523753324925028907690085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4349168883283352605126723 6523753324925028907690085)
        ·
          refine ⟨1223203748423442920191891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6523753324925028907690085 1223203748423442920191891)
          ·
            refine ⟨1834805622635164380287837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223203748423442920191891 1834805622635164380287837)
            ·
              refine ⟨688052108488186642607939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1834805622635164380287837 688052108488186642607939)
              ·
                refine ⟨1032078162732279963911909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688052108488186642607939 1032078162732279963911909)
                ·
                  refine ⟨193514655512302493233483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1032078162732279963911909 193514655512302493233483)
                  ·
                    rfl

theorem cell21_847954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_847954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_847954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_847954 prefixEnd_847954 := by exact prefixLift 847954
  have htrace : WordTrace (prefixWord ++ tailWord_847954) baseStart_847954 baseEnd_847954 := by
    simpa [prefixWord, tailWord_847954, baseEnd_847954] using wordTrace_append hprefix tailTrace_847954
  have hstable : (prefixWord ++ tailWord_847954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847954).length < 2 ^ (prefixWord ++ tailWord_847954).sum := by decide
  have hdescent : baseEnd_847954 < baseStart_847954 := by decide
  rcases family_descends (prefixWord ++ tailWord_847954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
