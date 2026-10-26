import V185TrunkScan22Chunk036

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_331506 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 6]
def baseStart_331506 : Nat := 118140960795 + 331506 * 2 ^ 59
def prefixEnd_331506 : Nat := 4983230072969 + 3 ^ 40 * 331506 * 2
def baseEnd_331506 : Nat := 37827092855441158877875

theorem tailTrace_331506 : CollatzResearch.WordTrace tailWord_331506 prefixEnd_331506 37827092855441158877875 := by
  unfold tailWord_331506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3022754284254463390605593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8060678091345235708281581 3022754284254463390605593)
  ·
    refine ⟨2267065713190847542954195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3022754284254463390605593 2267065713190847542954195)
    ·
      refine ⟨3400598569786271314431293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267065713190847542954195 3400598569786271314431293)
      ·
        refine ⟨1275224463669851742911735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3400598569786271314431293 1275224463669851742911735)
        ·
          refine ⟨1912836695504777614367603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275224463669851742911735 1912836695504777614367603)
          ·
            refine ⟨2869255043257166421551405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912836695504777614367603 2869255043257166421551405)
            ·
              refine ⟨1075970641221437408081777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2869255043257166421551405 1075970641221437408081777)
              ·
                refine ⟨806977980916078056061333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075970641221437408081777 806977980916078056061333)
                ·
                  refine ⟨37827092855441158877875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 806977980916078056061333 37827092855441158877875)
                  ·
                    rfl

theorem cell22_331506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_331506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331506 prefixEnd_331506 := by exact prefixLift 331506
  have htrace : WordTrace (prefixWord ++ tailWord_331506) baseStart_331506 baseEnd_331506 := by
    simpa [prefixWord, tailWord_331506, baseEnd_331506] using wordTrace_append hprefix tailTrace_331506
  have hstable : (prefixWord ++ tailWord_331506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331506).length < 2 ^ (prefixWord ++ tailWord_331506).sum := by decide
  have hdescent : baseEnd_331506 < baseStart_331506 := by decide
  rcases family_descends (prefixWord ++ tailWord_331506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331521 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 1, 5]
def baseStart_331521 : Nat := 118140960795 + 331521 * 2 ^ 59
def prefixEnd_331521 : Nat := 4983230072969 + 3 ^ 40 * 331521 * 2
def baseEnd_331521 : Nat := 113486413372868437508579

theorem tailTrace_331521 : CollatzResearch.WordTrace tailWord_331521 prefixEnd_331521 113486413372868437508579 := by
  unfold tailWord_331521
  simp only [CollatzResearch.WordTrace]
  refine ⟨12091564231963511124218417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8061042821309007416145611 12091564231963511124218417)
  ·
    refine ⟨9068673173972633343163813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12091564231963511124218417 9068673173972633343163813)
    ·
      refine ⟨1700376220119868751843215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9068673173972633343163813 1700376220119868751843215)
      ·
        refine ⟨2550564330179803127764823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1700376220119868751843215 2550564330179803127764823)
        ·
          refine ⟨3825846495269704691647235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550564330179803127764823 3825846495269704691647235)
          ·
            refine ⟨5738769742904557037470853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3825846495269704691647235 5738769742904557037470853)
            ·
              refine ⟨1076019326794604444525785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5738769742904557037470853 1076019326794604444525785)
              ·
                refine ⟨807014495095953333394339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1076019326794604444525785 807014495095953333394339)
                ·
                  refine ⟨1210521742643930000091509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807014495095953333394339 1210521742643930000091509)
                  ·
                    refine ⟨113486413372868437508579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1210521742643930000091509 113486413372868437508579)
                    ·
                      rfl

theorem cell22_331521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_331521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331521 prefixEnd_331521 := by exact prefixLift 331521
  have htrace : WordTrace (prefixWord ++ tailWord_331521) baseStart_331521 baseEnd_331521 := by
    simpa [prefixWord, tailWord_331521, baseEnd_331521] using wordTrace_append hprefix tailTrace_331521
  have hstable : (prefixWord ++ tailWord_331521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331521).length < 2 ^ (prefixWord ++ tailWord_331521).sum := by decide
  have hdescent : baseEnd_331521 < baseStart_331521 := by decide
  rcases family_descends (prefixWord ++ tailWord_331521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331737 : List Nat := [1, 2, 1, 2, 7, 1, 2, 6]
def baseStart_331737 : Nat := 118140960795 + 331737 * 2 ^ 59
def prefixEnd_331737 : Nat := 4983230072969 + 3 ^ 40 * 331737 * 2
def baseEnd_331737 : Nat := 12617817176346208234213

theorem tailTrace_331737 : CollatzResearch.WordTrace tailWord_331737 prefixEnd_331737 12617817176346208234213 := by
  unfold tailWord_331737
  simp only [CollatzResearch.WordTrace]
  refine ⟨12099442399180980014081465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8066294932787320009387643 12099442399180980014081465)
  ·
    refine ⟨9074581799385735010561099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12099442399180980014081465 9074581799385735010561099)
    ·
      refine ⟨13611872699078602515841649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9074581799385735010561099 13611872699078602515841649)
      ·
        refine ⟨10208904524308951886881237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13611872699078602515841649 10208904524308951886881237)
        ·
          refine ⟨239271199788491059848779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10208904524308951886881237 239271199788491059848779)
          ·
            refine ⟨358906799682736589773169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239271199788491059848779 358906799682736589773169)
            ·
              refine ⟨269180099762052442329877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358906799682736589773169 269180099762052442329877)
              ·
                refine ⟨12617817176346208234213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 269180099762052442329877 12617817176346208234213)
                ·
                  rfl

theorem cell22_331737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 6].length) (baseStart_331737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331737 prefixEnd_331737 := by exact prefixLift 331737
  have htrace : WordTrace (prefixWord ++ tailWord_331737) baseStart_331737 baseEnd_331737 := by
    simpa [prefixWord, tailWord_331737, baseEnd_331737] using wordTrace_append hprefix tailTrace_331737
  have hstable : (prefixWord ++ tailWord_331737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331737).length < 2 ^ (prefixWord ++ tailWord_331737).sum := by decide
  have hdescent : baseEnd_331737 < baseStart_331737 := by decide
  rcases family_descends (prefixWord ++ tailWord_331737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331769 : List Nat := [1, 2, 1, 3, 1, 5, 3, 2, 1, 3]
def baseStart_331769 : Nat := 118140960795 + 331769 * 2 ^ 59
def prefixEnd_331769 : Nat := 4983230072969 + 3 ^ 40 * 331769 * 2
def baseEnd_331769 : Nat := 113571308841078457307819

theorem tailTrace_331769 : CollatzResearch.WordTrace tailWord_331769 prefixEnd_331769 113571308841078457307819 := by
  unfold tailWord_331769
  simp only [CollatzResearch.WordTrace]
  refine ⟨12100609535065049479246361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8067073023376699652830907 12100609535065049479246361)
  ·
    refine ⟨9075457151298787109434771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12100609535065049479246361 9075457151298787109434771)
    ·
      refine ⟨13613185726948180664152157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9075457151298787109434771 13613185726948180664152157)
      ·
        refine ⟨5104944647605567749057059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13613185726948180664152157 5104944647605567749057059)
        ·
          refine ⟨7657416971408351623585589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5104944647605567749057059 7657416971408351623585589)
          ·
            refine ⟨717882841069532964711149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7657416971408351623585589 717882841069532964711149)
            ·
              refine ⟨269206065401074861766681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 717882841069532964711149 269206065401074861766681)
              ·
                refine ⟨201904549050806146325011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269206065401074861766681 201904549050806146325011)
                ·
                  refine ⟨302856823576209219487517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201904549050806146325011 302856823576209219487517)
                  ·
                    refine ⟨113571308841078457307819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 302856823576209219487517 113571308841078457307819)
                    ·
                      rfl

theorem cell22_331769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 1, 3].length) (baseStart_331769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331769 prefixEnd_331769 := by exact prefixLift 331769
  have htrace : WordTrace (prefixWord ++ tailWord_331769) baseStart_331769 baseEnd_331769 := by
    simpa [prefixWord, tailWord_331769, baseEnd_331769] using wordTrace_append hprefix tailTrace_331769
  have hstable : (prefixWord ++ tailWord_331769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331769).length < 2 ^ (prefixWord ++ tailWord_331769).sum := by decide
  have hdescent : baseEnd_331769 < baseStart_331769 := by decide
  rcases family_descends (prefixWord ++ tailWord_331769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331795 : List Nat := [1, 1, 1, 2, 1, 4, 5, 2, 1, 4]
def baseStart_331795 : Nat := 118140960795 + 331795 * 2 ^ 59
def prefixEnd_331795 : Nat := 4983230072969 + 3 ^ 40 * 331795 * 2
def baseEnd_331795 : Nat := 113580209172423056157739

theorem tailTrace_331795 : CollatzResearch.WordTrace tailWord_331795 prefixEnd_331795 113580209172423056157739 := by
  unfold tailWord_331795
  simp only [CollatzResearch.WordTrace]
  refine ⟨12101557832970855919692839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8067705221980570613128559 12101557832970855919692839)
  ·
    refine ⟨18152336749456283879539259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12101557832970855919692839 18152336749456283879539259)
    ·
      refine ⟨27228505124184425819308889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18152336749456283879539259 27228505124184425819308889)
      ·
        refine ⟨20421378843138319364481667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27228505124184425819308889 20421378843138319364481667)
        ·
          refine ⟨30632068264707479046722501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20421378843138319364481667 30632068264707479046722501)
          ·
            refine ⟨5743512799632652321260469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30632068264707479046722501 5743512799632652321260469)
            ·
              refine ⟨538454324965561155118169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5743512799632652321260469 538454324965561155118169)
              ·
                refine ⟨403840743724170866338627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538454324965561155118169 403840743724170866338627)
                ·
                  refine ⟨605761115586256299507941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403840743724170866338627 605761115586256299507941)
                  ·
                    refine ⟨113580209172423056157739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 605761115586256299507941 113580209172423056157739)
                    ·
                      rfl

theorem cell22_331795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 4].length) (baseStart_331795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331795 prefixEnd_331795 := by exact prefixLift 331795
  have htrace : WordTrace (prefixWord ++ tailWord_331795) baseStart_331795 baseEnd_331795 := by
    simpa [prefixWord, tailWord_331795, baseEnd_331795] using wordTrace_append hprefix tailTrace_331795
  have hstable : (prefixWord ++ tailWord_331795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331795).length < 2 ^ (prefixWord ++ tailWord_331795).sum := by decide
  have hdescent : baseEnd_331795 < baseStart_331795 := by decide
  rcases family_descends (prefixWord ++ tailWord_331795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331823 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 4, 4]
def baseStart_331823 : Nat := 118140960795 + 331823 * 2 ^ 59
def prefixEnd_331823 : Nat := 4983230072969 + 3 ^ 40 * 331823 * 2
def baseEnd_331823 : Nat := 113589794144640316457653

theorem tailTrace_331823 : CollatzResearch.WordTrace tailWord_331823 prefixEnd_331823 113589794144640316457653 := by
  unfold tailWord_331823
  simp only [CollatzResearch.WordTrace]
  refine ⟨12102579076869416701712123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8068386051246277801141415 12102579076869416701712123)
  ·
    refine ⟨18153868615304125052568185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12102579076869416701712123 18153868615304125052568185)
    ·
      refine ⟨13615401461478093789426139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18153868615304125052568185 13615401461478093789426139)
      ·
        refine ⟨20423102192217140684139209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13615401461478093789426139 20423102192217140684139209)
        ·
          refine ⟨15317326644162855513104407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20423102192217140684139209 15317326644162855513104407)
          ·
            refine ⟨22975989966244283269656611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15317326644162855513104407 22975989966244283269656611)
            ·
              refine ⟨34463984949366424904484917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22975989966244283269656611 34463984949366424904484917)
              ·
                refine ⟨3230998589003102334795461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34463984949366424904484917 3230998589003102334795461)
                ·
                  refine ⟨605812235438081687774149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3230998589003102334795461 605812235438081687774149)
                  ·
                    refine ⟨113589794144640316457653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 605812235438081687774149 113589794144640316457653)
                    ·
                      rfl

theorem cell22_331823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_331823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331823 prefixEnd_331823 := by exact prefixLift 331823
  have htrace : WordTrace (prefixWord ++ tailWord_331823) baseStart_331823 baseEnd_331823 := by
    simpa [prefixWord, tailWord_331823, baseEnd_331823] using wordTrace_append hprefix tailTrace_331823
  have hstable : (prefixWord ++ tailWord_331823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331823).length < 2 ^ (prefixWord ++ tailWord_331823).sum := by decide
  have hdescent : baseEnd_331823 < baseStart_331823 := by decide
  rcases family_descends (prefixWord ++ tailWord_331823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331827 : List Nat := [1, 1, 1, 2, 4, 1, 6, 2, 4]
def baseStart_331827 : Nat := 118140960795 + 331827 * 2 ^ 59
def prefixEnd_331827 : Nat := 4983230072969 + 3 ^ 40 * 331827 * 2
def baseEnd_331827 : Nat := 37863721142128546452547

theorem tailTrace_331827 : CollatzResearch.WordTrace tailWord_331827 prefixEnd_331827 37863721142128546452547 := by
  unfold tailWord_331827
  simp only [CollatzResearch.WordTrace]
  refine ⟨12102724968854925384857735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8068483312569950256571823 12102724968854925384857735)
  ·
    refine ⟨18154087453282388077286603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12102724968854925384857735 18154087453282388077286603)
    ·
      refine ⟨27231131179923582115929905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18154087453282388077286603 27231131179923582115929905)
      ·
        refine ⟨20423348384942686586947429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27231131179923582115929905 20423348384942686586947429)
        ·
          refine ⟨3829377822176753735052643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20423348384942686586947429 3829377822176753735052643)
          ·
            refine ⟨5744066733265130602578965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829377822176753735052643 5744066733265130602578965)
            ·
              refine ⟨269253128121802996995889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5744066733265130602578965 269253128121802996995889)
              ·
                refine ⟨201939846091352247746917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269253128121802996995889 201939846091352247746917)
                ·
                  refine ⟨37863721142128546452547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201939846091352247746917 37863721142128546452547)
                  ·
                    rfl

theorem cell22_331827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 4].length) (baseStart_331827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331827 prefixEnd_331827 := by exact prefixLift 331827
  have htrace : WordTrace (prefixWord ++ tailWord_331827) baseStart_331827 baseEnd_331827 := by
    simpa [prefixWord, tailWord_331827, baseEnd_331827] using wordTrace_append hprefix tailTrace_331827
  have hstable : (prefixWord ++ tailWord_331827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331827).length < 2 ^ (prefixWord ++ tailWord_331827).sum := by decide
  have hdescent : baseEnd_331827 < baseStart_331827 := by decide
  rcases family_descends (prefixWord ++ tailWord_331827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331887 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 3, 3]
def baseStart_331887 : Nat := 118140960795 + 331887 * 2 ^ 59
def prefixEnd_331887 : Nat := 4983230072969 + 3 ^ 40 * 331887 * 2
def baseEnd_331887 : Nat := 113611702652565482857457

theorem tailTrace_331887 : CollatzResearch.WordTrace tailWord_331887 prefixEnd_331887 113611702652565482857457 := by
  unfold tailWord_331887
  simp only [CollatzResearch.WordTrace]
  refine ⟨12104913348637555632041915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8069942232425037088027943 12104913348637555632041915)
  ·
    refine ⟨18157370022956333448062873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12104913348637555632041915 18157370022956333448062873)
    ·
      refine ⟨13618027517217250086047155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18157370022956333448062873 13618027517217250086047155)
      ·
        refine ⟨20427041275825875129070733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13618027517217250086047155 20427041275825875129070733)
        ·
          refine ⟨7660140478434703173401525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20427041275825875129070733 7660140478434703173401525)
          ·
            refine ⟨718138169853253422506393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7660140478434703173401525 718138169853253422506393)
            ·
              refine ⟨538603627389940066879795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718138169853253422506393 538603627389940066879795)
              ·
                refine ⟨807905441084910100319693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538603627389940066879795 807905441084910100319693)
                ·
                  refine ⟨302964540406841287619885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807905441084910100319693 302964540406841287619885)
                  ·
                    refine ⟨113611702652565482857457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 302964540406841287619885 113611702652565482857457)
                    ·
                      rfl

theorem cell22_331887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 3].length) (baseStart_331887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331887 prefixEnd_331887 := by exact prefixLift 331887
  have htrace : WordTrace (prefixWord ++ tailWord_331887) baseStart_331887 baseEnd_331887 := by
    simpa [prefixWord, tailWord_331887, baseEnd_331887] using wordTrace_append hprefix tailTrace_331887
  have hstable : (prefixWord ++ tailWord_331887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331887).length < 2 ^ (prefixWord ++ tailWord_331887).sum := by decide
  have hdescent : baseEnd_331887 < baseStart_331887 := by decide
  rcases family_descends (prefixWord ++ tailWord_331887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331938 : List Nat := [3, 3, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_331938 : Nat := 118140960795 + 331938 * 2 ^ 59
def prefixEnd_331938 : Nat := 4983230072969 + 3 ^ 40 * 331938 * 2
def baseEnd_331938 : Nat := 113629160994818349832301

theorem tailTrace_331938 : CollatzResearch.WordTrace tailWord_331938 prefixEnd_331938 113629160994818349832301 := by
  unfold tailWord_331938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3026693367863197835537117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8071182314301860894765645 3026693367863197835537117)
  ·
    refine ⟨1135010012948699188326419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3026693367863197835537117 1135010012948699188326419)
    ·
      refine ⟨1702515019423048782489629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1135010012948699188326419 1702515019423048782489629)
      ·
        refine ⟨638443132283643293433611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1702515019423048782489629 638443132283643293433611)
        ·
          refine ⟨957664698425464940150417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638443132283643293433611 957664698425464940150417)
          ·
            refine ⟨718248523819098705112813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 957664698425464940150417 718248523819098705112813)
            ·
              refine ⟨269343196432162014417305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 718248523819098705112813 269343196432162014417305)
              ·
                refine ⟨202007397324121510812979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269343196432162014417305 202007397324121510812979)
                ·
                  refine ⟨303011095986182266219469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202007397324121510812979 303011095986182266219469)
                  ·
                    refine ⟨113629160994818349832301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 303011095986182266219469 113629160994818349832301)
                    ·
                      rfl

theorem cell22_331938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_331938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331938 prefixEnd_331938 := by exact prefixLift 331938
  have htrace : WordTrace (prefixWord ++ tailWord_331938) baseStart_331938 baseEnd_331938 := by
    simpa [prefixWord, tailWord_331938, baseEnd_331938] using wordTrace_append hprefix tailTrace_331938
  have hstable : (prefixWord ++ tailWord_331938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331938).length < 2 ^ (prefixWord ++ tailWord_331938).sum := by decide
  have hdescent : baseEnd_331938 < baseStart_331938 := by decide
  rcases family_descends (prefixWord ++ tailWord_331938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331960 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 1, 5]
def baseStart_331960 : Nat := 118140960795 + 331960 * 2 ^ 59
def prefixEnd_331960 : Nat := 4983230072969 + 3 ^ 40 * 331960 * 2
def baseEnd_331960 : Nat := 113636692044417625782233

theorem tailTrace_331960 : CollatzResearch.WordTrace tailWord_331960 prefixEnd_331960 113636692044417625782233 := by
  unfold tailWord_331960
  simp only [CollatzResearch.WordTrace]
  refine ⟨6053787938686544549724667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8071717251582059399632889 6053787938686544549724667)
  ·
    refine ⟨9080681908029816824587001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6053787938686544549724667 9080681908029816824587001)
    ·
      refine ⟨6810511431022362618440251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9080681908029816824587001 6810511431022362618440251)
      ·
        refine ⟨10215767146533543927660377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6810511431022362618440251 10215767146533543927660377)
        ·
          refine ⟨7661825359900157945745283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10215767146533543927660377 7661825359900157945745283)
          ·
            refine ⟨11492738039850236918617925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7661825359900157945745283 11492738039850236918617925)
            ·
              refine ⟨2154888382471919422240861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11492738039850236918617925 2154888382471919422240861)
              ·
                refine ⟨808083143426969783340323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2154888382471919422240861 808083143426969783340323)
                ·
                  refine ⟨1212124715140454675010485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808083143426969783340323 1212124715140454675010485)
                  ·
                    refine ⟨113636692044417625782233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1212124715140454675010485 113636692044417625782233)
                    ·
                      rfl

theorem cell22_331960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_331960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331960 prefixEnd_331960 := by exact prefixLift 331960
  have htrace : WordTrace (prefixWord ++ tailWord_331960) baseStart_331960 baseEnd_331960 := by
    simpa [prefixWord, tailWord_331960, baseEnd_331960] using wordTrace_append hprefix tailTrace_331960
  have hstable : (prefixWord ++ tailWord_331960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331960).length < 2 ^ (prefixWord ++ tailWord_331960).sum := by decide
  have hdescent : baseEnd_331960 < baseStart_331960 := by decide
  rcases family_descends (prefixWord ++ tailWord_331960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331992 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 2, 4]
def baseStart_331992 : Nat := 118140960795 + 331992 * 2 ^ 59
def prefixEnd_331992 : Nat := 4983230072969 + 3 ^ 40 * 331992 * 2
def baseEnd_331992 : Nat := 113647646298380208982135

theorem tailTrace_331992 : CollatzResearch.WordTrace tailWord_331992 prefixEnd_331992 113647646298380208982135 := by
  unfold tailWord_331992
  simp only [CollatzResearch.WordTrace]
  refine ⟨6054371506628579282307115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8072495342171439043076153 6054371506628579282307115)
  ·
    refine ⟨9081557259942868923460673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6054371506628579282307115 9081557259942868923460673)
    ·
      refine ⟨6811167944957151692595505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9081557259942868923460673 6811167944957151692595505)
      ·
        refine ⟨5108375958717863769446629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6811167944957151692595505 5108375958717863769446629)
        ·
          refine ⟨957820492259599456771243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5108375958717863769446629 957820492259599456771243)
          ·
            refine ⟨1436730738389399185156865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957820492259599456771243 1436730738389399185156865)
            ·
              refine ⟨1077548053792049388867649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1436730738389399185156865 1077548053792049388867649)
              ·
                refine ⟨808161040344037041650737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077548053792049388867649 808161040344037041650737)
                ·
                  refine ⟨606120780258027781238053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 808161040344037041650737 606120780258027781238053)
                  ·
                    refine ⟨113647646298380208982135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 606120780258027781238053 113647646298380208982135)
                    ·
                      rfl

theorem cell22_331992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_331992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331992 prefixEnd_331992 := by exact prefixLift 331992
  have htrace : WordTrace (prefixWord ++ tailWord_331992) baseStart_331992 baseEnd_331992 := by
    simpa [prefixWord, tailWord_331992, baseEnd_331992] using wordTrace_append hprefix tailTrace_331992
  have hstable : (prefixWord ++ tailWord_331992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331992).length < 2 ^ (prefixWord ++ tailWord_331992).sum := by decide
  have hdescent : baseEnd_331992 < baseStart_331992 := by decide
  rcases family_descends (prefixWord ++ tailWord_331992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332007 : List Nat := [1, 1, 5, 3, 1, 1, 3, 7]
def baseStart_332007 : Nat := 118140960795 + 332007 * 2 ^ 59
def prefixEnd_332007 : Nat := 4983230072969 + 3 ^ 40 * 332007 * 2
def baseEnd_332007 : Nat := 12628086789436129984121

theorem tailTrace_332007 : CollatzResearch.WordTrace tailWord_332007 prefixEnd_332007 12628086789436129984121 := by
  unfold tailWord_332007
  simp only [CollatzResearch.WordTrace]
  refine ⟨12109290108202816126410275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8072860072135210750940183 12109290108202816126410275)
  ·
    refine ⟨18163935162304224189615413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12109290108202816126410275 18163935162304224189615413)
    ·
      refine ⟨1702868921466021017776445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18163935162304224189615413 1702868921466021017776445)
      ·
        refine ⟨638575845549757881666167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1702868921466021017776445 638575845549757881666167)
        ·
          refine ⟨957863768324636822499251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638575845549757881666167 957863768324636822499251)
          ·
            refine ⟨1436795652486955233748877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957863768324636822499251 1436795652486955233748877)
            ·
              refine ⟨538798369682608212655829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1436795652486955233748877 538798369682608212655829)
              ·
                refine ⟨12628086789436129984121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 538798369682608212655829 12628086789436129984121)
                ·
                  rfl

theorem cell22_332007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 7].length) (baseStart_332007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332007 prefixEnd_332007 := by exact prefixLift 332007
  have htrace : WordTrace (prefixWord ++ tailWord_332007) baseStart_332007 baseEnd_332007 := by
    simpa [prefixWord, tailWord_332007, baseEnd_332007] using wordTrace_append hprefix tailTrace_332007
  have hstable : (prefixWord ++ tailWord_332007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332007).length < 2 ^ (prefixWord ++ tailWord_332007).sum := by decide
  have hdescent : baseEnd_332007 < baseStart_332007 := by decide
  rcases family_descends (prefixWord ++ tailWord_332007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332035 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 7]
def baseStart_332035 : Nat := 118140960795 + 332035 * 2 ^ 59
def prefixEnd_332035 : Nat := 4983230072969 + 3 ^ 40 * 332035 * 2
def baseEnd_332035 : Nat := 37887455359047476719001

theorem tailTrace_332035 : CollatzResearch.WordTrace tailWord_332035 prefixEnd_332035 37887455359047476719001 := by
  unfold tailWord_332035
  simp only [CollatzResearch.WordTrace]
  refine ⟨12110311352101376908429559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8073540901400917938953039 12110311352101376908429559)
  ·
    refine ⟨18165467028152065362644339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12110311352101376908429559 18165467028152065362644339)
    ·
      refine ⟨27248200542228098043966509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18165467028152065362644339 27248200542228098043966509)
      ·
        refine ⟨10218075203335536766487441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27248200542228098043966509 10218075203335536766487441)
        ·
          refine ⟨7663556402501652574865581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10218075203335536766487441 7663556402501652574865581)
          ·
            refine ⟨2873833650938119715574593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7663556402501652574865581 2873833650938119715574593)
            ·
              refine ⟨2155375238203589786680945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2873833650938119715574593 2155375238203589786680945)
              ·
                refine ⟨1616531428652692340010709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2155375238203589786680945 1616531428652692340010709)
                ·
                  refine ⟨37887455359047476719001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1616531428652692340010709 37887455359047476719001)
                  ·
                    rfl

theorem cell22_332035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 7].length) (baseStart_332035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332035 prefixEnd_332035 := by exact prefixLift 332035
  have htrace : WordTrace (prefixWord ++ tailWord_332035) baseStart_332035 baseEnd_332035 := by
    simpa [prefixWord, tailWord_332035, baseEnd_332035] using wordTrace_append hprefix tailTrace_332035
  have hstable : (prefixWord ++ tailWord_332035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332035).length < 2 ^ (prefixWord ++ tailWord_332035).sum := by decide
  have hdescent : baseEnd_332035 < baseStart_332035 := by decide
  rcases family_descends (prefixWord ++ tailWord_332035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332080 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 8]
def baseStart_332080 : Nat := 118140960795 + 332080 * 2 ^ 59
def prefixEnd_332080 : Nat := 4983230072969 + 3 ^ 40 * 332080 * 2
def baseEnd_332080 : Nat := 37892590165592437593955

theorem tailTrace_332080 : CollatzResearch.WordTrace tailWord_332080 prefixEnd_332080 37892590165592437593955 := by
  unfold tailWord_332080
  simp only [CollatzResearch.WordTrace]
  refine ⟨6055976318469174796908847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8074635091292233062545129 6055976318469174796908847)
  ·
    refine ⟨9083964477703762195363271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6055976318469174796908847 9083964477703762195363271)
    ·
      refine ⟨13625946716555643293044907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9083964477703762195363271 13625946716555643293044907)
      ·
        refine ⟨20438920074833464939567361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13625946716555643293044907 20438920074833464939567361)
        ·
          refine ⟨15329190056125098704675521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20438920074833464939567361 15329190056125098704675521)
          ·
            refine ⟨11496892542093824028506641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15329190056125098704675521 11496892542093824028506641)
            ·
              refine ⟨8622669406570368021379981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11496892542093824028506641 8622669406570368021379981)
              ·
                refine ⟨3233501027463888008017493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8622669406570368021379981 3233501027463888008017493)
                ·
                  refine ⟨37892590165592437593955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3233501027463888008017493 37892590165592437593955)
                  ·
                    rfl

theorem cell22_332080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_332080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332080 prefixEnd_332080 := by exact prefixLift 332080
  have htrace : WordTrace (prefixWord ++ tailWord_332080) baseStart_332080 baseEnd_332080 := by
    simpa [prefixWord, tailWord_332080, baseEnd_332080] using wordTrace_append hprefix tailTrace_332080
  have hstable : (prefixWord ++ tailWord_332080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332080).length < 2 ^ (prefixWord ++ tailWord_332080).sum := by decide
  have hdescent : baseEnd_332080 < baseStart_332080 := by decide
  rcases family_descends (prefixWord ++ tailWord_332080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332114 : List Nat := [3, 2, 2, 1, 1, 1, 2, 6, 4]
def baseStart_332114 : Nat := 118140960795 + 332114 * 2 ^ 59
def prefixEnd_332114 : Nat := 4983230072969 + 3 ^ 40 * 332114 * 2
def baseEnd_332114 : Nat := 37896469797204185810587

theorem tailTrace_332114 : CollatzResearch.WordTrace tailWord_332114 prefixEnd_332114 37896469797204185810587 := by
  unfold tailWord_332114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3028298179703793350138849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8075461812543448933703597 3028298179703793350138849)
  ·
    refine ⟨2271223634777845012604137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3028298179703793350138849 2271223634777845012604137)
    ·
      refine ⟨1703417726083383759453103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2271223634777845012604137 1703417726083383759453103)
      ·
        refine ⟨2555126589125075639179655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1703417726083383759453103 2555126589125075639179655)
        ·
          refine ⟨3832689883687613458769483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2555126589125075639179655 3832689883687613458769483)
          ·
            refine ⟨5749034825531420188154225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832689883687613458769483 5749034825531420188154225)
            ·
              refine ⟨4311776119148565141115669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5749034825531420188154225 4311776119148565141115669)
              ·
                refine ⟨202114505585088990989797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4311776119148565141115669 202114505585088990989797)
                ·
                  refine ⟨37896469797204185810587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 202114505585088990989797 37896469797204185810587)
                  ·
                    rfl

theorem cell22_332114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_332114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332114 prefixEnd_332114 := by exact prefixLift 332114
  have htrace : WordTrace (prefixWord ++ tailWord_332114) baseStart_332114 baseEnd_332114 := by
    simpa [prefixWord, tailWord_332114, baseEnd_332114] using wordTrace_append hprefix tailTrace_332114
  have hstable : (prefixWord ++ tailWord_332114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332114).length < 2 ^ (prefixWord ++ tailWord_332114).sum := by decide
  have hdescent : baseEnd_332114 < baseStart_332114 := by decide
  rcases family_descends (prefixWord ++ tailWord_332114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332144 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 2, 4]
def baseStart_332144 : Nat := 118140960795 + 332144 * 2 ^ 59
def prefixEnd_332144 : Nat := 4983230072969 + 3 ^ 40 * 332144 * 2
def baseEnd_332144 : Nat := 113699679004702479181669

theorem tailTrace_332144 : CollatzResearch.WordTrace tailWord_332144 prefixEnd_332144 113699679004702479181669 := by
  unfold tailWord_332144
  simp only [CollatzResearch.WordTrace]
  refine ⟨6057143454353244262073743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8076191272470992349431657 6057143454353244262073743)
  ·
    refine ⟨9085715181529866393110615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6057143454353244262073743 9085715181529866393110615)
    ·
      refine ⟨13628572772294799589665923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9085715181529866393110615 13628572772294799589665923)
      ·
        refine ⟨20442859158442199384498885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13628572772294799589665923 20442859158442199384498885)
        ·
          refine ⟨3833036092207912384593541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20442859158442199384498885 3833036092207912384593541)
          ·
            refine ⟨718694267288983572111289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3833036092207912384593541 718694267288983572111289)
            ·
              refine ⟨539020700466737679083467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718694267288983572111289 539020700466737679083467)
              ·
                refine ⟨808531050700106518625201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539020700466737679083467 808531050700106518625201)
                ·
                  refine ⟨606398288025079888968901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 808531050700106518625201 606398288025079888968901)
                  ·
                    refine ⟨113699679004702479181669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 606398288025079888968901 113699679004702479181669)
                    ·
                      rfl

theorem cell22_332144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_332144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332144 prefixEnd_332144 := by exact prefixLift 332144
  have htrace : WordTrace (prefixWord ++ tailWord_332144) baseStart_332144 baseEnd_332144 := by
    simpa [prefixWord, tailWord_332144, baseEnd_332144] using wordTrace_append hprefix tailTrace_332144
  have hstable : (prefixWord ++ tailWord_332144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332144).length < 2 ^ (prefixWord ++ tailWord_332144).sum := by decide
  have hdescent : baseEnd_332144 < baseStart_332144 := by decide
  rcases family_descends (prefixWord ++ tailWord_332144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332150 : List Nat := [5, 1, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_332150 : Nat := 118140960795 + 332150 * 2 ^ 59
def prefixEnd_332150 : Nat := 4983230072969 + 3 ^ 40 * 332150 * 2
def baseEnd_332150 : Nat := 113701732927320463531651

theorem tailTrace_332150 : CollatzResearch.WordTrace tailWord_332150 prefixEnd_332150 113701732927320463531651 := by
  unfold tailWord_332150
  simp only [CollatzResearch.WordTrace]
  refine ⟨757156609167796971804119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8076337164456501032577269 757156609167796971804119)
  ·
    refine ⟨1135734913751695457706179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 757156609167796971804119 1135734913751695457706179)
    ·
      refine ⟨1703602370627543186559269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1135734913751695457706179 1703602370627543186559269)
      ·
        refine ⟨319425444492664347479863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1703602370627543186559269 319425444492664347479863)
        ·
          refine ⟨479138166738996521219795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319425444492664347479863 479138166738996521219795)
          ·
            refine ⟨718707250108494781829693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479138166738996521219795 718707250108494781829693)
            ·
              refine ⟨269515218790685543186135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 718707250108494781829693 269515218790685543186135)
              ·
                refine ⟨404272828186028314779203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269515218790685543186135 404272828186028314779203)
                ·
                  refine ⟨606409242279042472168805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404272828186028314779203 606409242279042472168805)
                  ·
                    refine ⟨113701732927320463531651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 606409242279042472168805 113701732927320463531651)
                    ·
                      rfl

theorem cell22_332150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_332150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332150 prefixEnd_332150 := by exact prefixLift 332150
  have htrace : WordTrace (prefixWord ++ tailWord_332150) baseStart_332150 baseEnd_332150 := by
    simpa [prefixWord, tailWord_332150, baseEnd_332150] using wordTrace_append hprefix tailTrace_332150
  have hstable : (prefixWord ++ tailWord_332150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332150).length < 2 ^ (prefixWord ++ tailWord_332150).sum := by decide
  have hdescent : baseEnd_332150 < baseStart_332150 := by decide
  rcases family_descends (prefixWord ++ tailWord_332150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332172 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_332172 : Nat := 118140960795 + 332172 * 2 ^ 59
def prefixEnd_332172 : Nat := 4983230072969 + 3 ^ 40 * 332172 * 2
def baseEnd_332172 : Nat := 113709263976919739481583

theorem tailTrace_332172 : CollatzResearch.WordTrace tailWord_332172 prefixEnd_332172 113709263976919739481583 := by
  unfold tailWord_332172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6057654076302524653083385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8076872101736699537444513 6057654076302524653083385)
  ·
    refine ⟨4543240557226893489812539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6057654076302524653083385 4543240557226893489812539)
    ·
      refine ⟨6814860835840340234718809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4543240557226893489812539 6814860835840340234718809)
      ·
        refine ⟨5111145626880255176039107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6814860835840340234718809 5111145626880255176039107)
        ·
          refine ⟨7666718440320382764058661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5111145626880255176039107 7666718440320382764058661)
          ·
            refine ⟨1437509707560071768260999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7666718440320382764058661 1437509707560071768260999)
            ·
              refine ⟨2156264561340107652391499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437509707560071768260999 2156264561340107652391499)
              ·
                refine ⟨3234396842010161478587249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156264561340107652391499 3234396842010161478587249)
                ·
                  refine ⟨2425797631507621108940437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3234396842010161478587249 2425797631507621108940437)
                  ·
                    refine ⟨113709263976919739481583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2425797631507621108940437 113709263976919739481583)
                    ·
                      rfl

theorem cell22_332172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_332172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332172 prefixEnd_332172 := by exact prefixLift 332172
  have htrace : WordTrace (prefixWord ++ tailWord_332172) baseStart_332172 baseEnd_332172 := by
    simpa [prefixWord, tailWord_332172, baseEnd_332172] using wordTrace_append hprefix tailTrace_332172
  have hstable : (prefixWord ++ tailWord_332172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332172).length < 2 ^ (prefixWord ++ tailWord_332172).sum := by decide
  have hdescent : baseEnd_332172 < baseStart_332172 := by decide
  rcases family_descends (prefixWord ++ tailWord_332172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332221 : List Nat := [1, 4, 1, 2, 2, 4, 1, 2, 5]
def baseStart_332221 : Nat := 118140960795 + 332221 * 2 ^ 59
def prefixEnd_332221 : Nat := 4983230072969 + 3 ^ 40 * 332221 * 2
def baseEnd_332221 : Nat := 37908679226099981668811

theorem tailTrace_332221 : CollatzResearch.WordTrace tailWord_332221 prefixEnd_332221 37908679226099981668811 := by
  unfold tailWord_332221
  simp only [CollatzResearch.WordTrace]
  refine ⟨12117095329427530674700517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8078063552951687116467011 12117095329427530674700517)
  ·
    refine ⟨2271955374267662001506347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12117095329427530674700517 2271955374267662001506347)
    ·
      refine ⟨3407933061401493002259521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2271955374267662001506347 3407933061401493002259521)
      ·
        refine ⟨2555949796051119751694641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3407933061401493002259521 2555949796051119751694641)
        ·
          refine ⟨1916962347038339813770981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2555949796051119751694641 1916962347038339813770981)
          ·
            refine ⟨359430440069688715082059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1916962347038339813770981 359430440069688715082059)
            ·
              refine ⟨539145660104533072623089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359430440069688715082059 539145660104533072623089)
              ·
                refine ⟨404359245078399804467317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539145660104533072623089 404359245078399804467317)
                ·
                  refine ⟨37908679226099981668811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 404359245078399804467317 37908679226099981668811)
                  ·
                    rfl

theorem cell22_332221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_332221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332221 prefixEnd_332221 := by exact prefixLift 332221
  have htrace : WordTrace (prefixWord ++ tailWord_332221) baseStart_332221 baseEnd_332221 := by
    simpa [prefixWord, tailWord_332221, baseEnd_332221] using wordTrace_append hprefix tailTrace_332221
  have hstable : (prefixWord ++ tailWord_332221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332221).length < 2 ^ (prefixWord ++ tailWord_332221).sum := by decide
  have hdescent : baseEnd_332221 < baseStart_332221 := by decide
  rcases family_descends (prefixWord ++ tailWord_332221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332343 : List Nat := [1, 1, 3, 1, 2, 3, 3, 4, 1, 3]
def baseStart_332343 : Nat := 118140960795 + 332343 * 2 ^ 59
def prefixEnd_332343 : Nat := 4983230072969 + 3 ^ 40 * 332343 * 2
def baseEnd_332343 : Nat := 113767800771532293456059

theorem tailTrace_332343 : CollatzResearch.WordTrace tailWord_332343 prefixEnd_332343 113767800771532293456059 := by
  unfold tailWord_332343
  simp only [CollatzResearch.WordTrace]
  refine ⟨12121545034985545510641683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8081030023323697007094455 12121545034985545510641683)
  ·
    refine ⟨18182317552478318265962525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12121545034985545510641683 18182317552478318265962525)
    ·
      refine ⟨6818369082179369349735947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18182317552478318265962525 6818369082179369349735947)
      ·
        refine ⟨10227553623269054024603921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6818369082179369349735947 10227553623269054024603921)
        ·
          refine ⟨7670665217451790518452941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10227553623269054024603921 7670665217451790518452941)
          ·
            refine ⟨2876499456544421444419853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7670665217451790518452941 2876499456544421444419853)
            ·
              refine ⟨1078687296204158041657445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2876499456544421444419853 1078687296204158041657445)
              ·
                refine ⟨202253868038279632810771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1078687296204158041657445 202253868038279632810771)
                ·
                  refine ⟨303380802057419449216157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202253868038279632810771 303380802057419449216157)
                  ·
                    refine ⟨113767800771532293456059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 303380802057419449216157 113767800771532293456059)
                    ·
                      rfl

theorem cell22_332343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_332343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332343 prefixEnd_332343 := by exact prefixLift 332343
  have htrace : WordTrace (prefixWord ++ tailWord_332343) baseStart_332343 baseEnd_332343 := by
    simpa [prefixWord, tailWord_332343, baseEnd_332343] using wordTrace_append hprefix tailTrace_332343
  have hstable : (prefixWord ++ tailWord_332343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332343).length < 2 ^ (prefixWord ++ tailWord_332343).sum := by decide
  have hdescent : baseEnd_332343 < baseStart_332343 := by decide
  rcases family_descends (prefixWord ++ tailWord_332343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332399 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 3, 5]
def baseStart_332399 : Nat := 118140960795 + 332399 * 2 ^ 59
def prefixEnd_332399 : Nat := 4983230072969 + 3 ^ 40 * 332399 * 2
def baseEnd_332399 : Nat := 113786970715966814055887

theorem tailTrace_332399 : CollatzResearch.WordTrace tailWord_332399 prefixEnd_332399 113786970715966814055887 := by
  unfold tailWord_332399
  simp only [CollatzResearch.WordTrace]
  refine ⟨12123587522782667074680251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8082391681855111383120167 12123587522782667074680251)
  ·
    refine ⟨18185381284174000612020377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12123587522782667074680251 18185381284174000612020377)
    ·
      refine ⟨13639035963130500459015283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18185381284174000612020377 13639035963130500459015283)
      ·
        refine ⟨20458553944695750688522925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13639035963130500459015283 20458553944695750688522925)
        ·
          refine ⟨7671957729260906508196097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20458553944695750688522925 7671957729260906508196097)
          ·
            refine ⟨5753968296945679881147073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7671957729260906508196097 5753968296945679881147073)
            ·
              refine ⟨4315476222709259910860305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5753968296945679881147073 4315476222709259910860305)
              ·
                refine ⟨3236607167031944933145229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4315476222709259910860305 3236607167031944933145229)
                ·
                  refine ⟨1213727687636979349929461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3236607167031944933145229 1213727687636979349929461)
                  ·
                    refine ⟨113786970715966814055887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1213727687636979349929461 113786970715966814055887)
                    ·
                      rfl

theorem cell22_332399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_332399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332399 prefixEnd_332399 := by exact prefixLift 332399
  have htrace : WordTrace (prefixWord ++ tailWord_332399) baseStart_332399 baseEnd_332399 := by
    simpa [prefixWord, tailWord_332399, baseEnd_332399] using wordTrace_append hprefix tailTrace_332399
  have hstable : (prefixWord ++ tailWord_332399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332399).length < 2 ^ (prefixWord ++ tailWord_332399).sum := by decide
  have hdescent : baseEnd_332399 < baseStart_332399 := by decide
  rcases family_descends (prefixWord ++ tailWord_332399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332416 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 1, 5]
def baseStart_332416 : Nat := 118140960795 + 332416 * 2 ^ 59
def prefixEnd_332416 : Nat := 4983230072969 + 3 ^ 40 * 332416 * 2
def baseEnd_332416 : Nat := 113792790163384436380835

theorem tailTrace_332416 : CollatzResearch.WordTrace tailWord_332416 prefixEnd_332416 113792790163384436380835 := by
  unfold tailWord_332416
  simp only [CollatzResearch.WordTrace]
  refine ⟨6062103781860539489024551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8082805042480719318699401 6062103781860539489024551)
  ·
    refine ⟨9093155672790809233536827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6062103781860539489024551 9093155672790809233536827)
    ·
      refine ⟨13639733509186213850305241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9093155672790809233536827 13639733509186213850305241)
      ·
        refine ⟨10229800131889660387728931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13639733509186213850305241 10229800131889660387728931)
        ·
          refine ⟨15344700197834490581593397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10229800131889660387728931 15344700197834490581593397)
          ·
            refine ⟨1438565643546983492024381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15344700197834490581593397 1438565643546983492024381)
            ·
              refine ⟨539462116330118809509143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1438565643546983492024381 539462116330118809509143)
              ·
                refine ⟨809193174495178214263715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539462116330118809509143 809193174495178214263715)
                ·
                  refine ⟨1213789761742767321395573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 809193174495178214263715 1213789761742767321395573)
                  ·
                    refine ⟨113792790163384436380835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1213789761742767321395573 113792790163384436380835)
                    ·
                      rfl

theorem cell22_332416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_332416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332416 prefixEnd_332416 := by exact prefixLift 332416
  have htrace : WordTrace (prefixWord ++ tailWord_332416) baseStart_332416 baseEnd_332416 := by
    simpa [prefixWord, tailWord_332416, baseEnd_332416] using wordTrace_append hprefix tailTrace_332416
  have hstable : (prefixWord ++ tailWord_332416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332416).length < 2 ^ (prefixWord ++ tailWord_332416).sum := by decide
  have hdescent : baseEnd_332416 < baseStart_332416 := by decide
  rcases family_descends (prefixWord ++ tailWord_332416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332448 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 2, 4]
def baseStart_332448 : Nat := 118140960795 + 332448 * 2 ^ 59
def prefixEnd_332448 : Nat := 4983230072969 + 3 ^ 40 * 332448 * 2
def baseEnd_332448 : Nat := 113803744417347019580737

theorem tailTrace_332448 : CollatzResearch.WordTrace tailWord_332448 prefixEnd_332448 113803744417347019580737 := by
  unfold tailWord_332448
  simp only [CollatzResearch.WordTrace]
  refine ⟨6062687349802574221606999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8083583133070098962142665 6062687349802574221606999)
  ·
    refine ⟨9094031024703861332410499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6062687349802574221606999 9094031024703861332410499)
    ·
      refine ⟨13641046537055791998615749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9094031024703861332410499 13641046537055791998615749)
      ·
        refine ⟨2557696225697960999740453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13641046537055791998615749 2557696225697960999740453)
        ·
          refine ⟨479568042318367687451335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2557696225697960999740453 479568042318367687451335)
          ·
            refine ⟨719352063477551531177003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479568042318367687451335 719352063477551531177003)
            ·
              refine ⟨1079028095216327296765505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719352063477551531177003 1079028095216327296765505)
              ·
                refine ⟨809271071412245472574129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079028095216327296765505 809271071412245472574129)
                ·
                  refine ⟨606953303559184104430597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 809271071412245472574129 606953303559184104430597)
                  ·
                    refine ⟨113803744417347019580737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 606953303559184104430597 113803744417347019580737)
                    ·
                      rfl

theorem cell22_332448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_332448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332448 prefixEnd_332448 := by exact prefixLift 332448
  have htrace : WordTrace (prefixWord ++ tailWord_332448) baseStart_332448 baseEnd_332448 := by
    simpa [prefixWord, tailWord_332448, baseEnd_332448] using wordTrace_append hprefix tailTrace_332448
  have hstable : (prefixWord ++ tailWord_332448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332448).length < 2 ^ (prefixWord ++ tailWord_332448).sum := by decide
  have hdescent : baseEnd_332448 < baseStart_332448 := by decide
  rcases family_descends (prefixWord ++ tailWord_332448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332478 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_332478 : Nat := 118140960795 + 332478 * 2 ^ 59
def prefixEnd_332478 : Nat := 4983230072969 + 3 ^ 40 * 332478 * 2
def baseEnd_332478 : Nat := 113814014030436941330645

theorem tailTrace_332478 : CollatzResearch.WordTrace tailWord_332478 prefixEnd_332478 113814014030436941330645 := by
  unfold tailWord_332478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1515808611187057945850761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8084312592997642377870725 1515808611187057945850761)
  ·
    refine ⟨1136856458390293459388071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1515808611187057945850761 1136856458390293459388071)
    ·
      refine ⟨1705284687585440189082107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1136856458390293459388071 1705284687585440189082107)
      ·
        refine ⟨2557927031378160283623161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705284687585440189082107 2557927031378160283623161)
        ·
          refine ⟨1918445273533620212717371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2557927031378160283623161 1918445273533620212717371)
          ·
            refine ⟨2877667910300430319076057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918445273533620212717371 2877667910300430319076057)
            ·
              refine ⟨2158250932725322739307043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2877667910300430319076057 2158250932725322739307043)
              ·
                refine ⟨3237376399087984108960565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158250932725322739307043 3237376399087984108960565)
                ·
                  refine ⟨303504037414498510215053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3237376399087984108960565 303504037414498510215053)
                  ·
                    refine ⟨113814014030436941330645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 303504037414498510215053 113814014030436941330645)
                    ·
                      rfl

theorem cell22_332478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_332478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332478 prefixEnd_332478 := by exact prefixLift 332478
  have htrace : WordTrace (prefixWord ++ tailWord_332478) baseStart_332478 baseEnd_332478 := by
    simpa [prefixWord, tailWord_332478, baseEnd_332478] using wordTrace_append hprefix tailTrace_332478
  have hstable : (prefixWord ++ tailWord_332478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332478).length < 2 ^ (prefixWord ++ tailWord_332478).sum := by decide
  have hdescent : baseEnd_332478 < baseStart_332478 := by decide
  rcases family_descends (prefixWord ++ tailWord_332478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332506 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_332506 : Nat := 118140960795 + 332506 * 2 ^ 59
def prefixEnd_332506 : Nat := 4983230072969 + 3 ^ 40 * 332506 * 2
def baseEnd_332506 : Nat := 113823599002654201630559

theorem tailTrace_332506 : CollatzResearch.WordTrace tailWord_332506 prefixEnd_332506 113823599002654201630559 := by
  unfold tailWord_332506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3031872533348756087206343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8084993422263349565883581 3031872533348756087206343)
  ·
    refine ⟨4547808800023134130809515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3031872533348756087206343 4547808800023134130809515)
    ·
      refine ⟨6821713200034701196214273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4547808800023134130809515 6821713200034701196214273)
      ·
        refine ⟨5116284900026025897160705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6821713200034701196214273 5116284900026025897160705)
        ·
          refine ⟨3837213675019519422870529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5116284900026025897160705 3837213675019519422870529)
          ·
            refine ⟨2877910256264639567152897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3837213675019519422870529 2877910256264639567152897)
            ·
              refine ⟨2158432692198479675364673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2877910256264639567152897 2158432692198479675364673)
              ·
                refine ⟨1618824519148859756523505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2158432692198479675364673 1618824519148859756523505)
                ·
                  refine ⟨1214118389361644817392629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1618824519148859756523505 1214118389361644817392629)
                  ·
                    refine ⟨113823599002654201630559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1214118389361644817392629 113823599002654201630559)
                    ·
                      rfl

theorem cell22_332506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_332506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332506 prefixEnd_332506 := by exact prefixLift 332506
  have htrace : WordTrace (prefixWord ++ tailWord_332506) baseStart_332506 baseEnd_332506 := by
    simpa [prefixWord, tailWord_332506, baseEnd_332506] using wordTrace_append hprefix tailTrace_332506
  have hstable : (prefixWord ++ tailWord_332506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332506).length < 2 ^ (prefixWord ++ tailWord_332506).sum := by decide
  have hdescent : baseEnd_332506 < baseStart_332506 := by decide
  rcases family_descends (prefixWord ++ tailWord_332506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332521 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 3, 4]
def baseStart_332521 : Nat := 118140960795 + 332521 * 2 ^ 59
def prefixEnd_332521 : Nat := 4983230072969 + 3 ^ 40 * 332521 * 2
def baseEnd_332521 : Nat := 113828733809199162505513

theorem tailTrace_332521 : CollatzResearch.WordTrace tailWord_332521 prefixEnd_332521 113828733809199162505513 := by
  unfold tailWord_332521
  simp only [CollatzResearch.WordTrace]
  refine ⟨12128037228340681910621417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8085358152227121273747611 12128037228340681910621417)
  ·
    refine ⟨9096027921255511432966063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12128037228340681910621417 9096027921255511432966063)
    ·
      refine ⟨13644041881883267149449095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9096027921255511432966063 13644041881883267149449095)
      ·
        refine ⟨20466062822824900724173643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13644041881883267149449095 20466062822824900724173643)
        ·
          refine ⟨30699094234237351086260465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20466062822824900724173643 30699094234237351086260465)
          ·
            refine ⟨23024320675678013314695349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30699094234237351086260465 23024320675678013314695349)
            ·
              refine ⟨2158530063344813748252689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23024320675678013314695349 2158530063344813748252689)
              ·
                refine ⟨1618897547508610311189517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2158530063344813748252689 1618897547508610311189517)
                ·
                  refine ⟨607086580315728866696069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1618897547508610311189517 607086580315728866696069)
                  ·
                    refine ⟨113828733809199162505513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 607086580315728866696069 113828733809199162505513)
                    ·
                      rfl

theorem cell22_332521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_332521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332521 prefixEnd_332521 := by exact prefixLift 332521
  have htrace : WordTrace (prefixWord ++ tailWord_332521) baseStart_332521 baseEnd_332521 := by
    simpa [prefixWord, tailWord_332521, baseEnd_332521] using wordTrace_append hprefix tailTrace_332521
  have hstable : (prefixWord ++ tailWord_332521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332521).length < 2 ^ (prefixWord ++ tailWord_332521).sum := by decide
  have hdescent : baseEnd_332521 < baseStart_332521 := by decide
  rcases family_descends (prefixWord ++ tailWord_332521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332536 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 6]
def baseStart_332536 : Nat := 118140960795 + 332536 * 2 ^ 59
def prefixEnd_332536 : Nat := 4983230072969 + 3 ^ 40 * 332536 * 2
def baseEnd_332536 : Nat := 37944622871914707793489

theorem tailTrace_332536 : CollatzResearch.WordTrace tailWord_332536 prefixEnd_332536 37944622871914707793489 := by
  unfold tailWord_332536
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064292161643169736208731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8085722882190892981611641 6064292161643169736208731)
  ·
    refine ⟨9096438242464754604313097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6064292161643169736208731 9096438242464754604313097)
    ·
      refine ⟨6822328681848565953234823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9096438242464754604313097 6822328681848565953234823)
      ·
        refine ⟨10233493022772848929852235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6822328681848565953234823 10233493022772848929852235)
        ·
          refine ⟨15350239534159273394778353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10233493022772848929852235 15350239534159273394778353)
          ·
            refine ⟨11512679650619455046083765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15350239534159273394778353 11512679650619455046083765)
            ·
              refine ⟨1079313717245573910570353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11512679650619455046083765 1079313717245573910570353)
              ·
                refine ⟨809485287934180432927765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079313717245573910570353 809485287934180432927765)
                ·
                  refine ⟨37944622871914707793489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 809485287934180432927765 37944622871914707793489)
                  ·
                    rfl

theorem cell22_332536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_332536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332536 prefixEnd_332536 := by exact prefixLift 332536
  have htrace : WordTrace (prefixWord ++ tailWord_332536) baseStart_332536 baseEnd_332536 := by
    simpa [prefixWord, tailWord_332536, baseEnd_332536] using wordTrace_append hprefix tailTrace_332536
  have hstable : (prefixWord ++ tailWord_332536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332536).length < 2 ^ (prefixWord ++ tailWord_332536).sum := by decide
  have hdescent : baseEnd_332536 < baseStart_332536 := by decide
  rcases family_descends (prefixWord ++ tailWord_332536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332553 : List Nat := [1, 2, 1, 1, 3, 2, 3, 5, 4]
def baseStart_332553 : Nat := 118140960795 + 332553 * 2 ^ 59
def prefixEnd_332553 : Nat := 4983230072969 + 3 ^ 40 * 332553 * 2
def baseEnd_332553 : Nat := 37946562687720581901805

theorem tailTrace_332553 : CollatzResearch.WordTrace tailWord_332553 prefixEnd_332553 37946562687720581901805 := by
  unfold tailWord_332553
  simp only [CollatzResearch.WordTrace]
  refine ⟨12129204364224751375786313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8086136242816500917190875 12129204364224751375786313)
  ·
    refine ⟨9096903273168563531839735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12129204364224751375786313 9096903273168563531839735)
    ·
      refine ⟨13645354909752845297759603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9096903273168563531839735 13645354909752845297759603)
      ·
        refine ⟨20468032364629267946639405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13645354909752845297759603 20468032364629267946639405)
        ·
          refine ⟨7675512136735975479989777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20468032364629267946639405 7675512136735975479989777)
          ·
            refine ⟨5756634102551981609992333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7675512136735975479989777 5756634102551981609992333)
            ·
              refine ⟨2158737788456993103747125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5756634102551981609992333 2158737788456993103747125)
              ·
                refine ⟨202381667667843103476293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2158737788456993103747125 202381667667843103476293)
                ·
                  refine ⟨37946562687720581901805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 202381667667843103476293 37946562687720581901805)
                  ·
                    rfl

theorem cell22_332553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 4].length) (baseStart_332553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332553 prefixEnd_332553 := by exact prefixLift 332553
  have htrace : WordTrace (prefixWord ++ tailWord_332553) baseStart_332553 baseEnd_332553 := by
    simpa [prefixWord, tailWord_332553, baseEnd_332553] using wordTrace_append hprefix tailTrace_332553
  have hstable : (prefixWord ++ tailWord_332553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332553).length < 2 ^ (prefixWord ++ tailWord_332553).sum := by decide
  have hdescent : baseEnd_332553 < baseStart_332553 := by decide
  rcases family_descends (prefixWord ++ tailWord_332553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332581 : List Nat := [1, 3, 1, 2, 3, 1, 2, 9]
def baseStart_332581 : Nat := 118140960795 + 332581 * 2 ^ 59
def prefixEnd_332581 : Nat := 4983230072969 + 3 ^ 40 * 332581 * 2
def baseEnd_332581 : Nat := 12649919226153222889481

theorem tailTrace_332581 : CollatzResearch.WordTrace tailWord_332581 prefixEnd_332581 12649919226153222889481 := by
  unfold tailWord_332581
  simp only [CollatzResearch.WordTrace]
  refine ⟨12130225608123312157805597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8086817072082208105203731 12130225608123312157805597)
  ·
    refine ⟨4548834603046242059177099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12130225608123312157805597 4548834603046242059177099)
    ·
      refine ⟨6823251904569363088765649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4548834603046242059177099 6823251904569363088765649)
      ·
        refine ⟨5117438928427022316574237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6823251904569363088765649 5117438928427022316574237)
        ·
          refine ⟨1919039598160133368715339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5117438928427022316574237 1919039598160133368715339)
          ·
            refine ⟨2878559397240200053073009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919039598160133368715339 2878559397240200053073009)
            ·
              refine ⟨2158919547930150039804757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2878559397240200053073009 2158919547930150039804757)
              ·
                refine ⟨12649919226153222889481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2158919547930150039804757 12649919226153222889481)
                ·
                  rfl

theorem cell22_332581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 9].length) (baseStart_332581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332581 prefixEnd_332581 := by exact prefixLift 332581
  have htrace : WordTrace (prefixWord ++ tailWord_332581) baseStart_332581 baseEnd_332581 := by
    simpa [prefixWord, tailWord_332581, baseEnd_332581] using wordTrace_append hprefix tailTrace_332581
  have hstable : (prefixWord ++ tailWord_332581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332581).length < 2 ^ (prefixWord ++ tailWord_332581).sum := by decide
  have hdescent : baseEnd_332581 < baseStart_332581 := by decide
  rcases family_descends (prefixWord ++ tailWord_332581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332589 : List Nat := [1, 5, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_332589 : Nat := 118140960795 + 332589 * 2 ^ 59
def prefixEnd_332589 : Nat := 4983230072969 + 3 ^ 40 * 332589 * 2
def baseEnd_332589 : Nat := 113852011598869651805305

theorem tailTrace_332589 : CollatzResearch.WordTrace tailWord_332589 prefixEnd_332589 113852011598869651805305 := by
  unfold tailWord_332589
  simp only [CollatzResearch.WordTrace]
  refine ⟨12130517392094329524096821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8087011594729553016064547 12130517392094329524096821)
  ·
    refine ⟨1137236005508843392884077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12130517392094329524096821 1137236005508843392884077)
    ·
      refine ⟨426463502065816272331529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1137236005508843392884077 426463502065816272331529)
      ·
        refine ⟨319847626549362204248647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426463502065816272331529 319847626549362204248647)
        ·
          refine ⟨479771439824043306372971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319847626549362204248647 479771439824043306372971)
          ·
            refine ⟨719657159736064959559457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479771439824043306372971 719657159736064959559457)
            ·
              refine ⟨539742869802048719669593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719657159736064959559457 539742869802048719669593)
              ·
                refine ⟨404807152351536539752195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539742869802048719669593 404807152351536539752195)
                ·
                  refine ⟨607210728527304809628293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404807152351536539752195 607210728527304809628293)
                  ·
                    refine ⟨113852011598869651805305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 607210728527304809628293 113852011598869651805305)
                    ·
                      rfl

theorem cell22_332589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_332589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332589 prefixEnd_332589 := by exact prefixLift 332589
  have htrace : WordTrace (prefixWord ++ tailWord_332589) baseStart_332589 baseEnd_332589 := by
    simpa [prefixWord, tailWord_332589, baseEnd_332589] using wordTrace_append hprefix tailTrace_332589
  have hstable : (prefixWord ++ tailWord_332589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332589).length < 2 ^ (prefixWord ++ tailWord_332589).sum := by decide
  have hdescent : baseEnd_332589 < baseStart_332589 := by decide
  rcases family_descends (prefixWord ++ tailWord_332589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332694 : List Nat := [5, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_332694 : Nat := 118140960795 + 332694 * 2 ^ 59
def prefixEnd_332694 : Nat := 4983230072969 + 3 ^ 40 * 332694 * 2
def baseEnd_332694 : Nat := 37962651748228125976661

theorem tailTrace_332694 : CollatzResearch.WordTrace tailWord_332694 prefixEnd_332694 37962651748228125976661 := by
  unfold tailWord_332694
  simp only [CollatzResearch.WordTrace]
  refine ⟨758396691044620778541821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8089564704475954971112757 758396691044620778541821)
  ·
    refine ⟨284398759141732791953183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 758396691044620778541821 284398759141732791953183)
    ·
      refine ⟨426598138712599187929775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284398759141732791953183 426598138712599187929775)
      ·
        refine ⟨639897208068898781894663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426598138712599187929775 639897208068898781894663)
        ·
          refine ⟨959845812103348172841995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639897208068898781894663 959845812103348172841995)
          ·
            refine ⟨1439768718155022259262993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959845812103348172841995 1439768718155022259262993)
            ·
              refine ⟨1079826538616266694447245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439768718155022259262993 1079826538616266694447245)
              ·
                refine ⟨404934951981100010417717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1079826538616266694447245 404934951981100010417717)
                ·
                  refine ⟨37962651748228125976661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 404934951981100010417717 37962651748228125976661)
                  ·
                    rfl

theorem cell22_332694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_332694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332694 prefixEnd_332694 := by exact prefixLift 332694
  have htrace : WordTrace (prefixWord ++ tailWord_332694) baseStart_332694 baseEnd_332694 := by
    simpa [prefixWord, tailWord_332694, baseEnd_332694] using wordTrace_append hprefix tailTrace_332694
  have hstable : (prefixWord ++ tailWord_332694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332694).length < 2 ^ (prefixWord ++ tailWord_332694).sum := by decide
  have hdescent : baseEnd_332694 < baseStart_332694 := by decide
  rcases family_descends (prefixWord ++ tailWord_332694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332705 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 6]
def baseStart_332705 : Nat := 118140960795 + 332705 * 2 ^ 59
def prefixEnd_332705 : Nat := 4983230072969 + 3 ^ 40 * 332705 * 2
def baseEnd_332705 : Nat := 37963906923161338634983

theorem tailTrace_332705 : CollatzResearch.WordTrace tailWord_332705 prefixEnd_332705 37963906923161338634983 := by
  unfold tailWord_332705
  simp only [CollatzResearch.WordTrace]
  refine ⟨12134748259674081335319569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8089832173116054223546379 12134748259674081335319569)
  ·
    refine ⟨9101061194755561001489677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12134748259674081335319569 9101061194755561001489677)
    ·
      refine ⟨3412897948033335375558629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9101061194755561001489677 3412897948033335375558629)
      ·
        refine ⟨639918365256250382917243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3412897948033335375558629 639918365256250382917243)
        ·
          refine ⟨959877547884375574375865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639918365256250382917243 959877547884375574375865)
          ·
            refine ⟨719908160913281680781899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 959877547884375574375865 719908160913281680781899)
            ·
              refine ⟨1079862241369922521172849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719908160913281680781899 1079862241369922521172849)
              ·
                refine ⟨809896681027441890879637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079862241369922521172849 809896681027441890879637)
                ·
                  refine ⟨37963906923161338634983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 809896681027441890879637 37963906923161338634983)
                  ·
                    rfl

theorem cell22_332705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_332705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332705 prefixEnd_332705 := by exact prefixLift 332705
  have htrace : WordTrace (prefixWord ++ tailWord_332705) baseStart_332705 baseEnd_332705 := by
    simpa [prefixWord, tailWord_332705, baseEnd_332705] using wordTrace_append hprefix tailTrace_332705
  have hstable : (prefixWord ++ tailWord_332705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332705).length < 2 ^ (prefixWord ++ tailWord_332705).sum := by decide
  have hdescent : baseEnd_332705 < baseStart_332705 := by decide
  rcases family_descends (prefixWord ++ tailWord_332705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332724 : List Nat := [2, 5, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_332724 : Nat := 118140960795 + 332724 * 2 ^ 59
def prefixEnd_332724 : Nat := 4983230072969 + 3 ^ 40 * 332724 * 2
def baseEnd_332724 : Nat := 113898224857774299679891

theorem tailTrace_332724 : CollatzResearch.WordTrace tailWord_332724 prefixEnd_332724 113898224857774299679891 := by
  unfold tailWord_332724
  simp only [CollatzResearch.WordTrace]
  refine ⟨6067720623302623790130613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8090294164403498386840817 6067720623302623790130613)
  ·
    refine ⟨568848808434620980324745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6067720623302623790130613 568848808434620980324745)
    ·
      refine ⟨426636606325965735243559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 568848808434620980324745 426636606325965735243559)
      ·
        refine ⟨639954909488948602865339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426636606325965735243559 639954909488948602865339)
        ·
          refine ⟨959932364233422904298009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639954909488948602865339 959932364233422904298009)
          ·
            refine ⟨719949273175067178223507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 959932364233422904298009 719949273175067178223507)
            ·
              refine ⟨1079923909762600767335261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719949273175067178223507 1079923909762600767335261)
              ·
                refine ⟨404971466160975287750723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1079923909762600767335261 404971466160975287750723)
                ·
                  refine ⟨607457199241462931626085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404971466160975287750723 607457199241462931626085)
                  ·
                    refine ⟨113898224857774299679891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 607457199241462931626085 113898224857774299679891)
                    ·
                      rfl

theorem cell22_332724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_332724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332724 prefixEnd_332724 := by exact prefixLift 332724
  have htrace : WordTrace (prefixWord ++ tailWord_332724) baseStart_332724 baseEnd_332724 := by
    simpa [prefixWord, tailWord_332724, baseEnd_332724] using wordTrace_append hprefix tailTrace_332724
  have hstable : (prefixWord ++ tailWord_332724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332724).length < 2 ^ (prefixWord ++ tailWord_332724).sum := by decide
  have hdescent : baseEnd_332724 < baseStart_332724 := by decide
  rcases family_descends (prefixWord ++ tailWord_332724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332767 : List Nat := [1, 1, 2, 3, 5, 2, 2, 6]
def baseStart_332767 : Nat := 118140960795 + 332767 * 2 ^ 59
def prefixEnd_332767 : Nat := 4983230072969 + 3 ^ 40 * 332767 * 2
def baseEnd_332767 : Nat := 12656993848504057872751

theorem tailTrace_332767 : CollatzResearch.WordTrace tailWord_332767 prefixEnd_332767 12656993848504057872751 := by
  unfold tailWord_332767
  simp only [CollatzResearch.WordTrace]
  refine ⟨12137009585449465924076555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8091339723632977282717703 12137009585449465924076555)
  ·
    refine ⟨18205514378174198886114833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12137009585449465924076555 18205514378174198886114833)
    ·
      refine ⟨13654135783630649164586125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18205514378174198886114833 13654135783630649164586125)
      ·
        refine ⟨5120300918861493436719797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13654135783630649164586125 5120300918861493436719797)
        ·
          refine ⟨480028211143265009692481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5120300918861493436719797 480028211143265009692481)
          ·
            refine ⟨360021158357448757269361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480028211143265009692481 360021158357448757269361)
            ·
              refine ⟨270015868768086567952021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360021158357448757269361 270015868768086567952021)
              ·
                refine ⟨12656993848504057872751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 270015868768086567952021 12656993848504057872751)
                ·
                  rfl

theorem cell22_332767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 6].length) (baseStart_332767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332767 prefixEnd_332767 := by exact prefixLift 332767
  have htrace : WordTrace (prefixWord ++ tailWord_332767) baseStart_332767 baseEnd_332767 := by
    simpa [prefixWord, tailWord_332767, baseEnd_332767] using wordTrace_append hprefix tailTrace_332767
  have hstable : (prefixWord ++ tailWord_332767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332767).length < 2 ^ (prefixWord ++ tailWord_332767).sum := by decide
  have hdescent : baseEnd_332767 < baseStart_332767 := by decide
  rcases family_descends (prefixWord ++ tailWord_332767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332812 : List Nat := [2, 2, 1, 2, 3, 2, 4, 1, 5]
def baseStart_332812 : Nat := 118140960795 + 332812 * 2 ^ 59
def prefixEnd_332812 : Nat := 4983230072969 + 3 ^ 40 * 332812 * 2
def baseEnd_332812 : Nat := 37976116352057134493207

theorem tailTrace_332812 : CollatzResearch.WordTrace tailWord_332812 prefixEnd_332812 37976116352057134493207 := by
  unfold tailWord_332812
  simp only [CollatzResearch.WordTrace]
  refine ⟨6069325435143219304732345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8092433913524292406309793 6069325435143219304732345)
  ·
    refine ⟨4551994076357414478549259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6069325435143219304732345 4551994076357414478549259)
    ·
      refine ⟨6827991114536121717823889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4551994076357414478549259 6827991114536121717823889)
      ·
        refine ⟨5120993335902091288367917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6827991114536121717823889 5120993335902091288367917)
        ·
          refine ⟨1920372500963284233137969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5120993335902091288367917 1920372500963284233137969)
          ·
            refine ⟨1440279375722463174853477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1920372500963284233137969 1440279375722463174853477)
            ·
              refine ⟨270052382947961845285027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1440279375722463174853477 270052382947961845285027)
              ·
                refine ⟨405078574421942767927541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270052382947961845285027 405078574421942767927541)
                ·
                  refine ⟨37976116352057134493207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 405078574421942767927541 37976116352057134493207)
                  ·
                    rfl

theorem cell22_332812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_332812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332812 prefixEnd_332812 := by exact prefixLift 332812
  have htrace : WordTrace (prefixWord ++ tailWord_332812) baseStart_332812 baseEnd_332812 := by
    simpa [prefixWord, tailWord_332812, baseEnd_332812] using wordTrace_append hprefix tailTrace_332812
  have hstable : (prefixWord ++ tailWord_332812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332812).length < 2 ^ (prefixWord ++ tailWord_332812).sum := by decide
  have hdescent : baseEnd_332812 < baseStart_332812 := by decide
  rcases family_descends (prefixWord ++ tailWord_332812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332872 : List Nat := [2, 1, 3, 1, 1, 1, 3, 5, 2, 3]
def baseStart_332872 : Nat := 118140960795 + 332872 * 2 ^ 59
def prefixEnd_332872 : Nat := 4983230072969 + 3 ^ 40 * 332872 * 2
def baseEnd_332872 : Nat := 113948888282351246979437

theorem tailTrace_332872 : CollatzResearch.WordTrace tailWord_332872 prefixEnd_332872 113948888282351246979437 := by
  unfold tailWord_332872
  simp only [CollatzResearch.WordTrace]
  refine ⟨6070419625034534428324435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8093892833379379237765913 6070419625034534428324435)
  ·
    refine ⟨9105629437551801642486653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6070419625034534428324435 9105629437551801642486653)
    ·
      refine ⟨3414611039081925615932495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9105629437551801642486653 3414611039081925615932495)
      ·
        refine ⟨5121916558622888423898743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3414611039081925615932495 5121916558622888423898743)
        ·
          refine ⟨7682874837934332635848115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5121916558622888423898743 7682874837934332635848115)
          ·
            refine ⟨11524312256901498953772173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7682874837934332635848115 11524312256901498953772173)
            ·
              refine ⟨4321617096338062107664565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11524312256901498953772173 4321617096338062107664565)
              ·
                refine ⟨405151602781693322593553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4321617096338062107664565 405151602781693322593553)
                ·
                  refine ⟨303863702086269991945165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405151602781693322593553 303863702086269991945165)
                  ·
                    refine ⟨113948888282351246979437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 303863702086269991945165 113948888282351246979437)
                    ·
                      rfl

theorem cell22_332872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_332872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332872 prefixEnd_332872 := by exact prefixLift 332872
  have htrace : WordTrace (prefixWord ++ tailWord_332872) baseStart_332872 baseEnd_332872 := by
    simpa [prefixWord, tailWord_332872, baseEnd_332872] using wordTrace_append hprefix tailTrace_332872
  have hstable : (prefixWord ++ tailWord_332872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332872).length < 2 ^ (prefixWord ++ tailWord_332872).sum := by decide
  have hdescent : baseEnd_332872 < baseStart_332872 := by decide
  rcases family_descends (prefixWord ++ tailWord_332872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332893 : List Nat := [1, 4, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_332893 : Nat := 118140960795 + 332893 * 2 ^ 59
def prefixEnd_332893 : Nat := 4983230072969 + 3 ^ 40 * 332893 * 2
def baseEnd_332893 : Nat := 113956077011514192204373

theorem tailTrace_332893 : CollatzResearch.WordTrace tailWord_332893 prefixEnd_332893 113956077011514192204373 := by
  unfold tailWord_332893
  simp only [CollatzResearch.WordTrace]
  refine ⟨12141605182992989443163333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8094403455328659628775555 12141605182992989443163333)
  ·
    refine ⟨2276550971811185520593125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12141605182992989443163333 2276550971811185520593125)
    ·
      refine ⟨426853307214597285111211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2276550971811185520593125 426853307214597285111211)
      ·
        refine ⟨640279960821895927666817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426853307214597285111211 640279960821895927666817)
        ·
          refine ⟨480209970616421945750113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 640279960821895927666817 480209970616421945750113)
          ·
            refine ⟨360157477962316459312585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480209970616421945750113 360157477962316459312585)
            ·
              refine ⟨270118108471737344484439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360157477962316459312585 270118108471737344484439)
              ·
                refine ⟨405177162707606016726659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270118108471737344484439 405177162707606016726659)
                ·
                  refine ⟨607765744061409025089989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405177162707606016726659 607765744061409025089989)
                  ·
                    refine ⟨113956077011514192204373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 607765744061409025089989 113956077011514192204373)
                    ·
                      rfl

theorem cell22_332893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_332893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332893 prefixEnd_332893 := by exact prefixLift 332893
  have htrace : WordTrace (prefixWord ++ tailWord_332893) baseStart_332893 baseEnd_332893 := by
    simpa [prefixWord, tailWord_332893, baseEnd_332893] using wordTrace_append hprefix tailTrace_332893
  have hstable : (prefixWord ++ tailWord_332893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332893).length < 2 ^ (prefixWord ++ tailWord_332893).sum := by decide
  have hdescent : baseEnd_332893 < baseStart_332893 := by decide
  rcases family_descends (prefixWord ++ tailWord_332893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332906 : List Nat := [3, 1, 3, 2, 2, 3, 1, 2, 2, 3]
def baseStart_332906 : Nat := 118140960795 + 332906 * 2 ^ 59
def prefixEnd_332906 : Nat := 4983230072969 + 3 ^ 40 * 332906 * 2
def baseEnd_332906 : Nat := 113960527177186491629333

theorem tailTrace_332906 : CollatzResearch.WordTrace tailWord_332906 prefixEnd_332906 113960527177186491629333 := by
  unfold tailWord_332906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3035519832986473165846643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8094719554630595108924381 3035519832986473165846643)
  ·
    refine ⟨4553279749479709748769965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3035519832986473165846643 4553279749479709748769965)
    ·
      refine ⟨1707479906054891155788737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4553279749479709748769965 1707479906054891155788737)
      ·
        refine ⟨1280609929541168366841553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1707479906054891155788737 1280609929541168366841553)
        ·
          refine ⟨960457447155876275131165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1280609929541168366841553 960457447155876275131165)
          ·
            refine ⟨360171542683453603174187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 960457447155876275131165 360171542683453603174187)
            ·
              refine ⟨540257314025180404761281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360171542683453603174187 540257314025180404761281)
              ·
                refine ⟨405192985518885303570961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540257314025180404761281 405192985518885303570961)
                ·
                  refine ⟨303894739139163977678221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405192985518885303570961 303894739139163977678221)
                  ·
                    refine ⟨113960527177186491629333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 303894739139163977678221 113960527177186491629333)
                    ·
                      rfl

theorem cell22_332906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_332906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332906 prefixEnd_332906 := by exact prefixLift 332906
  have htrace : WordTrace (prefixWord ++ tailWord_332906) baseStart_332906 baseEnd_332906 := by
    simpa [prefixWord, tailWord_332906, baseEnd_332906] using wordTrace_append hprefix tailTrace_332906
  have hstable : (prefixWord ++ tailWord_332906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332906).length < 2 ^ (prefixWord ++ tailWord_332906).sum := by decide
  have hdescent : baseEnd_332906 < baseStart_332906 := by decide
  rcases family_descends (prefixWord ++ tailWord_332906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332936 : List Nat := [2, 1, 3, 4, 3, 1, 2, 6]
def baseStart_332936 : Nat := 118140960795 + 332936 * 2 ^ 59
def prefixEnd_332936 : Nat := 4983230072969 + 3 ^ 40 * 332936 * 2
def baseEnd_332936 : Nat := 12663421865586268153249

theorem tailTrace_332936 : CollatzResearch.WordTrace tailWord_332936 prefixEnd_332936 12663421865586268153249 := by
  unfold tailWord_332936
  simp only [CollatzResearch.WordTrace]
  refine ⟨6071586760918603893489331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8095449014558138524652441 6071586760918603893489331)
  ·
    refine ⟨9107380141377905840233997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6071586760918603893489331 9107380141377905840233997)
    ·
      refine ⟨3415267553016714690087749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9107380141377905840233997 3415267553016714690087749)
      ·
        refine ⟨640362666190634004391453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3415267553016714690087749 640362666190634004391453)
        ·
          refine ⟨240135999821487751646795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 640362666190634004391453 240135999821487751646795)
          ·
            refine ⟨360203999732231627470193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240135999821487751646795 360203999732231627470193)
            ·
              refine ⟨270152999799173720602645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360203999732231627470193 270152999799173720602645)
              ·
                refine ⟨12663421865586268153249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 270152999799173720602645 12663421865586268153249)
                ·
                  rfl

theorem cell22_332936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 6].length) (baseStart_332936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332936 prefixEnd_332936 := by exact prefixLift 332936
  have htrace : WordTrace (prefixWord ++ tailWord_332936) baseStart_332936 baseEnd_332936 := by
    simpa [prefixWord, tailWord_332936, baseEnd_332936] using wordTrace_append hprefix tailTrace_332936
  have hstable : (prefixWord ++ tailWord_332936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332936).length < 2 ^ (prefixWord ++ tailWord_332936).sum := by decide
  have hdescent : baseEnd_332936 < baseStart_332936 := by decide
  rcases family_descends (prefixWord ++ tailWord_332936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332951 : List Nat := [1, 1, 3, 3, 3, 1, 3, 3, 1, 3]
def baseStart_332951 : Nat := 118140960795 + 332951 * 2 ^ 59
def prefixEnd_332951 : Nat := 4983230072969 + 3 ^ 40 * 332951 * 2
def baseEnd_332951 : Nat := 113975931596821374254195

theorem tailTrace_332951 : CollatzResearch.WordTrace tailWord_332951 prefixEnd_332951 113975931596821374254195 := by
  unfold tailWord_332951
  simp only [CollatzResearch.WordTrace]
  refine ⟨12143720616782865348774707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8095813744521910232516471 12143720616782865348774707)
  ·
    refine ⟨18215580925174298023162061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12143720616782865348774707 18215580925174298023162061)
    ·
      refine ⟨6830842846940361758685773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18215580925174298023162061 6830842846940361758685773)
      ·
        refine ⟨2561566067602635659507165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6830842846940361758685773 2561566067602635659507165)
        ·
          refine ⟨960587275350988372315187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2561566067602635659507165 960587275350988372315187)
          ·
            refine ⟨1440880913026482558472781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960587275350988372315187 1440880913026482558472781)
            ·
              refine ⟨540330342384930959427293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1440880913026482558472781 540330342384930959427293)
              ·
                refine ⟨202623878394349109785235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 540330342384930959427293 202623878394349109785235)
                ·
                  refine ⟨303935817591523664677853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202623878394349109785235 303935817591523664677853)
                  ·
                    refine ⟨113975931596821374254195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 303935817591523664677853 113975931596821374254195)
                    ·
                      rfl

theorem cell22_332951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_332951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_332951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_332951 prefixEnd_332951 := by exact prefixLift 332951
  have htrace : WordTrace (prefixWord ++ tailWord_332951) baseStart_332951 baseEnd_332951 := by
    simpa [prefixWord, tailWord_332951, baseEnd_332951] using wordTrace_append hprefix tailTrace_332951
  have hstable : (prefixWord ++ tailWord_332951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332951).length < 2 ^ (prefixWord ++ tailWord_332951).sum := by decide
  have hdescent : baseEnd_332951 < baseStart_332951 := by decide
  rcases family_descends (prefixWord ++ tailWord_332951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333007 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 4, 3]
def baseStart_333007 : Nat := 118140960795 + 333007 * 2 ^ 59
def prefixEnd_333007 : Nat := 4983230072969 + 3 ^ 40 * 333007 * 2
def baseEnd_333007 : Nat := 113995101541255894854023

theorem tailTrace_333007 : CollatzResearch.WordTrace tailWord_333007 prefixEnd_333007 113995101541255894854023 := by
  unfold tailWord_333007
  simp only [CollatzResearch.WordTrace]
  refine ⟨12145763104579986912813275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8097175403053324608542183 12145763104579986912813275)
  ·
    refine ⟨18218644656869980369219913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12145763104579986912813275 18218644656869980369219913)
    ·
      refine ⟨13663983492652485276914935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18218644656869980369219913 13663983492652485276914935)
      ·
        refine ⟨20495975238978727915372403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13663983492652485276914935 20495975238978727915372403)
        ·
          refine ⟨30743962858468091873058605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20495975238978727915372403 30743962858468091873058605)
          ·
            refine ⟨11528986071925534452396977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30743962858468091873058605 11528986071925534452396977)
            ·
              refine ⟨8646739553944150839297733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11528986071925534452396977 8646739553944150839297733)
              ·
                refine ⟨1621263666364528282368325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8646739553944150839297733 1621263666364528282368325)
                ·
                  refine ⟨303986937443349052944061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1621263666364528282368325 303986937443349052944061)
                  ·
                    refine ⟨113995101541255894854023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 303986937443349052944061 113995101541255894854023)
                    ·
                      rfl

theorem cell22_333007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 3].length) (baseStart_333007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333007 prefixEnd_333007 := by exact prefixLift 333007
  have htrace : WordTrace (prefixWord ++ tailWord_333007) baseStart_333007 baseEnd_333007 := by
    simpa [prefixWord, tailWord_333007, baseEnd_333007] using wordTrace_append hprefix tailTrace_333007
  have hstable : (prefixWord ++ tailWord_333007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333007).length < 2 ^ (prefixWord ++ tailWord_333007).sum := by decide
  have hdescent : baseEnd_333007 < baseStart_333007 := by decide
  rcases family_descends (prefixWord ++ tailWord_333007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333024 : List Nat := [2, 1, 1, 3, 1, 4, 1, 4, 2, 3]
def baseStart_333024 : Nat := 118140960795 + 333024 * 2 ^ 59
def prefixEnd_333024 : Nat := 4983230072969 + 3 ^ 40 * 333024 * 2
def baseEnd_333024 : Nat := 114000920988673517178971

theorem tailTrace_333024 : CollatzResearch.WordTrace tailWord_333024 prefixEnd_333024 114000920988673517178971 := by
  unfold tailWord_333024
  simp only [CollatzResearch.WordTrace]
  refine ⟨6073191572759199408091063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8097588763678932544121417 6073191572759199408091063)
  ·
    refine ⟨9109787359138799112136595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6073191572759199408091063 9109787359138799112136595)
    ·
      refine ⟨13664681038708198668204893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9109787359138799112136595 13664681038708198668204893)
      ·
        refine ⟨5124255389515574500576835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13664681038708198668204893 5124255389515574500576835)
        ·
          refine ⟨7686383084273361750865253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5124255389515574500576835 7686383084273361750865253)
          ·
            refine ⟨1441196828301255328287235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7686383084273361750865253 1441196828301255328287235)
            ·
              refine ⟨2161795242451882992430853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1441196828301255328287235 2161795242451882992430853)
              ·
                refine ⟨405336607959728061080785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2161795242451882992430853 405336607959728061080785)
                ·
                  refine ⟨304002455969796045810589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405336607959728061080785 304002455969796045810589)
                  ·
                    refine ⟨114000920988673517178971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304002455969796045810589 114000920988673517178971)
                    ·
                      rfl

theorem cell22_333024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 2, 3].length) (baseStart_333024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333024 prefixEnd_333024 := by exact prefixLift 333024
  have htrace : WordTrace (prefixWord ++ tailWord_333024) baseStart_333024 baseEnd_333024 := by
    simpa [prefixWord, tailWord_333024, baseEnd_333024] using wordTrace_append hprefix tailTrace_333024
  have hstable : (prefixWord ++ tailWord_333024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333024).length < 2 ^ (prefixWord ++ tailWord_333024).sum := by decide
  have hdescent : baseEnd_333024 < baseStart_333024 := by decide
  rcases family_descends (prefixWord ++ tailWord_333024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333129 : List Nat := [1, 2, 1, 1, 2, 3, 4, 3, 1, 4]
def baseStart_333129 : Nat := 118140960795 + 333129 * 2 ^ 59
def prefixEnd_333129 : Nat := 4983230072969 + 3 ^ 40 * 333129 * 2
def baseEnd_333129 : Nat := 114036864634488243303649

theorem tailTrace_333129 : CollatzResearch.WordTrace tailWord_333129 prefixEnd_333129 114036864634488243303649 := by
  unfold tailWord_333129
  simp only [CollatzResearch.WordTrace]
  refine ⟨12150212810138001748754441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8100141873425334499169627 12150212810138001748754441)
  ·
    refine ⟨9112659607603501311565831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12150212810138001748754441 9112659607603501311565831)
    ·
      refine ⟨13668989411405251967348747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9112659607603501311565831 13668989411405251967348747)
      ·
        refine ⟨20503484117107877951023121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13668989411405251967348747 20503484117107877951023121)
        ·
          refine ⟨15377613087830908463267341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20503484117107877951023121 15377613087830908463267341)
          ·
            refine ⟨5766604907936590673725253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15377613087830908463267341 5766604907936590673725253)
            ·
              refine ⟨1081238420238110751323485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5766604907936590673725253 1081238420238110751323485)
              ·
                refine ⟨405464407589291531746307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1081238420238110751323485 405464407589291531746307)
                ·
                  refine ⟨608196611383937297619461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405464407589291531746307 608196611383937297619461)
                  ·
                    refine ⟨114036864634488243303649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 608196611383937297619461 114036864634488243303649)
                    ·
                      rfl

theorem cell22_333129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_333129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333129 prefixEnd_333129 := by exact prefixLift 333129
  have htrace : WordTrace (prefixWord ++ tailWord_333129) baseStart_333129 baseEnd_333129 := by
    simpa [prefixWord, tailWord_333129, baseEnd_333129] using wordTrace_append hprefix tailTrace_333129
  have hstable : (prefixWord ++ tailWord_333129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333129).length < 2 ^ (prefixWord ++ tailWord_333129).sum := by decide
  have hdescent : baseEnd_333129 < baseStart_333129 := by decide
  rcases family_descends (prefixWord ++ tailWord_333129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333193 : List Nat := [1, 2, 1, 1, 7, 1, 2, 2, 2, 3]
def baseStart_333193 : Nat := 118140960795 + 333193 * 2 ^ 59
def prefixEnd_333193 : Nat := 4983230072969 + 3 ^ 40 * 333193 * 2
def baseEnd_333193 : Nat := 114058773142413409703453

theorem tailTrace_333193 : CollatzResearch.WordTrace tailWord_333193 prefixEnd_333193 114058773142413409703453 := by
  unfold tailWord_333193
  simp only [CollatzResearch.WordTrace]
  refine ⟨12152547081906140679084233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8101698054604093786056155 12152547081906140679084233)
  ·
    refine ⟨9114410311429605509313175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12152547081906140679084233 9114410311429605509313175)
    ·
      refine ⟨13671615467144408263969763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9114410311429605509313175 13671615467144408263969763)
      ·
        refine ⟨20507423200716612395954645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13671615467144408263969763 20507423200716612395954645)
        ·
          refine ⟨480642731266795603030187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 20507423200716612395954645 480642731266795603030187)
          ·
            refine ⟨720964096900193404545281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480642731266795603030187 720964096900193404545281)
            ·
              refine ⟨540723072675145053408961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 720964096900193404545281 540723072675145053408961)
              ·
                refine ⟨405542304506358790056721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540723072675145053408961 405542304506358790056721)
                ·
                  refine ⟨304156728379769092542541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405542304506358790056721 304156728379769092542541)
                  ·
                    refine ⟨114058773142413409703453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304156728379769092542541 114058773142413409703453)
                    ·
                      rfl

theorem cell22_333193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 3].length) (baseStart_333193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333193 prefixEnd_333193 := by exact prefixLift 333193
  have htrace : WordTrace (prefixWord ++ tailWord_333193) baseStart_333193 baseEnd_333193 := by
    simpa [prefixWord, tailWord_333193, baseEnd_333193] using wordTrace_append hprefix tailTrace_333193
  have hstable : (prefixWord ++ tailWord_333193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333193).length < 2 ^ (prefixWord ++ tailWord_333193).sum := by decide
  have hdescent : baseEnd_333193 < baseStart_333193 := by decide
  rcases family_descends (prefixWord ++ tailWord_333193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333279 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 6]
def baseStart_333279 : Nat := 118140960795 + 333279 * 2 ^ 59
def prefixEnd_333279 : Nat := 4983230072969 + 3 ^ 40 * 333279 * 2
def baseEnd_333279 : Nat := 38029404233312617351063

theorem tailTrace_333279 : CollatzResearch.WordTrace tailWord_333279 prefixEnd_333279 38029404233312617351063 := by
  unfold tailWord_333279
  simp only [CollatzResearch.WordTrace]
  refine ⟨12155683759594577366714891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8103789173063051577809927 12155683759594577366714891)
  ·
    refine ⟨18233525639391866050072337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12155683759594577366714891 18233525639391866050072337)
    ·
      refine ⟨13675144229543899537554253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18233525639391866050072337 13675144229543899537554253)
      ·
        refine ⟨5128179086078962326582845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13675144229543899537554253 5128179086078962326582845)
        ·
          refine ⟨1923067157279610872468567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5128179086078962326582845 1923067157279610872468567)
          ·
            refine ⟨2884600735919416308702851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923067157279610872468567 2884600735919416308702851)
            ·
              refine ⟨4326901103879124463054277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2884600735919416308702851 4326901103879124463054277)
              ·
                refine ⟨811293956977335836822677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4326901103879124463054277 811293956977335836822677)
                ·
                  refine ⟨38029404233312617351063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 811293956977335836822677 38029404233312617351063)
                  ·
                    rfl

theorem cell22_333279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 6].length) (baseStart_333279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333279 prefixEnd_333279 := by exact prefixLift 333279
  have htrace : WordTrace (prefixWord ++ tailWord_333279) baseStart_333279 baseEnd_333279 := by
    simpa [prefixWord, tailWord_333279, baseEnd_333279] using wordTrace_append hprefix tailTrace_333279
  have hstable : (prefixWord ++ tailWord_333279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333279).length < 2 ^ (prefixWord ++ tailWord_333279).sum := by decide
  have hdescent : baseEnd_333279 < baseStart_333279 := by decide
  rcases family_descends (prefixWord ++ tailWord_333279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333281 : List Nat := [1, 2, 3, 1, 2, 3, 1, 4, 1, 4]
def baseStart_333281 : Nat := 118140960795 + 333281 * 2 ^ 59
def prefixEnd_333281 : Nat := 4983230072969 + 3 ^ 40 * 333281 * 2
def baseEnd_333281 : Nat := 114088897340810513503183

theorem tailTrace_333281 : CollatzResearch.WordTrace tailWord_333281 prefixEnd_333281 114088897340810513503183 := by
  unfold tailWord_333281
  simp only [CollatzResearch.WordTrace]
  refine ⟨12155756705587331708287697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8103837803724887805525131 12155756705587331708287697)
  ·
    refine ⟨9116817529190498781215773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12155756705587331708287697 9116817529190498781215773)
    ·
      refine ⟨3418806573446437042955915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9116817529190498781215773 3418806573446437042955915)
      ·
        refine ⟨5128209860169655564433873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3418806573446437042955915 5128209860169655564433873)
        ·
          refine ⟨3846157395127241673325405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5128209860169655564433873 3846157395127241673325405)
          ·
            refine ⟨1442309023172715627497027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3846157395127241673325405 1442309023172715627497027)
            ·
              refine ⟨2163463534759073441245541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442309023172715627497027 2163463534759073441245541)
              ·
                refine ⟨405649412767326270233539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2163463534759073441245541 405649412767326270233539)
                ·
                  refine ⟨608474119150989405350309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405649412767326270233539 608474119150989405350309)
                  ·
                    refine ⟨114088897340810513503183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 608474119150989405350309 114088897340810513503183)
                    ·
                      rfl

theorem cell22_333281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_333281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333281 prefixEnd_333281 := by exact prefixLift 333281
  have htrace : WordTrace (prefixWord ++ tailWord_333281) baseStart_333281 baseEnd_333281 := by
    simpa [prefixWord, tailWord_333281, baseEnd_333281] using wordTrace_append hprefix tailTrace_333281
  have hstable : (prefixWord ++ tailWord_333281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333281).length < 2 ^ (prefixWord ++ tailWord_333281).sum := by decide
  have hdescent : baseEnd_333281 < baseStart_333281 := by decide
  rcases family_descends (prefixWord ++ tailWord_333281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333298 : List Nat := [3, 2, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_333298 : Nat := 118140960795 + 333298 * 2 ^ 59
def prefixEnd_333298 : Nat := 4983230072969 + 3 ^ 40 * 333298 * 2
def baseEnd_333298 : Nat := 114094716788228135828131

theorem tailTrace_333298 : CollatzResearch.WordTrace tailWord_333298 prefixEnd_333298 114094716788228135828131 := by
  unfold tailWord_333298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3039094186631435902914137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8104251164350495741104365 3039094186631435902914137)
  ·
    refine ⟨2279320639973576927185603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3039094186631435902914137 2279320639973576927185603)
    ·
      refine ⟨3418980959960365390778405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2279320639973576927185603 3418980959960365390778405)
      ·
        refine ⟨641058929992568510770951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3418980959960365390778405 641058929992568510770951)
        ·
          refine ⟨961588394988852766156427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641058929992568510770951 961588394988852766156427)
          ·
            refine ⟨1442382592483279149234641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961588394988852766156427 1442382592483279149234641)
            ·
              refine ⟨1081786944362459361925981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442382592483279149234641 1081786944362459361925981)
              ·
                refine ⟨405670104135922260722243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1081786944362459361925981 405670104135922260722243)
                ·
                  refine ⟨608505156203883391083365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405670104135922260722243 608505156203883391083365)
                  ·
                    refine ⟨114094716788228135828131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 608505156203883391083365 114094716788228135828131)
                    ·
                      rfl

theorem cell22_333298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_333298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333298 prefixEnd_333298 := by exact prefixLift 333298
  have htrace : WordTrace (prefixWord ++ tailWord_333298) baseStart_333298 baseEnd_333298 := by
    simpa [prefixWord, tailWord_333298, baseEnd_333298] using wordTrace_append hprefix tailTrace_333298
  have hstable : (prefixWord ++ tailWord_333298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333298).length < 2 ^ (prefixWord ++ tailWord_333298).sum := by decide
  have hdescent : baseEnd_333298 < baseStart_333298 := by decide
  rcases family_descends (prefixWord ++ tailWord_333298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333313 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 6]
def baseStart_333313 : Nat := 118140960795 + 333313 * 2 ^ 59
def prefixEnd_333313 : Nat := 4983230072969 + 3 ^ 40 * 333313 * 2
def baseEnd_333313 : Nat := 38033283864924365567695

theorem tailTrace_333313 : CollatzResearch.WordTrace tailWord_333313 prefixEnd_333313 38033283864924365567695 := by
  unfold tailWord_333313
  simp only [CollatzResearch.WordTrace]
  refine ⟨12156923841471401173452593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8104615894314267448968395 12156923841471401173452593)
  ·
    refine ⟨9117692881103550880089445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12156923841471401173452593 9117692881103550880089445)
    ·
      refine ⟨1709567415206915790016771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9117692881103550880089445 1709567415206915790016771)
      ·
        refine ⟨2564351122810373685025157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709567415206915790016771 2564351122810373685025157)
        ·
          refine ⟨480815835526945065942217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2564351122810373685025157 480815835526945065942217)
          ·
            refine ⟨360611876645208799456663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480815835526945065942217 360611876645208799456663)
            ·
              refine ⟨540917814967813199184995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360611876645208799456663 540917814967813199184995)
              ·
                refine ⟨811376722451719798777493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540917814967813199184995 811376722451719798777493)
                ·
                  refine ⟨38033283864924365567695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 811376722451719798777493 38033283864924365567695)
                  ·
                    rfl

theorem cell22_333313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 6].length) (baseStart_333313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333313 prefixEnd_333313 := by exact prefixLift 333313
  have htrace : WordTrace (prefixWord ++ tailWord_333313) baseStart_333313 baseEnd_333313 := by
    simpa [prefixWord, tailWord_333313, baseEnd_333313] using wordTrace_append hprefix tailTrace_333313
  have hstable : (prefixWord ++ tailWord_333313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333313).length < 2 ^ (prefixWord ++ tailWord_333313).sum := by decide
  have hdescent : baseEnd_333313 < baseStart_333313 := by decide
  rcases family_descends (prefixWord ++ tailWord_333313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333332 : List Nat := [2, 4, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_333332 : Nat := 118140960795 + 333332 * 2 ^ 59
def prefixEnd_333332 : Nat := 4983230072969 + 3 ^ 40 * 333332 * 2
def baseEnd_333332 : Nat := 114106355683063380478027

theorem tailTrace_333332 : CollatzResearch.WordTrace tailWord_333332 prefixEnd_333332 114106355683063380478027 := by
  unfold tailWord_333332
  simp only [CollatzResearch.WordTrace]
  refine ⟨6078808414201283709197125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8105077885601711612262833 6078808414201283709197125)
  ·
    refine ⟨1139776577662740695474461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6078808414201283709197125 1139776577662740695474461)
    ·
      refine ⟨427416216623527760802923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1139776577662740695474461 427416216623527760802923)
      ·
        refine ⟨641124324935291641204385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427416216623527760802923 641124324935291641204385)
        ·
          refine ⟨480843243701468730903289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 641124324935291641204385 480843243701468730903289)
          ·
            refine ⟨360632432776101548177467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480843243701468730903289 360632432776101548177467)
            ·
              refine ⟨540948649164152322266201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360632432776101548177467 540948649164152322266201)
              ·
                refine ⟨405711486873114241699651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540948649164152322266201 405711486873114241699651)
                ·
                  refine ⟨608567230309671362549477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405711486873114241699651 608567230309671362549477)
                  ·
                    refine ⟨114106355683063380478027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 608567230309671362549477 114106355683063380478027)
                    ·
                      rfl

theorem cell22_333332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_333332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333332 prefixEnd_333332 := by exact prefixLift 333332
  have htrace : WordTrace (prefixWord ++ tailWord_333332) baseStart_333332 baseEnd_333332 := by
    simpa [prefixWord, tailWord_333332, baseEnd_333332] using wordTrace_append hprefix tailTrace_333332
  have hstable : (prefixWord ++ tailWord_333332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333332).length < 2 ^ (prefixWord ++ tailWord_333332).sum := by decide
  have hdescent : baseEnd_333332 < baseStart_333332 := by decide
  rcases family_descends (prefixWord ++ tailWord_333332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333386 : List Nat := [3, 1, 2, 1, 1, 3, 1, 5, 5]
def baseStart_333386 : Nat := 118140960795 + 333386 * 2 ^ 59
def prefixEnd_333386 : Nat := 4983230072969 + 3 ^ 40 * 333386 * 2
def baseEnd_333386 : Nat := 38041613662208413209287

theorem tailTrace_333386 : CollatzResearch.WordTrace tailWord_333386 prefixEnd_333386 38041613662208413209287 := by
  unfold tailWord_333386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3039896592551733660215003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8106390913471289760573341 3039896592551733660215003)
  ·
    refine ⟨4559844888827600490322505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3039896592551733660215003 4559844888827600490322505)
    ·
      refine ⟨3419883666620700367741879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4559844888827600490322505 3419883666620700367741879)
      ·
        refine ⟨5129825499931050551612819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3419883666620700367741879 5129825499931050551612819)
        ·
          refine ⟨7694738249896575827419229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5129825499931050551612819 7694738249896575827419229)
          ·
            refine ⟨2885526843711215935282211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7694738249896575827419229 2885526843711215935282211)
            ·
              refine ⟨4328290265566823902923317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885526843711215935282211 4328290265566823902923317)
              ·
                refine ⟨405777212396889740899061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4328290265566823902923317 405777212396889740899061)
                ·
                  refine ⟨38041613662208413209287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 405777212396889740899061 38041613662208413209287)
                  ·
                    rfl

theorem cell22_333386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_333386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333386 prefixEnd_333386 := by exact prefixLift 333386
  have htrace : WordTrace (prefixWord ++ tailWord_333386) baseStart_333386 baseEnd_333386 := by
    simpa [prefixWord, tailWord_333386, baseEnd_333386] using wordTrace_append hprefix tailTrace_333386
  have hstable : (prefixWord ++ tailWord_333386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333386).length < 2 ^ (prefixWord ++ tailWord_333386).sum := by decide
  have hdescent : baseEnd_333386 < baseStart_333386 := by decide
  rcases family_descends (prefixWord ++ tailWord_333386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333450 : List Nat := [3, 1, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_333450 : Nat := 118140960795 + 333450 * 2 ^ 59
def prefixEnd_333450 : Nat := 4983230072969 + 3 ^ 40 * 333450 * 2
def baseEnd_333450 : Nat := 114146749494550406027665

theorem tailTrace_333450 : CollatzResearch.WordTrace tailWord_333450 prefixEnd_333450 114146749494550406027665 := by
  unfold tailWord_333450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3040480160493768392797451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8107947094650049047459869 3040480160493768392797451)
  ·
    refine ⟨4560720240740652589196177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3040480160493768392797451 4560720240740652589196177)
    ·
      refine ⟨3420540180555489441897133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4560720240740652589196177 3420540180555489441897133)
      ·
        refine ⟨1282702567708308540711425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3420540180555489441897133 1282702567708308540711425)
        ·
          refine ⟨962026925781231405533569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1282702567708308540711425 962026925781231405533569)
          ·
            refine ⟨721520194335923554150177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 962026925781231405533569 721520194335923554150177)
            ·
              refine ⟨541140145751942665612633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 721520194335923554150177 541140145751942665612633)
              ·
                refine ⟨405855109313956999209475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541140145751942665612633 405855109313956999209475)
                ·
                  refine ⟨608782663970935498814213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405855109313956999209475 608782663970935498814213)
                  ·
                    refine ⟨114146749494550406027665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 608782663970935498814213 114146749494550406027665)
                    ·
                      rfl

theorem cell22_333450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_333450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333450 prefixEnd_333450 := by exact prefixLift 333450
  have htrace : WordTrace (prefixWord ++ tailWord_333450) baseStart_333450 baseEnd_333450 := by
    simpa [prefixWord, tailWord_333450, baseEnd_333450] using wordTrace_append hprefix tailTrace_333450
  have hstable : (prefixWord ++ tailWord_333450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333450).length < 2 ^ (prefixWord ++ tailWord_333450).sum := by decide
  have hdescent : baseEnd_333450 < baseStart_333450 := by decide
  rcases family_descends (prefixWord ++ tailWord_333450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333461 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_333461 : Nat := 118140960795 + 333461 * 2 ^ 59
def prefixEnd_333461 : Nat := 4983230072969 + 3 ^ 40 * 333461 * 2
def baseEnd_333461 : Nat := 114150515019350044002631

theorem tailTrace_333461 : CollatzResearch.WordTrace tailWord_333461 prefixEnd_333461 114150515019350044002631 := by
  unfold tailWord_333461
  simp only [CollatzResearch.WordTrace]
  refine ⟨12162321844935222449840237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8108214563290148299893491 12162321844935222449840237)
  ·
    refine ⟨4560870691850708418690089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12162321844935222449840237 4560870691850708418690089)
    ·
      refine ⟨3420653018888031314017567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4560870691850708418690089 3420653018888031314017567)
      ·
        refine ⟨5130979528332046971026351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3420653018888031314017567 5130979528332046971026351)
        ·
          refine ⟨7696469292498070456539527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5130979528332046971026351 7696469292498070456539527)
          ·
            refine ⟨11544703938747105684809291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7696469292498070456539527 11544703938747105684809291)
            ·
              refine ⟨17317055908120658527213937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11544703938747105684809291 17317055908120658527213937)
              ·
                refine ⟨12987791931090493895410453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17317055908120658527213937 12987791931090493895410453)
                ·
                  refine ⟨608802746769866901347365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12987791931090493895410453 608802746769866901347365)
                  ·
                    refine ⟨114150515019350044002631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 608802746769866901347365 114150515019350044002631)
                    ·
                      rfl

theorem cell22_333461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_333461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333461 prefixEnd_333461 := by exact prefixLift 333461
  have htrace : WordTrace (prefixWord ++ tailWord_333461) baseStart_333461 baseEnd_333461 := by
    simpa [prefixWord, tailWord_333461, baseEnd_333461] using wordTrace_append hprefix tailTrace_333461
  have hstable : (prefixWord ++ tailWord_333461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333461).length < 2 ^ (prefixWord ++ tailWord_333461).sum := by decide
  have hdescent : baseEnd_333461 < baseStart_333461 := by decide
  rcases family_descends (prefixWord ++ tailWord_333461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333463 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 4, 3]
def baseStart_333463 : Nat := 118140960795 + 333463 * 2 ^ 59
def prefixEnd_333463 : Nat := 4983230072969 + 3 ^ 40 * 333463 * 2
def baseEnd_333463 : Nat := 114151199660222705452625

theorem tailTrace_333463 : CollatzResearch.WordTrace tailWord_333463 prefixEnd_333463 114151199660222705452625 := by
  unfold tailWord_333463
  simp only [CollatzResearch.WordTrace]
  refine ⟨12162394790927976791413043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8108263193951984527608695 12162394790927976791413043)
  ·
    refine ⟨18243592186391965187119565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12162394790927976791413043 18243592186391965187119565)
    ·
      refine ⟨6841347069896986945169837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18243592186391965187119565 6841347069896986945169837)
      ·
        refine ⟨2565505151211370104438689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6841347069896986945169837 2565505151211370104438689)
        ·
          refine ⟨1924128863408527578329017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2565505151211370104438689 1924128863408527578329017)
          ·
            refine ⟨1443096647556395683746763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1924128863408527578329017 1443096647556395683746763)
            ·
              refine ⟨2164644971334593525620145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443096647556395683746763 2164644971334593525620145)
              ·
                refine ⟨1623483728500945144215109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2164644971334593525620145 1623483728500945144215109)
                ·
                  refine ⟨304403199093927214540333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1623483728500945144215109 304403199093927214540333)
                  ·
                    refine ⟨114151199660222705452625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304403199093927214540333 114151199660222705452625)
                    ·
                      rfl

theorem cell22_333463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_333463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333463 prefixEnd_333463 := by exact prefixLift 333463
  have htrace : WordTrace (prefixWord ++ tailWord_333463) baseStart_333463 baseEnd_333463 := by
    simpa [prefixWord, tailWord_333463, baseEnd_333463] using wordTrace_append hprefix tailTrace_333463
  have hstable : (prefixWord ++ tailWord_333463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333463).length < 2 ^ (prefixWord ++ tailWord_333463).sum := by decide
  have hdescent : baseEnd_333463 < baseStart_333463 := by decide
  rcases family_descends (prefixWord ++ tailWord_333463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333476 : List Nat := [2, 3, 1, 2, 2, 2, 10]
def baseStart_333476 : Nat := 118140960795 + 333476 * 2 ^ 59
def prefixEnd_333476 : Nat := 4983230072969 + 3 ^ 40 * 333476 * 2
def baseEnd_333476 : Nat := 4227987030588703884355

theorem tailTrace_333476 : CollatzResearch.WordTrace tailWord_333476 prefixEnd_333476 4227987030588703884355 := by
  unfold tailWord_333476
  simp only [CollatzResearch.WordTrace]
  refine ⟨6081434469940440005818141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8108579293253920007757521 6081434469940440005818141)
  ·
    refine ⟨2280537926227665002181803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6081434469940440005818141 2280537926227665002181803)
    ·
      refine ⟨3420806889341497503272705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2280537926227665002181803 3420806889341497503272705)
      ·
        refine ⟨2565605167006123127454529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3420806889341497503272705 2565605167006123127454529)
        ·
          refine ⟨1924203875254592345590897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2565605167006123127454529 1924203875254592345590897)
          ·
            refine ⟨1443152906440944259193173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1924203875254592345590897 1443152906440944259193173)
            ·
              refine ⟨4227987030588703884355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1443152906440944259193173 4227987030588703884355)
              ·
                rfl

theorem cell22_333476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 10].length) (baseStart_333476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333476 prefixEnd_333476 := by exact prefixLift 333476
  have htrace : WordTrace (prefixWord ++ tailWord_333476) baseStart_333476 baseEnd_333476 := by
    simpa [prefixWord, tailWord_333476, baseEnd_333476] using wordTrace_append hprefix tailTrace_333476
  have hstable : (prefixWord ++ tailWord_333476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333476).length < 2 ^ (prefixWord ++ tailWord_333476).sum := by decide
  have hdescent : baseEnd_333476 < baseStart_333476 := by decide
  rcases family_descends (prefixWord ++ tailWord_333476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333553 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 2, 5]
def baseStart_333553 : Nat := 118140960795 + 333553 * 2 ^ 59
def prefixEnd_333553 : Nat := 4983230072969 + 3 ^ 40 * 333553 * 2
def baseEnd_333553 : Nat := 114182008499492470702349

theorem tailTrace_333553 : CollatzResearch.WordTrace tailWord_333553 prefixEnd_333553 114182008499492470702349 := by
  unfold tailWord_333553
  simp only [CollatzResearch.WordTrace]
  refine ⟨12165677360601922162189313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8110451573734614774792875 12165677360601922162189313)
  ·
    refine ⟨9124258020451441621641985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12165677360601922162189313 9124258020451441621641985)
    ·
      refine ⟨6843193515338581216231489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9124258020451441621641985 6843193515338581216231489)
      ·
        refine ⟨5132395136503935912173617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6843193515338581216231489 5132395136503935912173617)
        ·
          refine ⟨3849296352377951934130213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5132395136503935912173617 3849296352377951934130213)
          ·
            refine ⟨721743066070865987649415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3849296352377951934130213 721743066070865987649415)
            ·
              refine ⟨1082614599106298981474123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721743066070865987649415 1082614599106298981474123)
              ·
                refine ⟨1623921898659448472211185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082614599106298981474123 1623921898659448472211185)
                ·
                  refine ⟨1217941423994586354158389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1623921898659448472211185 1217941423994586354158389)
                  ·
                    refine ⟨114182008499492470702349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1217941423994586354158389 114182008499492470702349)
                    ·
                      rfl

theorem cell22_333553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_333553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333553 prefixEnd_333553 := by exact prefixLift 333553
  have htrace : WordTrace (prefixWord ++ tailWord_333553) baseStart_333553 baseEnd_333553 := by
    simpa [prefixWord, tailWord_333553, baseEnd_333553] using wordTrace_append hprefix tailTrace_333553
  have hstable : (prefixWord ++ tailWord_333553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333553).length < 2 ^ (prefixWord ++ tailWord_333553).sum := by decide
  have hdescent : baseEnd_333553 < baseStart_333553 := by decide
  rcases family_descends (prefixWord ++ tailWord_333553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333600 : List Nat := [2, 1, 1, 5, 1, 1, 1, 6, 4]
def baseStart_333600 : Nat := 118140960795 + 333600 * 2 ^ 59
def prefixEnd_333600 : Nat := 4983230072969 + 3 ^ 40 * 333600 * 2
def baseEnd_333600 : Nat := 38066032520000004925735

theorem tailTrace_333600 : CollatzResearch.WordTrace tailWord_333600 prefixEnd_333600 38066032520000004925735 := by
  unfold tailWord_333600
  simp only [CollatzResearch.WordTrace]
  refine ⟨6083695795715824594575127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8111594394287766126100169 6083695795715824594575127)
  ·
    refine ⟨9125543693573736891862691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6083695795715824594575127 9125543693573736891862691)
    ·
      refine ⟨13688315540360605337794037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9125543693573736891862691 13688315540360605337794037)
      ·
        refine ⟨1283279581908806750418191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13688315540360605337794037 1283279581908806750418191)
        ·
          refine ⟨1924919372863210125627287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283279581908806750418191 1924919372863210125627287)
          ·
            refine ⟨2887379059294815188440931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1924919372863210125627287 2887379059294815188440931)
            ·
              refine ⟨4331068588942222782661397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2887379059294815188440931 4331068588942222782661397)
              ·
                refine ⟨203018840106666692937253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4331068588942222782661397 203018840106666692937253)
                ·
                  refine ⟨38066032520000004925735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203018840106666692937253 38066032520000004925735)
                  ·
                    rfl

theorem cell22_333600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 4].length) (baseStart_333600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333600 prefixEnd_333600 := by exact prefixLift 333600
  have htrace : WordTrace (prefixWord ++ tailWord_333600) baseStart_333600 baseEnd_333600 := by
    simpa [prefixWord, tailWord_333600, baseEnd_333600] using wordTrace_append hprefix tailTrace_333600
  have hstable : (prefixWord ++ tailWord_333600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333600).length < 2 ^ (prefixWord ++ tailWord_333600).sum := by decide
  have hdescent : baseEnd_333600 < baseStart_333600 := by decide
  rcases family_descends (prefixWord ++ tailWord_333600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333630 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_333630 : Nat := 118140960795 + 333630 * 2 ^ 59
def prefixEnd_333630 : Nat := 4983230072969 + 3 ^ 40 * 333630 * 2
def baseEnd_333630 : Nat := 114208367173089936527113

theorem tailTrace_333630 : CollatzResearch.WordTrace tailWord_333630 prefixEnd_333630 114208367173089936527113 := by
  unfold tailWord_333630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1521060722665370539092793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8112323854215309541828229 1521060722665370539092793)
  ·
    refine ⟨1140795541999027904319595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1521060722665370539092793 1140795541999027904319595)
    ·
      refine ⟨1711193312998541856479393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1140795541999027904319595 1711193312998541856479393)
      ·
        refine ⟨1283394984748906392359545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1711193312998541856479393 1283394984748906392359545)
        ·
          refine ⟨962546238561679794269659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1283394984748906392359545 962546238561679794269659)
          ·
            refine ⟨1443819357842519691404489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962546238561679794269659 1443819357842519691404489)
            ·
              refine ⟨1082864518381889768553367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1443819357842519691404489 1082864518381889768553367)
              ·
                refine ⟨1624296777572834652830051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082864518381889768553367 1624296777572834652830051)
                ·
                  refine ⟨2436445166359251979245077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624296777572834652830051 2436445166359251979245077)
                  ·
                    refine ⟨114208367173089936527113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2436445166359251979245077 114208367173089936527113)
                    ·
                      rfl

theorem cell22_333630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_333630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333630 prefixEnd_333630 := by exact prefixLift 333630
  have htrace : WordTrace (prefixWord ++ tailWord_333630) baseStart_333630 baseEnd_333630 := by
    simpa [prefixWord, tailWord_333630, baseEnd_333630] using wordTrace_append hprefix tailTrace_333630
  have hstable : (prefixWord ++ tailWord_333630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333630).length < 2 ^ (prefixWord ++ tailWord_333630).sum := by decide
  have hdescent : baseEnd_333630 < baseStart_333630 := by decide
  rcases family_descends (prefixWord ++ tailWord_333630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333645 : List Nat := [1, 6, 1, 2, 1, 1, 10]
def baseStart_333645 : Nat := 118140960795 + 333645 * 2 ^ 59
def prefixEnd_333645 : Nat := 4983230072969 + 3 ^ 40 * 333645 * 2
def baseEnd_333645 : Nat := 4230129702949440644521

theorem tailTrace_333645 : CollatzResearch.WordTrace tailWord_333645 prefixEnd_333645 4230129702949440644521 := by
  unfold tailWord_333645
  simp only [CollatzResearch.WordTrace]
  refine ⟨12169032876268621874538389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8112688584179081249692259 12169032876268621874538389)
  ·
    refine ⟨570423416075091650368987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12169032876268621874538389 570423416075091650368987)
    ·
      refine ⟨855635124112637475553481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570423416075091650368987 855635124112637475553481)
      ·
        refine ⟨641726343084478106665111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 855635124112637475553481 641726343084478106665111)
        ·
          refine ⟨962589514626717159997667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641726343084478106665111 962589514626717159997667)
          ·
            refine ⟨1443884271940075739996501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962589514626717159997667 1443884271940075739996501)
            ·
              refine ⟨4230129702949440644521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1443884271940075739996501 4230129702949440644521)
              ·
                rfl

theorem cell22_333645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 10].length) (baseStart_333645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333645 prefixEnd_333645 := by exact prefixLift 333645
  have htrace : WordTrace (prefixWord ++ tailWord_333645) baseStart_333645 baseEnd_333645 := by
    simpa [prefixWord, tailWord_333645, baseEnd_333645] using wordTrace_append hprefix tailTrace_333645
  have hstable : (prefixWord ++ tailWord_333645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333645).length < 2 ^ (prefixWord ++ tailWord_333645).sum := by decide
  have hdescent : baseEnd_333645 < baseStart_333645 := by decide
  rcases family_descends (prefixWord ++ tailWord_333645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333658 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_333658 : Nat := 118140960795 + 333658 * 2 ^ 59
def prefixEnd_333658 : Nat := 4983230072969 + 3 ^ 40 * 333658 * 2
def baseEnd_333658 : Nat := 114217952145307196827027

theorem tailTrace_333658 : CollatzResearch.WordTrace tailWord_333658 prefixEnd_333658 114217952145307196827027 := by
  unfold tailWord_333658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3042376756305381273690407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8113004683481016729841085 3042376756305381273690407)
  ·
    refine ⟨4563565134458071910535611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3042376756305381273690407 4563565134458071910535611)
    ·
      refine ⟨6845347701687107865803417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4563565134458071910535611 6845347701687107865803417)
      ·
        refine ⟨5134010776265330899352563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6845347701687107865803417 5134010776265330899352563)
        ·
          refine ⟨7701016164397996349028845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5134010776265330899352563 7701016164397996349028845)
          ·
            refine ⟨2887881061649248630885817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7701016164397996349028845 2887881061649248630885817)
            ·
              refine ⟨2165910796236936473164363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2887881061649248630885817 2165910796236936473164363)
              ·
                refine ⟨3248866194355404709746545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2165910796236936473164363 3248866194355404709746545)
                ·
                  refine ⟨2436649645766553532309909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3248866194355404709746545 2436649645766553532309909)
                  ·
                    refine ⟨114217952145307196827027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2436649645766553532309909 114217952145307196827027)
                    ·
                      rfl

theorem cell22_333658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_333658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333658 prefixEnd_333658 := by exact prefixLift 333658
  have htrace : WordTrace (prefixWord ++ tailWord_333658) baseStart_333658 baseEnd_333658 := by
    simpa [prefixWord, tailWord_333658, baseEnd_333658] using wordTrace_append hprefix tailTrace_333658
  have hstable : (prefixWord ++ tailWord_333658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333658).length < 2 ^ (prefixWord ++ tailWord_333658).sum := by decide
  have hdescent : baseEnd_333658 < baseStart_333658 := by decide
  rcases family_descends (prefixWord ++ tailWord_333658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333666 : List Nat := [3, 3, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_333666 : Nat := 118140960795 + 333666 * 2 ^ 59
def prefixEnd_333666 : Nat := 4983230072969 + 3 ^ 40 * 333666 * 2
def baseEnd_333666 : Nat := 114220690708797842627003

theorem tailTrace_333666 : CollatzResearch.WordTrace tailWord_333666 prefixEnd_333666 114220690708797842627003 := by
  unfold tailWord_333666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3042449702298135615263213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8113199206128361640701901 3042449702298135615263213)
  ·
    refine ⟨1140918638361800855723705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3042449702298135615263213 1140918638361800855723705)
    ·
      refine ⟨855688978771350641792779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1140918638361800855723705 855688978771350641792779)
      ·
        refine ⟨1283533468157025962689169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855688978771350641792779 1283533468157025962689169)
        ·
          refine ⟨962650101117769472016877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1283533468157025962689169 962650101117769472016877)
          ·
            refine ⟨360993787919163552006329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 962650101117769472016877 360993787919163552006329)
            ·
              refine ⟨270745340939372664004747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360993787919163552006329 270745340939372664004747)
              ·
                refine ⟨406118011409058996007121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270745340939372664004747 406118011409058996007121)
                ·
                  refine ⟨304588508556794247005341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406118011409058996007121 304588508556794247005341)
                  ·
                    refine ⟨114220690708797842627003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304588508556794247005341 114220690708797842627003)
                    ·
                      rfl

theorem cell22_333666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_333666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333666 prefixEnd_333666 := by exact prefixLift 333666
  have htrace : WordTrace (prefixWord ++ tailWord_333666) baseStart_333666 baseEnd_333666 := by
    simpa [prefixWord, tailWord_333666, baseEnd_333666] using wordTrace_append hprefix tailTrace_333666
  have hstable : (prefixWord ++ tailWord_333666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333666).length < 2 ^ (prefixWord ++ tailWord_333666).sum := by decide
  have hdescent : baseEnd_333666 < baseStart_333666 := by decide
  rcases family_descends (prefixWord ++ tailWord_333666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333735 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 8]
def baseStart_333735 : Nat := 118140960795 + 333735 * 2 ^ 59
def prefixEnd_333735 : Nat := 4983230072969 + 3 ^ 40 * 333735 * 2
def baseEnd_333735 : Nat := 38081436939634887550597

theorem tailTrace_333735 : CollatzResearch.WordTrace tailWord_333735 prefixEnd_333735 38081436939634887550597 := by
  unfold tailWord_333735
  simp only [CollatzResearch.WordTrace]
  refine ⟨12172315445942567245314659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8114876963961711496876439 12172315445942567245314659)
  ·
    refine ⟨18258473168913850867971989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12172315445942567245314659 18258473168913850867971989)
    ·
      refine ⟨855865929792836759436187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18258473168913850867971989 855865929792836759436187)
      ·
        refine ⟨1283798894689255139154281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855865929792836759436187 1283798894689255139154281)
        ·
          refine ⟨962849171016941354365711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1283798894689255139154281 962849171016941354365711)
          ·
            refine ⟨1444273756525412031548567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962849171016941354365711 1444273756525412031548567)
            ·
              refine ⟨2166410634788118047322851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1444273756525412031548567 2166410634788118047322851)
              ·
                refine ⟨3249615952182177070984277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166410634788118047322851 3249615952182177070984277)
                ·
                  refine ⟨38081436939634887550597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3249615952182177070984277 38081436939634887550597)
                  ·
                    rfl

theorem cell22_333735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 8].length) (baseStart_333735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333735 prefixEnd_333735 := by exact prefixLift 333735
  have htrace : WordTrace (prefixWord ++ tailWord_333735) baseStart_333735 baseEnd_333735 := by
    simpa [prefixWord, tailWord_333735, baseEnd_333735] using wordTrace_append hprefix tailTrace_333735
  have hstable : (prefixWord ++ tailWord_333735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333735).length < 2 ^ (prefixWord ++ tailWord_333735).sum := by decide
  have hdescent : baseEnd_333735 < baseStart_333735 := by decide
  rcases family_descends (prefixWord ++ tailWord_333735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333752 : List Nat := [2, 1, 2, 1, 2, 3, 4, 3, 4]
def baseStart_333752 : Nat := 118140960795 + 333752 * 2 ^ 59
def prefixEnd_333752 : Nat := 4983230072969 + 3 ^ 40 * 333752 * 2
def baseEnd_333752 : Nat := 38083376755440761658913

theorem tailTrace_333752 : CollatzResearch.WordTrace tailWord_333752 prefixEnd_333752 38083376755440761658913 := by
  unfold tailWord_333752
  simp only [CollatzResearch.WordTrace]
  refine ⟨6086467743440489574341755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8115290324587319432455673 6086467743440489574341755)
  ·
    refine ⟨9129701615160734361512633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6086467743440489574341755 9129701615160734361512633)
    ·
      refine ⟨6847276211370550771134475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9129701615160734361512633 6847276211370550771134475)
      ·
        refine ⟨10270914317055826156701713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6847276211370550771134475 10270914317055826156701713)
        ·
          refine ⟨7703185737791869617526285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10270914317055826156701713 7703185737791869617526285)
          ·
            refine ⟨2888694651671951106572357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7703185737791869617526285 2888694651671951106572357)
            ·
              refine ⟨541630247188490832482317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2888694651671951106572357 541630247188490832482317)
              ·
                refine ⟨203111342695684062180869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 541630247188490832482317 203111342695684062180869)
                ·
                  refine ⟨38083376755440761658913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203111342695684062180869 38083376755440761658913)
                  ·
                    rfl

theorem cell22_333752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 4].length) (baseStart_333752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333752 prefixEnd_333752 := by exact prefixLift 333752
  have htrace : WordTrace (prefixWord ++ tailWord_333752) baseStart_333752 baseEnd_333752 := by
    simpa [prefixWord, tailWord_333752, baseEnd_333752] using wordTrace_append hprefix tailTrace_333752
  have hstable : (prefixWord ++ tailWord_333752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333752).length < 2 ^ (prefixWord ++ tailWord_333752).sum := by decide
  have hdescent : baseEnd_333752 < baseStart_333752 := by decide
  rcases family_descends (prefixWord ++ tailWord_333752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333780 : List Nat := [2, 4, 1, 2, 1, 1, 2, 9]
def baseStart_333780 : Nat := 118140960795 + 333780 * 2 ^ 59
def prefixEnd_333780 : Nat := 4983230072969 + 3 ^ 40 * 333780 * 2
def baseEnd_333780 : Nat := 12695523915393282808517

theorem tailTrace_333780 : CollatzResearch.WordTrace tailWord_333780 prefixEnd_333780 12695523915393282808517 := by
  unfold tailWord_333780
  simp only [CollatzResearch.WordTrace]
  refine ⟨6086978365389769965351397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8115971153853026620468529 6086978365389769965351397)
  ·
    refine ⟨1141308443510581868503387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6086978365389769965351397 1141308443510581868503387)
    ·
      refine ⟨1711962665265872802755081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141308443510581868503387 1711962665265872802755081)
      ·
        refine ⟨1283971998949404602066311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1711962665265872802755081 1283971998949404602066311)
        ·
          refine ⟨1925957998424106903099467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283971998949404602066311 1925957998424106903099467)
          ·
            refine ⟨2888936997636160354649201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925957998424106903099467 2888936997636160354649201)
            ·
              refine ⟨2166702748227120265986901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2888936997636160354649201 2166702748227120265986901)
              ·
                refine ⟨12695523915393282808517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2166702748227120265986901 12695523915393282808517)
                ·
                  rfl

theorem cell22_333780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 9].length) (baseStart_333780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333780 prefixEnd_333780 := by exact prefixLift 333780
  have htrace : WordTrace (prefixWord ++ tailWord_333780) baseStart_333780 baseEnd_333780 := by
    simpa [prefixWord, tailWord_333780, baseEnd_333780] using wordTrace_append hprefix tailTrace_333780
  have hstable : (prefixWord ++ tailWord_333780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333780).length < 2 ^ (prefixWord ++ tailWord_333780).sum := by decide
  have hdescent : baseEnd_333780 < baseStart_333780 := by decide
  rcases family_descends (prefixWord ++ tailWord_333780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333784 : List Nat := [2, 1, 2, 2, 2, 2, 5, 1, 2, 3]
def baseStart_333784 : Nat := 118140960795 + 333784 * 2 ^ 59
def prefixEnd_333784 : Nat := 4983230072969 + 3 ^ 40 * 333784 * 2
def baseEnd_333784 : Nat := 114261084520284868176641

theorem tailTrace_333784 : CollatzResearch.WordTrace tailWord_333784 prefixEnd_333784 114261084520284868176641 := by
  unfold tailWord_333784
  simp only [CollatzResearch.WordTrace]
  refine ⟨6087051311382524306924203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8116068415176699075898937 6087051311382524306924203)
  ·
    refine ⟨9130576967073786460386305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6087051311382524306924203 9130576967073786460386305)
    ·
      refine ⟨6847932725305339845289729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9130576967073786460386305 6847932725305339845289729)
      ·
        refine ⟨5135949543979004883967297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6847932725305339845289729 5135949543979004883967297)
        ·
          refine ⟨3851962157984253662975473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5135949543979004883967297 3851962157984253662975473)
          ·
            refine ⟨2888971618488190247231605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3851962157984253662975473 2888971618488190247231605)
            ·
              refine ⟨270841089233267835677963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2888971618488190247231605 270841089233267835677963)
              ·
                refine ⟨406261633849901753516945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270841089233267835677963 406261633849901753516945)
                ·
                  refine ⟨304696225387426315137709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406261633849901753516945 304696225387426315137709)
                  ·
                    refine ⟨114261084520284868176641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304696225387426315137709 114261084520284868176641)
                    ·
                      rfl

theorem cell22_333784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_333784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333784 prefixEnd_333784 := by exact prefixLift 333784
  have htrace : WordTrace (prefixWord ++ tailWord_333784) baseStart_333784 baseEnd_333784 := by
    simpa [prefixWord, tailWord_333784, baseEnd_333784] using wordTrace_append hprefix tailTrace_333784
  have hstable : (prefixWord ++ tailWord_333784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333784).length < 2 ^ (prefixWord ++ tailWord_333784).sum := by decide
  have hdescent : baseEnd_333784 < baseStart_333784 := by decide
  rcases family_descends (prefixWord ++ tailWord_333784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333788 : List Nat := [2, 2, 6, 1, 1, 1, 2, 2, 1, 4]
def baseStart_333788 : Nat := 118140960795 + 333788 * 2 ^ 59
def prefixEnd_333788 : Nat := 4983230072969 + 3 ^ 40 * 333788 * 2
def baseEnd_333788 : Nat := 114262453802030191076629

theorem tailTrace_333788 : CollatzResearch.WordTrace tailWord_333788 prefixEnd_333788 114262453802030191076629 := by
  unfold tailWord_333788
  simp only [CollatzResearch.WordTrace]
  refine ⟨6087124257375278648497009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8116165676500371531329345 6087124257375278648497009)
  ·
    refine ⟨4565343193031458986372757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6087124257375278648497009 4565343193031458986372757)
    ·
      refine ⟨214000462173349639986223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4565343193031458986372757 214000462173349639986223)
      ·
        refine ⟨321000693260024459979335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214000462173349639986223 321000693260024459979335)
        ·
          refine ⟨481501039890036689969003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321000693260024459979335 481501039890036689969003)
          ·
            refine ⟨722251559835055034953505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481501039890036689969003 722251559835055034953505)
            ·
              refine ⟨541688669876291276215129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 722251559835055034953505 541688669876291276215129)
              ·
                refine ⟨406266502407218457161347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541688669876291276215129 406266502407218457161347)
                ·
                  refine ⟨609399753610827685742021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406266502407218457161347 609399753610827685742021)
                  ·
                    refine ⟨114262453802030191076629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 609399753610827685742021 114262453802030191076629)
                    ·
                      rfl

theorem cell22_333788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_333788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333788 prefixEnd_333788 := by exact prefixLift 333788
  have htrace : WordTrace (prefixWord ++ tailWord_333788) baseStart_333788 baseEnd_333788 := by
    simpa [prefixWord, tailWord_333788, baseEnd_333788] using wordTrace_append hprefix tailTrace_333788
  have hstable : (prefixWord ++ tailWord_333788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333788).length < 2 ^ (prefixWord ++ tailWord_333788).sum := by decide
  have hdescent : baseEnd_333788 < baseStart_333788 := by decide
  rcases family_descends (prefixWord ++ tailWord_333788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333814 : List Nat := [5, 1, 1, 1, 5, 1, 8]
def baseStart_333814 : Nat := 118140960795 + 333814 * 2 ^ 59
def prefixEnd_333814 : Nat := 4983230072969 + 3 ^ 40 * 333814 * 2
def baseEnd_333814 : Nat := 4232272375310177404687

theorem tailTrace_333814 : CollatzResearch.WordTrace tailWord_333814 prefixEnd_333814 4232272375310177404687 := by
  unfold tailWord_333814
  simp only [CollatzResearch.WordTrace]
  refine ⟨760949800791022733590031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8116797875104242491626997 760949800791022733590031)
  ·
    refine ⟨1141424701186534100385047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 760949800791022733590031 1141424701186534100385047)
    ·
      refine ⟨1712137051779801150577571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141424701186534100385047 1712137051779801150577571)
      ·
        refine ⟨2568205577669701725866357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712137051779801150577571 2568205577669701725866357)
        ·
          refine ⟨240769272906534536799971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2568205577669701725866357 240769272906534536799971)
          ·
            refine ⟨361153909359801805199957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240769272906534536799971 361153909359801805199957)
            ·
              refine ⟨4232272375310177404687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 361153909359801805199957 4232272375310177404687)
              ·
                rfl

theorem cell22_333814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 8].length) (baseStart_333814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333814 prefixEnd_333814 := by exact prefixLift 333814
  have htrace : WordTrace (prefixWord ++ tailWord_333814) baseStart_333814 baseEnd_333814 := by
    simpa [prefixWord, tailWord_333814, baseEnd_333814] using wordTrace_append hprefix tailTrace_333814
  have hstable : (prefixWord ++ tailWord_333814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333814).length < 2 ^ (prefixWord ++ tailWord_333814).sum := by decide
  have hdescent : baseEnd_333814 < baseStart_333814 := by decide
  rcases family_descends (prefixWord ++ tailWord_333814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333825 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 7]
def baseStart_333825 : Nat := 118140960795 + 333825 * 2 ^ 59
def prefixEnd_333825 : Nat := 4983230072969 + 3 ^ 40 * 333825 * 2
def baseEnd_333825 : Nat := 38091706552724809300505

theorem tailTrace_333825 : CollatzResearch.WordTrace tailWord_333825 prefixEnd_333825 38091706552724809300505 := by
  unfold tailWord_333825
  simp only [CollatzResearch.WordTrace]
  refine ⟨12175598015616512616090929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8117065343744341744060619 12175598015616512616090929)
  ·
    refine ⟨9131698511712384462068197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12175598015616512616090929 9131698511712384462068197)
    ·
      refine ⟨1712193470946072086637787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9131698511712384462068197 1712193470946072086637787)
      ·
        refine ⟨2568290206419108129956681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712193470946072086637787 2568290206419108129956681)
        ·
          refine ⟨1926217654814331097467511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2568290206419108129956681 1926217654814331097467511)
          ·
            refine ⟨2889326482221496646201267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926217654814331097467511 2889326482221496646201267)
            ·
              refine ⟨4333989723332244969301901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2889326482221496646201267 4333989723332244969301901)
              ·
                refine ⟨1625246146249591863488213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4333989723332244969301901 1625246146249591863488213)
                ·
                  refine ⟨38091706552724809300505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1625246146249591863488213 38091706552724809300505)
                  ·
                    rfl

theorem cell22_333825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_333825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333825 prefixEnd_333825 := by exact prefixLift 333825
  have htrace : WordTrace (prefixWord ++ tailWord_333825) baseStart_333825 baseEnd_333825 := by
    simpa [prefixWord, tailWord_333825, baseEnd_333825] using wordTrace_append hprefix tailTrace_333825
  have hstable : (prefixWord ++ tailWord_333825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333825).length < 2 ^ (prefixWord ++ tailWord_333825).sum := by decide
  have hdescent : baseEnd_333825 < baseStart_333825 := by decide
  rcases family_descends (prefixWord ++ tailWord_333825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333829 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 3, 3]
def baseStart_333829 : Nat := 118140960795 + 333829 * 2 ^ 59
def prefixEnd_333829 : Nat := 4983230072969 + 3 ^ 40 * 333829 * 2
def baseEnd_333829 : Nat := 114276488939919750801503

theorem tailTrace_333829 : CollatzResearch.WordTrace tailWord_333829 prefixEnd_333829 114276488939919750801503 := by
  unfold tailWord_333829
  simp only [CollatzResearch.WordTrace]
  refine ⟨12175743907602021299236541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8117162605068014199491027 12175743907602021299236541)
  ·
    refine ⟨4565903965350757987213703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12175743907602021299236541 4565903965350757987213703)
    ·
      refine ⟨6848855948026136980820555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4565903965350757987213703 6848855948026136980820555)
      ·
        refine ⟨10273283922039205471230833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6848855948026136980820555 10273283922039205471230833)
        ·
          refine ⟨7704962941529404103423125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10273283922039205471230833 7704962941529404103423125)
          ·
            refine ⟨361170137884190817347959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7704962941529404103423125 361170137884190817347959)
            ·
              refine ⟨541755206826286226021939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361170137884190817347959 541755206826286226021939)
              ·
                refine ⟨812632810239429339032909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541755206826286226021939 812632810239429339032909)
                ·
                  refine ⟨304737303839786002137341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 812632810239429339032909 304737303839786002137341)
                  ·
                    refine ⟨114276488939919750801503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304737303839786002137341 114276488939919750801503)
                    ·
                      rfl

theorem cell22_333829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_333829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333829 prefixEnd_333829 := by exact prefixLift 333829
  have htrace : WordTrace (prefixWord ++ tailWord_333829) baseStart_333829 baseEnd_333829 := by
    simpa [prefixWord, tailWord_333829, baseEnd_333829] using wordTrace_append hprefix tailTrace_333829
  have hstable : (prefixWord ++ tailWord_333829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333829).length < 2 ^ (prefixWord ++ tailWord_333829).sum := by decide
  have hdescent : baseEnd_333829 < baseStart_333829 := by decide
  rcases family_descends (prefixWord ++ tailWord_333829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333876 : List Nat := [2, 5, 1, 2, 2, 1, 2, 2, 5]
def baseStart_333876 : Nat := 118140960795 + 333876 * 2 ^ 59
def prefixEnd_333876 : Nat := 4983230072969 + 3 ^ 40 * 333876 * 2
def baseEnd_333876 : Nat := 38097526000142431625453

theorem tailTrace_333876 : CollatzResearch.WordTrace tailWord_333876 prefixEnd_333876 38097526000142431625453 := by
  unfold tailWord_333876
  simp only [CollatzResearch.WordTrace]
  refine ⟨6088729069215874163098741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8118305425621165550798321 6088729069215874163098741)
  ·
    refine ⟨570818350238988202790507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6088729069215874163098741 570818350238988202790507)
    ·
      refine ⟨856227525358482304185761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570818350238988202790507 856227525358482304185761)
      ·
        refine ⟨642170644018861728139321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 856227525358482304185761 642170644018861728139321)
        ·
          refine ⟨481627983014146296104491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 642170644018861728139321 481627983014146296104491)
          ·
            refine ⟨722441974521219444156737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481627983014146296104491 722441974521219444156737)
            ·
              refine ⟨541831480890914583117553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 722441974521219444156737 541831480890914583117553)
              ·
                refine ⟨406373610668185937338165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541831480890914583117553 406373610668185937338165)
                ·
                  refine ⟨38097526000142431625453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 406373610668185937338165 38097526000142431625453)
                  ·
                    rfl

theorem cell22_333876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_333876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333876 prefixEnd_333876 := by exact prefixLift 333876
  have htrace : WordTrace (prefixWord ++ tailWord_333876) baseStart_333876 baseEnd_333876 := by
    simpa [prefixWord, tailWord_333876, baseEnd_333876] using wordTrace_append hprefix tailTrace_333876
  have hstable : (prefixWord ++ tailWord_333876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333876).length < 2 ^ (prefixWord ++ tailWord_333876).sum := by decide
  have hdescent : baseEnd_333876 < baseStart_333876 := by decide
  rcases family_descends (prefixWord ++ tailWord_333876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333880 : List Nat := [2, 1, 2, 1, 7, 1, 2, 2, 1, 3]
def baseStart_333880 : Nat := 118140960795 + 333880 * 2 ^ 59
def prefixEnd_333880 : Nat := 4983230072969 + 3 ^ 40 * 333880 * 2
def baseEnd_333880 : Nat := 114293947282172617776347

theorem tailTrace_333880 : CollatzResearch.WordTrace tailWord_333880 prefixEnd_333880 114293947282172617776347 := by
  unfold tailWord_333880
  simp only [CollatzResearch.WordTrace]
  refine ⟨6088802015208628504671547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8118402686944838006228729 6088802015208628504671547)
  ·
    refine ⟨9133203022812942757007321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6088802015208628504671547 9133203022812942757007321)
    ·
      refine ⟨6849902267109707067755491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9133203022812942757007321 6849902267109707067755491)
      ·
        refine ⟨10274853400664560601633237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6849902267109707067755491 10274853400664560601633237)
        ·
          refine ⟨240816876578075639100779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10274853400664560601633237 240816876578075639100779)
          ·
            refine ⟨361225314867113458651169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240816876578075639100779 361225314867113458651169)
            ·
              refine ⟨270918986150335093988377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361225314867113458651169 270918986150335093988377)
              ·
                refine ⟨203189239612751320491283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270918986150335093988377 203189239612751320491283)
                ·
                  refine ⟨304783859419126980736925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203189239612751320491283 304783859419126980736925)
                  ·
                    refine ⟨114293947282172617776347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304783859419126980736925 114293947282172617776347)
                    ·
                      rfl

theorem cell22_333880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_333880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333880 prefixEnd_333880 := by exact prefixLift 333880
  have htrace : WordTrace (prefixWord ++ tailWord_333880) baseStart_333880 baseEnd_333880 := by
    simpa [prefixWord, tailWord_333880, baseEnd_333880] using wordTrace_append hprefix tailTrace_333880
  have hstable : (prefixWord ++ tailWord_333880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333880).length < 2 ^ (prefixWord ++ tailWord_333880).sum := by decide
  have hdescent : baseEnd_333880 < baseStart_333880 := by decide
  rcases family_descends (prefixWord ++ tailWord_333880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333902 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_333902 : Nat := 118140960795 + 333902 * 2 ^ 59
def prefixEnd_333902 : Nat := 4983230072969 + 3 ^ 40 * 333902 * 2
def baseEnd_333902 : Nat := 114301478331771893726279

theorem tailTrace_333902 : CollatzResearch.WordTrace tailWord_333902 prefixEnd_333902 114301478331771893726279 := by
  unfold tailWord_333902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1522300804542194345830495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8118937624225036511095973 1522300804542194345830495)
  ·
    refine ⟨2283451206813291518745743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1522300804542194345830495 2283451206813291518745743)
    ·
      refine ⟨3425176810219937278118615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2283451206813291518745743 3425176810219937278118615)
      ·
        refine ⟨5137765215329905917177923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3425176810219937278118615 5137765215329905917177923)
        ·
          refine ⟨7706647822994858875766885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5137765215329905917177923 7706647822994858875766885)
          ·
            refine ⟨1444996466811536039206291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7706647822994858875766885 1444996466811536039206291)
            ·
              refine ⟨2167494700217304058809437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1444996466811536039206291 2167494700217304058809437)
              ·
                refine ⟨812810512581489022053539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2167494700217304058809437 812810512581489022053539)
                ·
                  refine ⟨1219215768872233533080309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812810512581489022053539 1219215768872233533080309)
                  ·
                    refine ⟨114301478331771893726279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1219215768872233533080309 114301478331771893726279)
                    ·
                      rfl

theorem cell22_333902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_333902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333902 prefixEnd_333902 := by exact prefixLift 333902
  have htrace : WordTrace (prefixWord ++ tailWord_333902) baseStart_333902 baseEnd_333902 := by
    simpa [prefixWord, tailWord_333902, baseEnd_333902] using wordTrace_append hprefix tailTrace_333902
  have hstable : (prefixWord ++ tailWord_333902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333902).length < 2 ^ (prefixWord ++ tailWord_333902).sum := by decide
  have hdescent : baseEnd_333902 < baseStart_333902 := by decide
  rcases family_descends (prefixWord ++ tailWord_333902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333936 : List Nat := [2, 1, 1, 1, 5, 4, 1, 2, 2, 3]
def baseStart_333936 : Nat := 118140960795 + 333936 * 2 ^ 59
def prefixEnd_333936 : Nat := 4983230072969 + 3 ^ 40 * 333936 * 2
def baseEnd_333936 : Nat := 114313117226607138376175

theorem tailTrace_333936 : CollatzResearch.WordTrace tailWord_333936 prefixEnd_333936 114313117226607138376175 := by
  unfold tailWord_333936
  simp only [CollatzResearch.WordTrace]
  refine ⟨6089823259107189286690831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8119764345476252382254441 6089823259107189286690831)
  ·
    refine ⟨9134734888660783930036247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6089823259107189286690831 9134734888660783930036247)
    ·
      refine ⟨13702102332991175895054371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9134734888660783930036247 13702102332991175895054371)
      ·
        refine ⟨20553153499486763842581557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13702102332991175895054371 20553153499486763842581557)
        ·
          refine ⟨1926858140576884110242021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20553153499486763842581557 1926858140576884110242021)
          ·
            refine ⟨361285901358165770670379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1926858140576884110242021 361285901358165770670379)
            ·
              refine ⟨541928852037248656005569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361285901358165770670379 541928852037248656005569)
              ·
                refine ⟨406446639027936492004177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541928852037248656005569 406446639027936492004177)
                ·
                  refine ⟨304834979270952369003133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406446639027936492004177 304834979270952369003133)
                  ·
                    refine ⟨114313117226607138376175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304834979270952369003133 114313117226607138376175)
                    ·
                      rfl

theorem cell22_333936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 2, 3].length) (baseStart_333936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333936 prefixEnd_333936 := by exact prefixLift 333936
  have htrace : WordTrace (prefixWord ++ tailWord_333936) baseStart_333936 baseEnd_333936 := by
    simpa [prefixWord, tailWord_333936, baseEnd_333936] using wordTrace_append hprefix tailTrace_333936
  have hstable : (prefixWord ++ tailWord_333936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333936).length < 2 ^ (prefixWord ++ tailWord_333936).sum := by decide
  have hdescent : baseEnd_333936 < baseStart_333936 := by decide
  rcases family_descends (prefixWord ++ tailWord_333936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333953 : List Nat := [1, 2, 4, 2, 3, 1, 3, 1, 2, 3]
def baseStart_333953 : Nat := 118140960795 + 333953 * 2 ^ 59
def prefixEnd_333953 : Nat := 4983230072969 + 3 ^ 40 * 333953 * 2
def baseEnd_333953 : Nat := 114318936674024760701123

theorem tailTrace_333953 : CollatzResearch.WordTrace tailWord_333953 prefixEnd_333953 114318936674024760701123 := by
  unfold tailWord_333953
  simp only [CollatzResearch.WordTrace]
  refine ⟨12180266559152790476750513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8120177706101860317833675 12180266559152790476750513)
  ·
    refine ⟨9135199919364592857562885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12180266559152790476750513 9135199919364592857562885)
    ·
      refine ⟨1712849984880861160793041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9135199919364592857562885 1712849984880861160793041)
      ·
        refine ⟨1284637488660645870594781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1712849984880861160793041 1284637488660645870594781)
        ·
          refine ⟨481739058247742201473043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1284637488660645870594781 481739058247742201473043)
          ·
            refine ⟨722608587371613302209565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481739058247742201473043 722608587371613302209565)
            ·
              refine ⟨270978220264354988328587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 722608587371613302209565 270978220264354988328587)
              ·
                refine ⟨406467330396532482492881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270978220264354988328587 406467330396532482492881)
                ·
                  refine ⟨304850497797399361869661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406467330396532482492881 304850497797399361869661)
                  ·
                    refine ⟨114318936674024760701123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304850497797399361869661 114318936674024760701123)
                    ·
                      rfl

theorem cell22_333953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_333953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333953 prefixEnd_333953 := by exact prefixLift 333953
  have htrace : WordTrace (prefixWord ++ tailWord_333953) baseStart_333953 baseEnd_333953 := by
    simpa [prefixWord, tailWord_333953, baseEnd_333953] using wordTrace_append hprefix tailTrace_333953
  have hstable : (prefixWord ++ tailWord_333953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333953).length < 2 ^ (prefixWord ++ tailWord_333953).sum := by decide
  have hdescent : baseEnd_333953 < baseStart_333953 := by decide
  rcases family_descends (prefixWord ++ tailWord_333953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333966 : List Nat := [4, 1, 1, 3, 3, 2, 2, 6]
def baseStart_333966 : Nat := 118140960795 + 333966 * 2 ^ 59
def prefixEnd_333966 : Nat := 4983230072969 + 3 ^ 40 * 333966 * 2
def baseEnd_333966 : Nat := 12702598537744117791787

theorem tailTrace_333966 : CollatzResearch.WordTrace tailWord_333966 prefixEnd_333966 12702598537744117791787 := by
  unfold tailWord_333966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1522592588513211712121719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8120493805403795797982501 1522592588513211712121719)
  ·
    refine ⟨2283888882769817568182579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1522592588513211712121719 2283888882769817568182579)
    ·
      refine ⟨3425833324154726352273869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2283888882769817568182579 3425833324154726352273869)
      ·
        refine ⟨1284687496558022382102701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3425833324154726352273869 1284687496558022382102701)
        ·
          refine ⟨481757811209258393288513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1284687496558022382102701 481757811209258393288513)
          ·
            refine ⟨361318358406943794966385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481757811209258393288513 361318358406943794966385)
            ·
              refine ⟨270988768805207846224789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361318358406943794966385 270988768805207846224789)
              ·
                refine ⟨12702598537744117791787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 270988768805207846224789 12702598537744117791787)
                ·
                  rfl

theorem cell22_333966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_333966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_333966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_333966 prefixEnd_333966 := by exact prefixLift 333966
  have htrace : WordTrace (prefixWord ++ tailWord_333966) baseStart_333966 baseEnd_333966 := by
    simpa [prefixWord, tailWord_333966, baseEnd_333966] using wordTrace_append hprefix tailTrace_333966
  have hstable : (prefixWord ++ tailWord_333966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333966).length < 2 ^ (prefixWord ++ tailWord_333966).sum := by decide
  have hdescent : baseEnd_333966 < baseStart_333966 := by decide
  rcases family_descends (prefixWord ++ tailWord_333966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334004 : List Nat := [2, 5, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_334004 : Nat := 118140960795 + 334004 * 2 ^ 59
def prefixEnd_334004 : Nat := 4983230072969 + 3 ^ 40 * 334004 * 2
def baseEnd_334004 : Nat := 114336395016277627675967

theorem tailTrace_334004 : CollatzResearch.WordTrace tailWord_334004 prefixEnd_334004 114336395016277627675967 := by
  unfold tailWord_334004
  simp only [CollatzResearch.WordTrace]
  refine ⟨6091063340984013093428533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8121417787978684124571377 6091063340984013093428533)
  ·
    refine ⟨571037188217251227508925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6091063340984013093428533 571037188217251227508925)
    ·
      refine ⟨214138945581469210315847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 571037188217251227508925 214138945581469210315847)
      ·
        refine ⟨321208418372203815473771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214138945581469210315847 321208418372203815473771)
        ·
          refine ⟨481812627558305723210657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321208418372203815473771 481812627558305723210657)
          ·
            refine ⟨361359470668729292407993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481812627558305723210657 361359470668729292407993)
            ·
              refine ⟨271019603001546969305995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361359470668729292407993 271019603001546969305995)
              ·
                refine ⟨406529404502320453958993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271019603001546969305995 406529404502320453958993)
                ·
                  refine ⟨304897053376740340469245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406529404502320453958993 304897053376740340469245)
                  ·
                    refine ⟨114336395016277627675967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304897053376740340469245 114336395016277627675967)
                    ·
                      rfl

theorem cell22_334004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_334004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334004 prefixEnd_334004 := by exact prefixLift 334004
  have htrace : WordTrace (prefixWord ++ tailWord_334004) baseStart_334004 baseEnd_334004 := by
    simpa [prefixWord, tailWord_334004, baseEnd_334004] using wordTrace_append hprefix tailTrace_334004
  have hstable : (prefixWord ++ tailWord_334004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334004).length < 2 ^ (prefixWord ++ tailWord_334004).sum := by decide
  have hdescent : baseEnd_334004 < baseStart_334004 := by decide
  rcases family_descends (prefixWord ++ tailWord_334004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334039 : List Nat := [1, 1, 3, 2, 1, 2, 1, 7, 4]
def baseStart_334039 : Nat := 118140960795 + 334039 * 2 ^ 59
def prefixEnd_334039 : Nat := 4983230072969 + 3 ^ 40 * 334039 * 2
def baseEnd_334039 : Nat := 38116125410516401016953

theorem tailTrace_334039 : CollatzResearch.WordTrace tailWord_334039 prefixEnd_334039 38116125410516401016953 := by
  unfold tailWord_334039
  simp only [CollatzResearch.WordTrace]
  refine ⟨12183403236841227164381171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8122268824560818109587447 12183403236841227164381171)
  ·
    refine ⟨18275104855261840746571757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12183403236841227164381171 18275104855261840746571757)
    ·
      refine ⟨6853164320723190279964409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18275104855261840746571757 6853164320723190279964409)
      ·
        refine ⟨5139873240542392709973307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6853164320723190279964409 5139873240542392709973307)
        ·
          refine ⟨7709809860813589064959961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5139873240542392709973307 7709809860813589064959961)
          ·
            refine ⟨5782357395610191798719971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7709809860813589064959961 5782357395610191798719971)
            ·
              refine ⟨8673536093415287698079957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5782357395610191798719971 8673536093415287698079957)
              ·
                refine ⟨203286002189420805423749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8673536093415287698079957 203286002189420805423749)
                ·
                  refine ⟨38116125410516401016953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203286002189420805423749 38116125410516401016953)
                  ·
                    rfl

theorem cell22_334039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 4].length) (baseStart_334039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334039 prefixEnd_334039 := by exact prefixLift 334039
  have htrace : WordTrace (prefixWord ++ tailWord_334039) baseStart_334039 baseEnd_334039 := by
    simpa [prefixWord, tailWord_334039, baseEnd_334039] using wordTrace_append hprefix tailTrace_334039
  have hstable : (prefixWord ++ tailWord_334039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334039).length < 2 ^ (prefixWord ++ tailWord_334039).sum := by decide
  have hdescent : baseEnd_334039 < baseStart_334039 := by decide
  rcases family_descends (prefixWord ++ tailWord_334039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334052 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_334052 : Nat := 118140960795 + 334052 * 2 ^ 59
def prefixEnd_334052 : Nat := 4983230072969 + 3 ^ 40 * 334052 * 2
def baseEnd_334052 : Nat := 114352826397221502475819

theorem tailTrace_334052 : CollatzResearch.WordTrace tailWord_334052 prefixEnd_334052 114352826397221502475819 := by
  unfold tailWord_334052
  simp only [CollatzResearch.WordTrace]
  refine ⟨6091938692897065192302205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8122584923862753589736273 6091938692897065192302205)
  ·
    refine ⟨2284477009836399447113327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6091938692897065192302205 2284477009836399447113327)
    ·
      refine ⟨3426715514754599170669991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2284477009836399447113327 3426715514754599170669991)
      ·
        refine ⟨5140073272131898756004987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3426715514754599170669991 5140073272131898756004987)
        ·
          refine ⟨7710109908197848134007481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5140073272131898756004987 7710109908197848134007481)
          ·
            refine ⟨5782582431148386100505611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7710109908197848134007481 5782582431148386100505611)
            ·
              refine ⟨8673873646722579150758417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5782582431148386100505611 8673873646722579150758417)
              ·
                refine ⟨6505405235041934363068813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8673873646722579150758417 6505405235041934363068813)
                ·
                  refine ⟨2439526963140725386150805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6505405235041934363068813 2439526963140725386150805)
                  ·
                    refine ⟨114352826397221502475819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2439526963140725386150805 114352826397221502475819)
                    ·
                      rfl

theorem cell22_334052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_334052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334052 prefixEnd_334052 := by exact prefixLift 334052
  have htrace : WordTrace (prefixWord ++ tailWord_334052) baseStart_334052 baseEnd_334052 := by
    simpa [prefixWord, tailWord_334052, baseEnd_334052] using wordTrace_append hprefix tailTrace_334052
  have hstable : (prefixWord ++ tailWord_334052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334052).length < 2 ^ (prefixWord ++ tailWord_334052).sum := by decide
  have hdescent : baseEnd_334052 < baseStart_334052 := by decide
  rcases family_descends (prefixWord ++ tailWord_334052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334056 : List Nat := [2, 1, 4, 1, 2, 3, 1, 4, 4]
def baseStart_334056 : Nat := 118140960795 + 334056 * 2 ^ 59
def prefixEnd_334056 : Nat := 4983230072969 + 3 ^ 40 * 334056 * 2
def baseEnd_334056 : Nat := 38118065226322275125269

theorem tailTrace_334056 : CollatzResearch.WordTrace tailWord_334056 prefixEnd_334056 38118065226322275125269 := by
  unfold tailWord_334056
  simp only [CollatzResearch.WordTrace]
  refine ⟨6092011638889819533875011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8122682185186426045166681 6092011638889819533875011)
  ·
    refine ⟨9138017458334729300812517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6092011638889819533875011 9138017458334729300812517)
    ·
      refine ⟨1713378273437761743902347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9138017458334729300812517 1713378273437761743902347)
      ·
        refine ⟨2570067410156642615853521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713378273437761743902347 2570067410156642615853521)
        ·
          refine ⟨1927550557617481961890141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2570067410156642615853521 1927550557617481961890141)
          ·
            refine ⟨722831459106555735708803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1927550557617481961890141 722831459106555735708803)
            ·
              refine ⟨1084247188659833603563205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722831459106555735708803 1084247188659833603563205)
              ·
                refine ⟨203296347873718800668101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1084247188659833603563205 203296347873718800668101)
                ·
                  refine ⟨38118065226322275125269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203296347873718800668101 38118065226322275125269)
                  ·
                    rfl

theorem cell22_334056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 4].length) (baseStart_334056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334056 prefixEnd_334056 := by exact prefixLift 334056
  have htrace : WordTrace (prefixWord ++ tailWord_334056) baseStart_334056 baseEnd_334056 := by
    simpa [prefixWord, tailWord_334056, baseEnd_334056] using wordTrace_append hprefix tailTrace_334056
  have hstable : (prefixWord ++ tailWord_334056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334056).length < 2 ^ (prefixWord ++ tailWord_334056).sum := by decide
  have hdescent : baseEnd_334056 < baseStart_334056 := by decide
  rcases family_descends (prefixWord ++ tailWord_334056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334116 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_334116 : Nat := 118140960795 + 334116 * 2 ^ 59
def prefixEnd_334116 : Nat := 4983230072969 + 3 ^ 40 * 334116 * 2
def baseEnd_334116 : Nat := 114374734905146668875623

theorem tailTrace_334116 : CollatzResearch.WordTrace tailWord_334116 prefixEnd_334116 114374734905146668875623 := by
  unfold tailWord_334116
  simp only [CollatzResearch.WordTrace]
  refine ⟨6093105828781134657467101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8124141105041512876622801 6093105828781134657467101)
  ·
    refine ⟨2284914685792925496550163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6093105828781134657467101 2284914685792925496550163)
    ·
      refine ⟨3427372028689388244825245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2284914685792925496550163 3427372028689388244825245)
      ·
        refine ⟨1285264510758520591809467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3427372028689388244825245 1285264510758520591809467)
        ·
          refine ⟨1927896766137780887714201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285264510758520591809467 1927896766137780887714201)
          ·
            refine ⟨1445922574603335665785651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1927896766137780887714201 1445922574603335665785651)
            ·
              refine ⟨2168883861905003498678477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1445922574603335665785651 2168883861905003498678477)
              ·
                refine ⟨813331448214376312004429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2168883861905003498678477 813331448214376312004429)
                ·
                  refine ⟨304999293080391117001661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813331448214376312004429 304999293080391117001661)
                  ·
                    refine ⟨114374734905146668875623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 304999293080391117001661 114374734905146668875623)
                    ·
                      rfl

theorem cell22_334116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_334116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334116 prefixEnd_334116 := by exact prefixLift 334116
  have htrace : WordTrace (prefixWord ++ tailWord_334116) baseStart_334116 baseEnd_334116 := by
    simpa [prefixWord, tailWord_334116, baseEnd_334116] using wordTrace_append hprefix tailTrace_334116
  have hstable : (prefixWord ++ tailWord_334116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334116).length < 2 ^ (prefixWord ++ tailWord_334116).sum := by decide
  have hdescent : baseEnd_334116 < baseStart_334116 := by decide
  rcases family_descends (prefixWord ++ tailWord_334116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334264 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 7]
def baseStart_334264 : Nat := 118140960795 + 334264 * 2 ^ 59
def prefixEnd_334264 : Nat := 4983230072969 + 3 ^ 40 * 334264 * 2
def baseEnd_334264 : Nat := 38141799443241205391723

theorem tailTrace_334264 : CollatzResearch.WordTrace tailWord_334264 prefixEnd_334264 38141799443241205391723 := by
  unfold tailWord_334264
  simp only [CollatzResearch.WordTrace]
  refine ⟨6095804830513045295660923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8127739774017393727547897 6095804830513045295660923)
  ·
    refine ⟨9143707245769567943491385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6095804830513045295660923 9143707245769567943491385)
    ·
      refine ⟨6857780434327175957618539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9143707245769567943491385 6857780434327175957618539)
      ·
        refine ⟨10286670651490763936427809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6857780434327175957618539 10286670651490763936427809)
        ·
          refine ⟨7715002988618072952320857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10286670651490763936427809 7715002988618072952320857)
          ·
            refine ⟨5786252241463554714240643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7715002988618072952320857 5786252241463554714240643)
            ·
              refine ⟨8679378362195332071360965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5786252241463554714240643 8679378362195332071360965)
              ·
                refine ⟨1627383442911624763380181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8679378362195332071360965 1627383442911624763380181)
                ·
                  refine ⟨38141799443241205391723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1627383442911624763380181 38141799443241205391723)
                  ·
                    rfl

theorem cell22_334264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_334264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334264 prefixEnd_334264 := by exact prefixLift 334264
  have htrace : WordTrace (prefixWord ++ tailWord_334264) baseStart_334264 baseEnd_334264 := by
    simpa [prefixWord, tailWord_334264, baseEnd_334264] using wordTrace_append hprefix tailTrace_334264
  have hstable : (prefixWord ++ tailWord_334264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334264).length < 2 ^ (prefixWord ++ tailWord_334264).sum := by decide
  have hdescent : baseEnd_334264 < baseStart_334264 := by decide
  rcases family_descends (prefixWord ++ tailWord_334264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334281 : List Nat := [1, 2, 1, 1, 2, 1, 7, 2, 5]
def baseStart_334281 : Nat := 118140960795 + 334281 * 2 ^ 59
def prefixEnd_334281 : Nat := 4983230072969 + 3 ^ 40 * 334281 * 2
def baseEnd_334281 : Nat := 38143739259047079500039

theorem tailTrace_334281 : CollatzResearch.WordTrace tailWord_334281 prefixEnd_334281 38143739259047079500039 := by
  unfold tailWord_334281
  simp only [CollatzResearch.WordTrace]
  refine ⟨12192229701964502494690697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8128153134643001663127131 12192229701964502494690697)
  ·
    refine ⟨9144172276473376871018023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12192229701964502494690697 9144172276473376871018023)
    ·
      refine ⟨13716258414710065306527035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9144172276473376871018023 13716258414710065306527035)
      ·
        refine ⟨20574387622065097959790553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13716258414710065306527035 20574387622065097959790553)
        ·
          refine ⟨15430790716548823469842915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20574387622065097959790553 15430790716548823469842915)
          ·
            refine ⟨23146186074823235204764373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15430790716548823469842915 23146186074823235204764373)
            ·
              refine ⟨542488736128669575111665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23146186074823235204764373 542488736128669575111665)
              ·
                refine ⟨406866552096502181333749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542488736128669575111665 406866552096502181333749)
                ·
                  refine ⟨38143739259047079500039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 406866552096502181333749 38143739259047079500039)
                  ·
                    rfl

theorem cell22_334281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 5].length) (baseStart_334281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334281 prefixEnd_334281 := by exact prefixLift 334281
  have htrace : WordTrace (prefixWord ++ tailWord_334281) baseStart_334281 baseEnd_334281 := by
    simpa [prefixWord, tailWord_334281, baseEnd_334281] using wordTrace_append hprefix tailTrace_334281
  have hstable : (prefixWord ++ tailWord_334281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334281).length < 2 ^ (prefixWord ++ tailWord_334281).sum := by decide
  have hdescent : baseEnd_334281 < baseStart_334281 := by decide
  rcases family_descends (prefixWord ++ tailWord_334281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334298 : List Nat := [3, 1, 1, 2, 3, 1, 5, 1, 5]
def baseStart_334298 : Nat := 118140960795 + 334298 * 2 ^ 59
def prefixEnd_334298 : Nat := 4983230072969 + 3 ^ 40 * 334298 * 2
def baseEnd_334298 : Nat := 38145679074852953608355

theorem tailTrace_334298 : CollatzResearch.WordTrace tailWord_334298 prefixEnd_334298 38145679074852953608355 := by
  unfold tailWord_334298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3048212435725728599514887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8128566495268609598706365 3048212435725728599514887)
  ·
    refine ⟨4572318653588592899272331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3048212435725728599514887 4572318653588592899272331)
    ·
      refine ⟨6858477980382889348908497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4572318653588592899272331 6858477980382889348908497)
      ·
        refine ⟨5143858485287167011681373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6858477980382889348908497 5143858485287167011681373)
        ·
          refine ⟨1928946931982687629380515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5143858485287167011681373 1928946931982687629380515)
          ·
            refine ⟨2893420397974031444070773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928946931982687629380515 2893420397974031444070773)
            ·
              refine ⟨271258162310065447881635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2893420397974031444070773 271258162310065447881635)
              ·
                refine ⟨406887243465098171822453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271258162310065447881635 406887243465098171822453)
                ·
                  refine ⟨38145679074852953608355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 406887243465098171822453 38145679074852953608355)
                  ·
                    rfl

theorem cell22_334298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_334298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334298 prefixEnd_334298 := by exact prefixLift 334298
  have htrace : WordTrace (prefixWord ++ tailWord_334298) baseStart_334298 baseEnd_334298 := by
    simpa [prefixWord, tailWord_334298, baseEnd_334298] using wordTrace_append hprefix tailTrace_334298
  have hstable : (prefixWord ++ tailWord_334298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334298).length < 2 ^ (prefixWord ++ tailWord_334298).sum := by decide
  have hdescent : baseEnd_334298 < baseStart_334298 := by decide
  rcases family_descends (prefixWord ++ tailWord_334298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334349 : List Nat := [1, 7, 1, 1, 1, 3, 2, 1, 5]
def baseStart_334349 : Nat := 118140960795 + 334349 * 2 ^ 59
def prefixEnd_334349 : Nat := 4983230072969 + 3 ^ 40 * 334349 * 2
def baseEnd_334349 : Nat := 38151498522270575933303

theorem tailTrace_334349 : CollatzResearch.WordTrace tailWord_334349 prefixEnd_334349 38151498522270575933303 := by
  unfold tailWord_334349
  simp only [CollatzResearch.WordTrace]
  refine ⟨12194709865718150108166101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8129806577145433405444067 12194709865718150108166101)
  ·
    refine ⟨285813512477769143160143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12194709865718150108166101 285813512477769143160143)
    ·
      refine ⟨428720268716653714740215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285813512477769143160143 428720268716653714740215)
      ·
        refine ⟨643080403074980572110323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428720268716653714740215 643080403074980572110323)
        ·
          refine ⟨964620604612470858165485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643080403074980572110323 964620604612470858165485)
          ·
            refine ⟨361732726729676571812057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 964620604612470858165485 361732726729676571812057)
            ·
              refine ⟨271299545047257428859043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361732726729676571812057 271299545047257428859043)
              ·
                refine ⟨406949317570886143288565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271299545047257428859043 406949317570886143288565)
                ·
                  refine ⟨38151498522270575933303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 406949317570886143288565 38151498522270575933303)
                  ·
                    rfl

theorem cell22_334349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_334349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334349 prefixEnd_334349 := by exact prefixLift 334349
  have htrace : WordTrace (prefixWord ++ tailWord_334349) baseStart_334349 baseEnd_334349 := by
    simpa [prefixWord, tailWord_334349, baseEnd_334349] using wordTrace_append hprefix tailTrace_334349
  have hstable : (prefixWord ++ tailWord_334349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334349).length < 2 ^ (prefixWord ++ tailWord_334349).sum := by decide
  have hdescent : baseEnd_334349 < baseStart_334349 := by decide
  rcases family_descends (prefixWord ++ tailWord_334349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334371 : List Nat := [1, 1, 1, 4, 4, 1, 2, 8]
def baseStart_334371 : Nat := 118140960795 + 334371 * 2 ^ 59
def prefixEnd_334371 : Nat := 4983230072969 + 3 ^ 40 * 334371 * 2
def baseEnd_334371 : Nat := 12718002957379000416649

theorem tailTrace_334371 : CollatzResearch.WordTrace tailWord_334371 prefixEnd_334371 12718002957379000416649 := by
  unfold tailWord_334371
  simp only [CollatzResearch.WordTrace]
  refine ⟨12195512271638447865466967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8130341514425631910311311 12195512271638447865466967)
  ·
    refine ⟨18293268407457671798200451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12195512271638447865466967 18293268407457671798200451)
    ·
      refine ⟨27439902611186507697300677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18293268407457671798200451 27439902611186507697300677)
      ·
        refine ⟨5144981739597470193243877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27439902611186507697300677 5144981739597470193243877)
        ·
          refine ⟨964684076174525661233227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5144981739597470193243877 964684076174525661233227)
          ·
            refine ⟨1447026114261788491849841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964684076174525661233227 1447026114261788491849841)
            ·
              refine ⟨1085269585696341368887381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447026114261788491849841 1085269585696341368887381)
              ·
                refine ⟨12718002957379000416649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1085269585696341368887381 12718002957379000416649)
                ·
                  rfl

theorem cell22_334371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 8].length) (baseStart_334371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334371 prefixEnd_334371 := by exact prefixLift 334371
  have htrace : WordTrace (prefixWord ++ tailWord_334371) baseStart_334371 baseEnd_334371 := by
    simpa [prefixWord, tailWord_334371, baseEnd_334371] using wordTrace_append hprefix tailTrace_334371
  have hstable : (prefixWord ++ tailWord_334371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334371).length < 2 ^ (prefixWord ++ tailWord_334371).sum := by decide
  have hdescent : baseEnd_334371 < baseStart_334371 := by decide
  rcases family_descends (prefixWord ++ tailWord_334371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334388 : List Nat := [2, 5, 1, 3, 11]
def baseStart_334388 : Nat := 118140960795 + 334388 * 2 ^ 59
def prefixEnd_334388 : Nat := 4983230072969 + 3 ^ 40 * 334388 * 2
def baseEnd_334388 : Nat := 471061094912875004423

theorem tailTrace_334388 : CollatzResearch.WordTrace tailWord_334388 prefixEnd_334388 471061094912875004423 := by
  unfold tailWord_334388
  simp only [CollatzResearch.WordTrace]
  refine ⟨6098066156288429884417909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8130754875051239845890545 6098066156288429884417909)
  ·
    refine ⟨571693702152040301664179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6098066156288429884417909 571693702152040301664179)
    ·
      refine ⟨857540553228060452496269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 571693702152040301664179 857540553228060452496269)
      ·
        refine ⟨321577707460522669686101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 857540553228060452496269 321577707460522669686101)
        ·
          refine ⟨471061094912875004423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 321577707460522669686101 471061094912875004423)
          ·
            rfl

theorem cell22_334388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 11].length) (baseStart_334388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334388 prefixEnd_334388 := by exact prefixLift 334388
  have htrace : WordTrace (prefixWord ++ tailWord_334388) baseStart_334388 baseEnd_334388 := by
    simpa [prefixWord, tailWord_334388, baseEnd_334388] using wordTrace_append hprefix tailTrace_334388
  have hstable : (prefixWord ++ tailWord_334388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334388).length < 2 ^ (prefixWord ++ tailWord_334388).sum := by decide
  have hdescent : baseEnd_334388 < baseStart_334388 := by decide
  rcases family_descends (prefixWord ++ tailWord_334388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334390 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_334390 : Nat := 118140960795 + 334390 * 2 ^ 59
def prefixEnd_334390 : Nat := 4983230072969 + 3 ^ 40 * 334390 * 2
def baseEnd_334390 : Nat := 114468530704701287524783

theorem tailTrace_334390 : CollatzResearch.WordTrace tailWord_334390 prefixEnd_334390 114468530704701287524783 := by
  unfold tailWord_334390
  simp only [CollatzResearch.WordTrace]
  refine ⟨762262828660600881900539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8130803505713076073605749 762262828660600881900539)
  ·
    refine ⟨1143394242990901322850809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 762262828660600881900539 1143394242990901322850809)
    ·
      refine ⟨857545682243175992138107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1143394242990901322850809 857545682243175992138107)
      ·
        refine ⟨1286318523364763988207161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857545682243175992138107 1286318523364763988207161)
        ·
          refine ⟨964738892523572991155371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1286318523364763988207161 964738892523572991155371)
          ·
            refine ⟨1447108338785359486733057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964738892523572991155371 1447108338785359486733057)
            ·
              refine ⟨1085331254089019615049793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447108338785359486733057 1085331254089019615049793)
              ·
                refine ⟨813998440566764711287345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085331254089019615049793 813998440566764711287345)
                ·
                  refine ⟨610498830425073533465509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 813998440566764711287345 610498830425073533465509)
                  ·
                    refine ⟨114468530704701287524783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 610498830425073533465509 114468530704701287524783)
                    ·
                      rfl

theorem cell22_334390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_334390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334390 prefixEnd_334390 := by exact prefixLift 334390
  have htrace : WordTrace (prefixWord ++ tailWord_334390) baseStart_334390 baseEnd_334390 := by
    simpa [prefixWord, tailWord_334390, baseEnd_334390] using wordTrace_append hprefix tailTrace_334390
  have hstable : (prefixWord ++ tailWord_334390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334390).length < 2 ^ (prefixWord ++ tailWord_334390).sum := by decide
  have hdescent : baseEnd_334390 < baseStart_334390 := by decide
  rcases family_descends (prefixWord ++ tailWord_334390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334420 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_334420 : Nat := 118140960795 + 334420 * 2 ^ 59
def prefixEnd_334420 : Nat := 4983230072969 + 3 ^ 40 * 334420 * 2
def baseEnd_334420 : Nat := 114478800317791209274691

theorem tailTrace_334420 : CollatzResearch.WordTrace tailWord_334420 prefixEnd_334420 114478800317791209274691 := by
  unfold tailWord_334420
  simp only [CollatzResearch.WordTrace]
  refine ⟨6098649724230464617000357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8131532965640619489333809 6098649724230464617000357)
  ·
    refine ⟨1143496823293212115687567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6098649724230464617000357 1143496823293212115687567)
    ·
      refine ⟨1715245234939818173531351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1143496823293212115687567 1715245234939818173531351)
      ·
        refine ⟨2572867852409727260297027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1715245234939818173531351 2572867852409727260297027)
        ·
          refine ⟨3859301778614590890445541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572867852409727260297027 3859301778614590890445541)
          ·
            refine ⟨723619083490235791958539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3859301778614590890445541 723619083490235791958539)
            ·
              refine ⟨1085428625235353687937809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723619083490235791958539 1085428625235353687937809)
              ·
                refine ⟨814071468926515265953357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085428625235353687937809 814071468926515265953357)
                ·
                  refine ⟨305276800847443224732509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814071468926515265953357 305276800847443224732509)
                  ·
                    refine ⟨114478800317791209274691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305276800847443224732509 114478800317791209274691)
                    ·
                      rfl

theorem cell22_334420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_334420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334420 prefixEnd_334420 := by exact prefixLift 334420
  have htrace : WordTrace (prefixWord ++ tailWord_334420) baseStart_334420 baseEnd_334420 := by
    simpa [prefixWord, tailWord_334420, baseEnd_334420] using wordTrace_append hprefix tailTrace_334420
  have hstable : (prefixWord ++ tailWord_334420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334420).length < 2 ^ (prefixWord ++ tailWord_334420).sum := by decide
  have hdescent : baseEnd_334420 < baseStart_334420 := by decide
  rcases family_descends (prefixWord ++ tailWord_334420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334478 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_334478 : Nat := 118140960795 + 334478 * 2 ^ 59
def prefixEnd_334478 : Nat := 4983230072969 + 3 ^ 40 * 334478 * 2
def baseEnd_334478 : Nat := 38166218301032797108171

theorem tailTrace_334478 : CollatzResearch.WordTrace tailWord_334478 prefixEnd_334478 38166218301032797108171 := by
  unfold tailWord_334478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1524926860281350642451511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8132943254833870093074725 1524926860281350642451511)
  ·
    refine ⟨2287390290422025963677267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1524926860281350642451511 2287390290422025963677267)
    ·
      refine ⟨3431085435633038945515901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2287390290422025963677267 3431085435633038945515901)
      ·
        refine ⟨1286657038362389604568463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3431085435633038945515901 1286657038362389604568463)
        ·
          refine ⟨1929985557543584406852695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286657038362389604568463 1929985557543584406852695)
          ·
            refine ⟨2894978336315376610279043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929985557543584406852695 2894978336315376610279043)
            ·
              refine ⟨4342467504473064915418565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2894978336315376610279043 4342467504473064915418565)
              ·
                refine ⟨814212657088699671640981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4342467504473064915418565 814212657088699671640981)
                ·
                  refine ⟨38166218301032797108171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 814212657088699671640981 38166218301032797108171)
                  ·
                    rfl

theorem cell22_334478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_334478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334478 prefixEnd_334478 := by exact prefixLift 334478
  have htrace : WordTrace (prefixWord ++ tailWord_334478) baseStart_334478 baseEnd_334478 := by
    simpa [prefixWord, tailWord_334478, baseEnd_334478] using wordTrace_append hprefix tailTrace_334478
  have hstable : (prefixWord ++ tailWord_334478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334478).length < 2 ^ (prefixWord ++ tailWord_334478).sum := by decide
  have hdescent : baseEnd_334478 < baseStart_334478 := by decide
  rcases family_descends (prefixWord ++ tailWord_334478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334493 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_334493 : Nat := 118140960795 + 334493 * 2 ^ 59
def prefixEnd_334493 : Nat := 4983230072969 + 3 ^ 40 * 334493 * 2
def baseEnd_334493 : Nat := 114503789709643352199467

theorem tailTrace_334493 : CollatzResearch.WordTrace tailWord_334493 prefixEnd_334493 114503789709643352199467 := by
  unfold tailWord_334493
  simp only [CollatzResearch.WordTrace]
  refine ⟨12199961977196462701408133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8133307984797641800938755 12199961977196462701408133)
  ·
    refine ⟨2287492870724336756514025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12199961977196462701408133 2287492870724336756514025)
    ·
      refine ⟨1715619653043252567385519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2287492870724336756514025 1715619653043252567385519)
      ·
        refine ⟨2573429479564878851078279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1715619653043252567385519 2573429479564878851078279)
        ·
          refine ⟨3860144219347318276617419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2573429479564878851078279 3860144219347318276617419)
          ·
            refine ⟨5790216329020977414926129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860144219347318276617419 5790216329020977414926129)
            ·
              refine ⟨4342662246765733061194597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5790216329020977414926129 4342662246765733061194597)
              ·
                refine ⟨814249171268574948973987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4342662246765733061194597 814249171268574948973987)
                ·
                  refine ⟨1221373756902862423460981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814249171268574948973987 1221373756902862423460981)
                  ·
                    refine ⟨114503789709643352199467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1221373756902862423460981 114503789709643352199467)
                    ·
                      rfl

theorem cell22_334493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_334493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334493 prefixEnd_334493 := by exact prefixLift 334493
  have htrace : WordTrace (prefixWord ++ tailWord_334493) baseStart_334493 baseEnd_334493 := by
    simpa [prefixWord, tailWord_334493, baseEnd_334493] using wordTrace_append hprefix tailTrace_334493
  have hstable : (prefixWord ++ tailWord_334493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334493).length < 2 ^ (prefixWord ++ tailWord_334493).sum := by decide
  have hdescent : baseEnd_334493 < baseStart_334493 := by decide
  rcases family_descends (prefixWord ++ tailWord_334493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334527 : List Nat := [1, 1, 2, 2, 2, 4, 4, 1, 2, 3]
def baseStart_334527 : Nat := 118140960795 + 334527 * 2 ^ 59
def prefixEnd_334527 : Nat := 4983230072969 + 3 ^ 40 * 334527 * 2
def baseEnd_334527 : Nat := 114515428604478596849363

theorem tailTrace_334527 : CollatzResearch.WordTrace tailWord_334527 prefixEnd_334527 114515428604478596849363 := by
  unfold tailWord_334527
  simp only [CollatzResearch.WordTrace]
  refine ⟨12201202059073286508145835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8134134706048857672097223 12201202059073286508145835)
  ·
    refine ⟨18301803088609929762218753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12201202059073286508145835 18301803088609929762218753)
    ·
      refine ⟨13726352316457447321664065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18301803088609929762218753 13726352316457447321664065)
      ·
        refine ⟨10294764237343085491248049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13726352316457447321664065 10294764237343085491248049)
        ·
          refine ⟨7721073178007314118436037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10294764237343085491248049 7721073178007314118436037)
          ·
            refine ⟨1447701220876371397206757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7721073178007314118436037 1447701220876371397206757)
            ·
              refine ⟨271443978914319636976267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1447701220876371397206757 271443978914319636976267)
              ·
                refine ⟨407165968371479455464401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271443978914319636976267 407165968371479455464401)
                ·
                  refine ⟨305374476278609591598301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407165968371479455464401 305374476278609591598301)
                  ·
                    refine ⟨114515428604478596849363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305374476278609591598301 114515428604478596849363)
                    ·
                      rfl

theorem cell22_334527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 2, 3].length) (baseStart_334527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334527 prefixEnd_334527 := by exact prefixLift 334527
  have htrace : WordTrace (prefixWord ++ tailWord_334527) baseStart_334527 baseEnd_334527 := by
    simpa [prefixWord, tailWord_334527, baseEnd_334527] using wordTrace_append hprefix tailTrace_334527
  have hstable : (prefixWord ++ tailWord_334527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334527).length < 2 ^ (prefixWord ++ tailWord_334527).sum := by decide
  have hdescent : baseEnd_334527 < baseStart_334527 := by decide
  rcases family_descends (prefixWord ++ tailWord_334527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334613 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 8]
def baseStart_334613 : Nat := 118140960795 + 334613 * 2 ^ 59
def prefixEnd_334613 : Nat := 4983230072969 + 3 ^ 40 * 334613 * 2
def baseEnd_334613 : Nat := 38181622720667679733033

theorem tailTrace_334613 : CollatzResearch.WordTrace tailWord_334613 prefixEnd_334613 38181622720667679733033 := by
  unfold tailWord_334613
  simp only [CollatzResearch.WordTrace]
  refine ⟨12204338736761723195776493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8136225824507815463850995 12204338736761723195776493)
  ·
    refine ⟨4576627026285646198416185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12204338736761723195776493 4576627026285646198416185)
    ·
      refine ⟨3432470269714234648812139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4576627026285646198416185 3432470269714234648812139)
      ·
        refine ⟨5148705404571351973218209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3432470269714234648812139 5148705404571351973218209)
        ·
          refine ⟨3861529053428513979913657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5148705404571351973218209 3861529053428513979913657)
          ·
            refine ⟨2896146790071385484935243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3861529053428513979913657 2896146790071385484935243)
            ·
              refine ⟨4344220185107078227402865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896146790071385484935243 4344220185107078227402865)
              ·
                refine ⟨3258165138830308670552149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4344220185107078227402865 3258165138830308670552149)
                ·
                  refine ⟨38181622720667679733033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3258165138830308670552149 38181622720667679733033)
                  ·
                    rfl

theorem cell22_334613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_334613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334613 prefixEnd_334613 := by exact prefixLift 334613
  have htrace : WordTrace (prefixWord ++ tailWord_334613) baseStart_334613 baseEnd_334613 := by
    simpa [prefixWord, tailWord_334613, baseEnd_334613] using wordTrace_append hprefix tailTrace_334613
  have hstable : (prefixWord ++ tailWord_334613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334613).length < 2 ^ (prefixWord ++ tailWord_334613).sum := by decide
  have hdescent : baseEnd_334613 < baseStart_334613 := by decide
  rcases family_descends (prefixWord ++ tailWord_334613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334696 : List Nat := [2, 1, 4, 2, 1, 4, 2, 1, 2, 3]
def baseStart_334696 : Nat := 118140960795 + 334696 * 2 ^ 59
def prefixEnd_334696 : Nat := 4983230072969 + 3 ^ 40 * 334696 * 2
def baseEnd_334696 : Nat := 114573280758218489373845

theorem tailTrace_334696 : CollatzResearch.WordTrace tailWord_334696 prefixEnd_334696 114573280758218489373845 := by
  unfold tailWord_334696
  simp only [CollatzResearch.WordTrace]
  refine ⟨6103682997730514185523971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8138243996974018914031961 6103682997730514185523971)
  ·
    refine ⟨9155524496595771278285957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6103682997730514185523971 9155524496595771278285957)
    ·
      refine ⟨1716660843111707114678617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9155524496595771278285957 1716660843111707114678617)
      ·
        refine ⟨1287495632333780336008963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1716660843111707114678617 1287495632333780336008963)
        ·
          refine ⟨1931243448500670504013445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287495632333780336008963 1931243448500670504013445)
          ·
            refine ⟨362108146593875719502521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1931243448500670504013445 362108146593875719502521)
            ·
              refine ⟨271581109945406789626891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362108146593875719502521 271581109945406789626891)
              ·
                refine ⟨407371664918110184440337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271581109945406789626891 407371664918110184440337)
                ·
                  refine ⟨305528748688582638330253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407371664918110184440337 305528748688582638330253)
                  ·
                    refine ⟨114573280758218489373845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305528748688582638330253 114573280758218489373845)
                    ·
                      rfl

theorem cell22_334696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_334696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334696 prefixEnd_334696 := by exact prefixLift 334696
  have htrace : WordTrace (prefixWord ++ tailWord_334696) baseStart_334696 baseEnd_334696 := by
    simpa [prefixWord, tailWord_334696, baseEnd_334696] using wordTrace_append hprefix tailTrace_334696
  have hstable : (prefixWord ++ tailWord_334696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334696).length < 2 ^ (prefixWord ++ tailWord_334696).sum := by decide
  have hdescent : baseEnd_334696 < baseStart_334696 := by decide
  rcases family_descends (prefixWord ++ tailWord_334696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334724 : List Nat := [2, 3, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_334724 : Nat := 118140960795 + 334724 * 2 ^ 59
def prefixEnd_334724 : Nat := 4983230072969 + 3 ^ 40 * 334724 * 2
def baseEnd_334724 : Nat := 114582865730435749673759

theorem tailTrace_334724 : CollatzResearch.WordTrace tailWord_334724 prefixEnd_334724 114582865730435749673759 := by
  unfold tailWord_334724
  simp only [CollatzResearch.WordTrace]
  refine ⟨6104193619679794576533613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8138924826239726102044817 6104193619679794576533613)
  ·
    refine ⟨2289072607379922966200105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6104193619679794576533613 2289072607379922966200105)
    ·
      refine ⟨1716804455534942224650079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2289072607379922966200105 1716804455534942224650079)
      ·
        refine ⟨2575206683302413336975119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1716804455534942224650079 2575206683302413336975119)
        ·
          refine ⟨3862810024953620005462679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575206683302413336975119 3862810024953620005462679)
          ·
            refine ⟨5794215037430430008194019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3862810024953620005462679 5794215037430430008194019)
            ·
              refine ⟨8691322556145645012291029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5794215037430430008194019 8691322556145645012291029)
              ·
                refine ⟨203702872409663554975571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8691322556145645012291029 203702872409663554975571)
                ·
                  refine ⟨305554308614495332463357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203702872409663554975571 305554308614495332463357)
                  ·
                    refine ⟨114582865730435749673759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305554308614495332463357 114582865730435749673759)
                    ·
                      rfl

theorem cell22_334724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_334724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334724 prefixEnd_334724 := by exact prefixLift 334724
  have htrace : WordTrace (prefixWord ++ tailWord_334724) baseStart_334724 baseEnd_334724 := by
    simpa [prefixWord, tailWord_334724, baseEnd_334724] using wordTrace_append hprefix tailTrace_334724
  have hstable : (prefixWord ++ tailWord_334724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334724).length < 2 ^ (prefixWord ++ tailWord_334724).sum := by decide
  have hdescent : baseEnd_334724 < baseStart_334724 := by decide
  rcases family_descends (prefixWord ++ tailWord_334724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334741 : List Nat := [1, 3, 2, 1, 1, 4, 4, 2, 1, 3]
def baseStart_334741 : Nat := 118140960795 + 334741 * 2 ^ 59
def prefixEnd_334741 : Nat := 4983230072969 + 3 ^ 40 * 334741 * 2
def baseEnd_334741 : Nat := 114588685177853371998707

theorem tailTrace_334741 : CollatzResearch.WordTrace tailWord_334741 prefixEnd_334741 114588685177853371998707 := by
  unfold tailWord_334741
  simp only [CollatzResearch.WordTrace]
  refine ⟨12209007280298001056436077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8139338186865334037624051 12209007280298001056436077)
  ·
    refine ⟨4578377730111750396163529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12209007280298001056436077 4578377730111750396163529)
    ·
      refine ⟨3433783297583812797122647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4578377730111750396163529 3433783297583812797122647)
      ·
        refine ⟨5150674946375719195683971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433783297583812797122647 5150674946375719195683971)
        ·
          refine ⟨7726012419563578793525957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5150674946375719195683971 7726012419563578793525957)
          ·
            refine ⟨1448627328668171023786117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7726012419563578793525957 1448627328668171023786117)
            ·
              refine ⟨271617624125282066959897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1448627328668171023786117 271617624125282066959897)
              ·
                refine ⟨203713218093961550219923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271617624125282066959897 203713218093961550219923)
                ·
                  refine ⟨305569827140942325329885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203713218093961550219923 305569827140942325329885)
                  ·
                    refine ⟨114588685177853371998707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305569827140942325329885 114588685177853371998707)
                    ·
                      rfl

theorem cell22_334741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_334741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334741 prefixEnd_334741 := by exact prefixLift 334741
  have htrace : WordTrace (prefixWord ++ tailWord_334741) baseStart_334741 baseEnd_334741 := by
    simpa [prefixWord, tailWord_334741, baseEnd_334741] using wordTrace_append hprefix tailTrace_334741
  have hstable : (prefixWord ++ tailWord_334741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334741).length < 2 ^ (prefixWord ++ tailWord_334741).sum := by decide
  have hdescent : baseEnd_334741 < baseStart_334741 := by decide
  rcases family_descends (prefixWord ++ tailWord_334741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334784 : List Nat := [2, 1, 1, 2, 3, 3, 4, 1, 1, 4]
def baseStart_334784 : Nat := 118140960795 + 334784 * 2 ^ 59
def prefixEnd_334784 : Nat := 4983230072969 + 3 ^ 40 * 334784 * 2
def baseEnd_334784 : Nat := 114603404956615593173575

theorem tailTrace_334784 : CollatzResearch.WordTrace tailWord_334784 prefixEnd_334784 114603404956615593173575 := by
  unfold tailWord_334784
  simp only [CollatzResearch.WordTrace]
  refine ⟨6105287809571109700125703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8140383746094812933500937 6105287809571109700125703)
  ·
    refine ⟨9157931714356664550188555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6105287809571109700125703 9157931714356664550188555)
    ·
      refine ⟨13736897571534996825282833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9157931714356664550188555 13736897571534996825282833)
      ·
        refine ⟨10302673178651247618962125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13736897571534996825282833 10302673178651247618962125)
        ·
          refine ⟨3863502441994217857110797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10302673178651247618962125 3863502441994217857110797)
          ·
            refine ⟨1448813415747831696416549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3863502441994217857110797 1448813415747831696416549)
            ·
              refine ⟨271652515452718443078103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1448813415747831696416549 271652515452718443078103)
              ·
                refine ⟨407478773179077664617155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271652515452718443078103 407478773179077664617155)
                ·
                  refine ⟨611218159768616496925733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407478773179077664617155 611218159768616496925733)
                  ·
                    refine ⟨114603404956615593173575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 611218159768616496925733 114603404956615593173575)
                    ·
                      rfl

theorem cell22_334784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 1, 4].length) (baseStart_334784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334784 prefixEnd_334784 := by exact prefixLift 334784
  have htrace : WordTrace (prefixWord ++ tailWord_334784) baseStart_334784 baseEnd_334784 := by
    simpa [prefixWord, tailWord_334784, baseEnd_334784] using wordTrace_append hprefix tailTrace_334784
  have hstable : (prefixWord ++ tailWord_334784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334784).length < 2 ^ (prefixWord ++ tailWord_334784).sum := by decide
  have hdescent : baseEnd_334784 < baseStart_334784 := by decide
  rcases family_descends (prefixWord ++ tailWord_334784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334788 : List Nat := [2, 3, 3, 3, 2, 1, 1, 2, 5]
def baseStart_334788 : Nat := 118140960795 + 334788 * 2 ^ 59
def prefixEnd_334788 : Nat := 4983230072969 + 3 ^ 40 * 334788 * 2
def baseEnd_334788 : Nat := 38201591412786972024521

theorem tailTrace_334788 : CollatzResearch.WordTrace tailWord_334788 prefixEnd_334788 38201591412786972024521 := by
  unfold tailWord_334788
  simp only [CollatzResearch.WordTrace]
  refine ⟨6105360755563864041698509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8140481007418485388931345 6105360755563864041698509)
  ·
    refine ⟨2289510283336449015636941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6105360755563864041698509 2289510283336449015636941)
    ·
      refine ⟨858566356251168380863853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2289510283336449015636941 858566356251168380863853)
      ·
        refine ⟨321962383594188142823945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 858566356251168380863853 321962383594188142823945)
        ·
          refine ⟨241471787695641107117959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321962383594188142823945 241471787695641107117959)
          ·
            refine ⟨362207681543461660676939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241471787695641107117959 362207681543461660676939)
            ·
              refine ⟨543311522315192491015409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362207681543461660676939 543311522315192491015409)
              ·
                refine ⟨407483641736394368261557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543311522315192491015409 407483641736394368261557)
                ·
                  refine ⟨38201591412786972024521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 407483641736394368261557 38201591412786972024521)
                  ·
                    rfl

theorem cell22_334788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_334788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334788 prefixEnd_334788 := by exact prefixLift 334788
  have htrace : WordTrace (prefixWord ++ tailWord_334788) baseStart_334788 baseEnd_334788 := by
    simpa [prefixWord, tailWord_334788, baseEnd_334788] using wordTrace_append hprefix tailTrace_334788
  have hstable : (prefixWord ++ tailWord_334788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334788).length < 2 ^ (prefixWord ++ tailWord_334788).sum := by decide
  have hdescent : baseEnd_334788 < baseStart_334788 := by decide
  rcases family_descends (prefixWord ++ tailWord_334788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334840 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 1, 8]
def baseStart_334840 : Nat := 118140960795 + 334840 * 2 ^ 59
def prefixEnd_334840 : Nat := 4983230072969 + 3 ^ 40 * 334840 * 2
def baseEnd_334840 : Nat := 114622574901050113773403

theorem tailTrace_334840 : CollatzResearch.WordTrace tailWord_334840 prefixEnd_334840 114622574901050113773403 := by
  unfold tailWord_334840
  simp only [CollatzResearch.WordTrace]
  refine ⟨6106309053469670482144987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8141745404626227309526649 6106309053469670482144987)
  ·
    refine ⟨9159463580204505723217481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6106309053469670482144987 9159463580204505723217481)
    ·
      refine ⟨6869597685153379292413111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9159463580204505723217481 6869597685153379292413111)
      ·
        refine ⟨10304396527730068938619667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6869597685153379292413111 10304396527730068938619667)
        ·
          refine ⟨15456594791595103407929501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10304396527730068938619667 15456594791595103407929501)
          ·
            refine ⟨5796223046848163777973563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15456594791595103407929501 5796223046848163777973563)
            ·
              refine ⟨8694334570272245666960345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5796223046848163777973563 8694334570272245666960345)
              ·
                refine ⟨6520750927704184250220259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8694334570272245666960345 6520750927704184250220259)
                ·
                  refine ⟨9781126391556276375330389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6520750927704184250220259 9781126391556276375330389)
                  ·
                    refine ⟨114622574901050113773403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9781126391556276375330389 114622574901050113773403)
                    ·
                      rfl

theorem cell22_334840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_334840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334840 prefixEnd_334840 := by exact prefixLift 334840
  have htrace : WordTrace (prefixWord ++ tailWord_334840) baseStart_334840 baseEnd_334840 := by
    simpa [prefixWord, tailWord_334840, baseEnd_334840] using wordTrace_append hprefix tailTrace_334840
  have hstable : (prefixWord ++ tailWord_334840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334840).length < 2 ^ (prefixWord ++ tailWord_334840).sum := by decide
  have hdescent : baseEnd_334840 < baseStart_334840 := by decide
  rcases family_descends (prefixWord ++ tailWord_334840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334842 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 5, 3]
def baseStart_334842 : Nat := 118140960795 + 334842 * 2 ^ 59
def prefixEnd_334842 : Nat := 4983230072969 + 3 ^ 40 * 334842 * 2
def baseEnd_334842 : Nat := 114623259541922775223397

theorem tailTrace_334842 : CollatzResearch.WordTrace tailWord_334842 prefixEnd_334842 114623259541922775223397 := by
  unfold tailWord_334842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3053172763233023826465695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8141794035288063537241853 3053172763233023826465695)
  ·
    refine ⟨4579759144849535739698543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3053172763233023826465695 4579759144849535739698543)
    ·
      refine ⟨6869638717274303609547815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4579759144849535739698543 6869638717274303609547815)
      ·
        refine ⟨10304458075911455414321723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6869638717274303609547815 10304458075911455414321723)
        ·
          refine ⟨15456687113867183121482585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10304458075911455414321723 15456687113867183121482585)
          ·
            refine ⟨11592515335400387341111939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15456687113867183121482585 11592515335400387341111939)
            ·
              refine ⟨17388773003100581011667909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11592515335400387341111939 17388773003100581011667909)
              ·
                refine ⟨3260394938081358939687733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17388773003100581011667909 3260394938081358939687733)
                ·
                  refine ⟨305662025445127400595725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3260394938081358939687733 305662025445127400595725)
                  ·
                    refine ⟨114623259541922775223397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305662025445127400595725 114623259541922775223397)
                    ·
                      rfl

theorem cell22_334842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_334842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334842 prefixEnd_334842 := by exact prefixLift 334842
  have htrace : WordTrace (prefixWord ++ tailWord_334842) baseStart_334842 baseEnd_334842 := by
    simpa [prefixWord, tailWord_334842, baseEnd_334842] using wordTrace_append hprefix tailTrace_334842
  have hstable : (prefixWord ++ tailWord_334842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334842).length < 2 ^ (prefixWord ++ tailWord_334842).sum := by decide
  have hdescent : baseEnd_334842 < baseStart_334842 := by decide
  rcases family_descends (prefixWord ++ tailWord_334842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334846 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_334846 : Nat := 118140960795 + 334846 * 2 ^ 59
def prefixEnd_334846 : Nat := 4983230072969 + 3 ^ 40 * 334846 * 2
def baseEnd_334846 : Nat := 114624628823668098123385

theorem tailTrace_334846 : CollatzResearch.WordTrace tailWord_334846 prefixEnd_334846 114624628823668098123385 := by
  unfold tailWord_334846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526604618114700498626049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8141891296611735992672261 1526604618114700498626049)
  ·
    refine ⟨1144953463586025373969537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1526604618114700498626049 1144953463586025373969537)
    ·
      refine ⟨858715097689519030477153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1144953463586025373969537 858715097689519030477153)
      ·
        refine ⟨644036323267139272857865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 858715097689519030477153 644036323267139272857865)
        ·
          refine ⟨483027242450354454643399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 644036323267139272857865 483027242450354454643399)
          ·
            refine ⟨724540863675531681965099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483027242450354454643399 724540863675531681965099)
            ·
              refine ⟨1086811295513297522947649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 724540863675531681965099 1086811295513297522947649)
              ·
                refine ⟨815108471634973142210737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086811295513297522947649 815108471634973142210737)
                ·
                  refine ⟨611331353726229856658053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 815108471634973142210737 611331353726229856658053)
                  ·
                    refine ⟨114624628823668098123385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 611331353726229856658053 114624628823668098123385)
                    ·
                      rfl

theorem cell22_334846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_334846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334846 prefixEnd_334846 := by exact prefixLift 334846
  have htrace : WordTrace (prefixWord ++ tailWord_334846) baseStart_334846 baseEnd_334846 := by
    simpa [prefixWord, tailWord_334846, baseEnd_334846] using wordTrace_append hprefix tailTrace_334846
  have hstable : (prefixWord ++ tailWord_334846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334846).length < 2 ^ (prefixWord ++ tailWord_334846).sum := by decide
  have hdescent : baseEnd_334846 < baseStart_334846 := by decide
  rcases family_descends (prefixWord ++ tailWord_334846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334850 : List Nat := [3, 4, 1, 3, 1, 1, 3, 2, 4]
def baseStart_334850 : Nat := 118140960795 + 334850 * 2 ^ 59
def prefixEnd_334850 : Nat := 4983230072969 + 3 ^ 40 * 334850 * 2
def baseEnd_334850 : Nat := 38208666035137807007791

theorem tailTrace_334850 : CollatzResearch.WordTrace tailWord_334850 prefixEnd_334850 38208666035137807007791 := by
  unfold tailWord_334850
  simp only [CollatzResearch.WordTrace]
  refine ⟨3053245709225778168038501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8141988557935408448102669 3053245709225778168038501)
  ·
    refine ⟨572483570479833406507219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3053245709225778168038501 572483570479833406507219)
    ·
      refine ⟨858725355719750109760829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 572483570479833406507219 858725355719750109760829)
      ·
        refine ⟨322022008394906291160311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 858725355719750109760829 322022008394906291160311)
        ·
          refine ⟨483033012592359436740467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322022008394906291160311 483033012592359436740467)
          ·
            refine ⟨724549518888539155110701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483033012592359436740467 724549518888539155110701)
            ·
              refine ⟨271706069583202183166513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 724549518888539155110701 271706069583202183166513)
              ·
                refine ⟨203779552187401637374885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271706069583202183166513 203779552187401637374885)
                ·
                  refine ⟨38208666035137807007791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203779552187401637374885 38208666035137807007791)
                  ·
                    rfl

theorem cell22_334850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_334850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334850 prefixEnd_334850 := by exact prefixLift 334850
  have htrace : WordTrace (prefixWord ++ tailWord_334850) baseStart_334850 baseEnd_334850 := by
    simpa [prefixWord, tailWord_334850, baseEnd_334850] using wordTrace_append hprefix tailTrace_334850
  have hstable : (prefixWord ++ tailWord_334850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334850).length < 2 ^ (prefixWord ++ tailWord_334850).sum := by decide
  have hdescent : baseEnd_334850 < baseStart_334850 := by decide
  rcases family_descends (prefixWord ++ tailWord_334850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334859 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 3, 3]
def baseStart_334859 : Nat := 118140960795 + 334859 * 2 ^ 59
def prefixEnd_334859 : Nat := 4983230072969 + 3 ^ 40 * 334859 * 2
def baseEnd_334859 : Nat := 114629078989340397548345

theorem tailTrace_334859 : CollatzResearch.WordTrace tailWord_334859 prefixEnd_334859 114629078989340397548345 := by
  unfold tailWord_334859
  simp only [CollatzResearch.WordTrace]
  refine ⟨12213311093870507209231631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8142207395913671472821087 12213311093870507209231631)
  ·
    refine ⟨18319966640805760813847447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12213311093870507209231631 18319966640805760813847447)
    ·
      refine ⟨27479949961208641220771171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18319966640805760813847447 27479949961208641220771171)
      ·
        refine ⟨41219924941812961831156757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27479949961208641220771171 41219924941812961831156757)
        ·
          refine ⟨1932183981647482585835473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41219924941812961831156757 1932183981647482585835473)
          ·
            refine ⟨1449137986235611939376605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1932183981647482585835473 1449137986235611939376605)
            ·
              refine ⟨543426744838354477266227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1449137986235611939376605 543426744838354477266227)
              ·
                refine ⟨815140117257531715899341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543426744838354477266227 815140117257531715899341)
                ·
                  refine ⟨305677543971574393462253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815140117257531715899341 305677543971574393462253)
                  ·
                    refine ⟨114629078989340397548345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305677543971574393462253 114629078989340397548345)
                    ·
                      rfl

theorem cell22_334859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 3].length) (baseStart_334859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334859 prefixEnd_334859 := by exact prefixLift 334859
  have htrace : WordTrace (prefixWord ++ tailWord_334859) baseStart_334859 baseEnd_334859 := by
    simpa [prefixWord, tailWord_334859, baseEnd_334859] using wordTrace_append hprefix tailTrace_334859
  have hstable : (prefixWord ++ tailWord_334859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334859).length < 2 ^ (prefixWord ++ tailWord_334859).sum := by decide
  have hdescent : baseEnd_334859 < baseStart_334859 := by decide
  rcases family_descends (prefixWord ++ tailWord_334859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334910 : List Nat := [4, 2, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_334910 : Nat := 118140960795 + 334910 * 2 ^ 59
def prefixEnd_334910 : Nat := 4983230072969 + 3 ^ 40 * 334910 * 2
def baseEnd_334910 : Nat := 114646537331593264523189

theorem tailTrace_334910 : CollatzResearch.WordTrace tailWord_334910 prefixEnd_334910 114646537331593264523189 := by
  unfold tailWord_334910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526896402085717864917273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8143447477790495279558789 1526896402085717864917273)
  ·
    refine ⟨1145172301564288398687955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1526896402085717864917273 1145172301564288398687955)
    ·
      refine ⟨1717758452346432598031933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1145172301564288398687955 1717758452346432598031933)
      ·
        refine ⟨644159419629912224261975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1717758452346432598031933 644159419629912224261975)
        ·
          refine ⟨966239129444868336392963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644159419629912224261975 966239129444868336392963)
          ·
            refine ⟨1449358694167302504589445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966239129444868336392963 1449358694167302504589445)
            ·
              refine ⟨271754755156369219610521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1449358694167302504589445 271754755156369219610521)
              ·
                refine ⟨203816066367276914707891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271754755156369219610521 203816066367276914707891)
                ·
                  refine ⟨305724099550915372061837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203816066367276914707891 305724099550915372061837)
                  ·
                    refine ⟨114646537331593264523189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305724099550915372061837 114646537331593264523189)
                    ·
                      rfl

theorem cell22_334910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_334910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334910 prefixEnd_334910 := by exact prefixLift 334910
  have htrace : WordTrace (prefixWord ++ tailWord_334910) baseStart_334910 baseEnd_334910 := by
    simpa [prefixWord, tailWord_334910, baseEnd_334910] using wordTrace_append hprefix tailTrace_334910
  have hstable : (prefixWord ++ tailWord_334910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334910).length < 2 ^ (prefixWord ++ tailWord_334910).sum := by decide
  have hdescent : baseEnd_334910 < baseStart_334910 := by decide
  rcases family_descends (prefixWord ++ tailWord_334910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334949 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 4, 3]
def baseStart_334949 : Nat := 118140960795 + 334949 * 2 ^ 59
def prefixEnd_334949 : Nat := 4983230072969 + 3 ^ 40 * 334949 * 2
def baseEnd_334949 : Nat := 114659887828610162798069

theorem tailTrace_334949 : CollatzResearch.WordTrace tailWord_334949 prefixEnd_334949 114659887828610162798069 := by
  unfold tailWord_334949
  simp only [CollatzResearch.WordTrace]
  refine ⟨12216593663544452580007901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8144395775696301720005267 12216593663544452580007901)
  ·
    refine ⟨4581222623829169717502963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12216593663544452580007901 4581222623829169717502963)
    ·
      refine ⟨6871833935743754576254445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4581222623829169717502963 6871833935743754576254445)
      ·
        refine ⟨2576937725903907966095417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6871833935743754576254445 2576937725903907966095417)
        ·
          refine ⟨1932703294427930974571563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2576937725903907966095417 1932703294427930974571563)
          ·
            refine ⟨2899054941641896461857345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932703294427930974571563 2899054941641896461857345)
            ·
              refine ⟨2174291206231422346393009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2899054941641896461857345 2174291206231422346393009)
              ·
                refine ⟨1630718404673566759794757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2174291206231422346393009 1630718404673566759794757)
                ·
                  refine ⟨305759700876293767461517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1630718404673566759794757 305759700876293767461517)
                  ·
                    refine ⟨114659887828610162798069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305759700876293767461517 114659887828610162798069)
                    ·
                      rfl

theorem cell22_334949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_334949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334949 prefixEnd_334949 := by exact prefixLift 334949
  have htrace : WordTrace (prefixWord ++ tailWord_334949) baseStart_334949 baseEnd_334949 := by
    simpa [prefixWord, tailWord_334949, baseEnd_334949] using wordTrace_append hprefix tailTrace_334949
  have hstable : (prefixWord ++ tailWord_334949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334949).length < 2 ^ (prefixWord ++ tailWord_334949).sum := by decide
  have hdescent : baseEnd_334949 < baseStart_334949 := by decide
  rcases family_descends (prefixWord ++ tailWord_334949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334951 : List Nat := [1, 1, 5, 1, 1, 4, 2, 3, 4]
def baseStart_334951 : Nat := 118140960795 + 334951 * 2 ^ 59
def prefixEnd_334951 : Nat := 4983230072969 + 3 ^ 40 * 334951 * 2
def baseEnd_334951 : Nat := 38220190823160941416021

theorem tailTrace_334951 : CollatzResearch.WordTrace tailWord_334951 prefixEnd_334951 38220190823160941416021 := by
  unfold tailWord_334951
  simp only [CollatzResearch.WordTrace]
  refine ⟨12216666609537206921580707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8144444406358137947720471 12216666609537206921580707)
  ·
    refine ⟨18324999914305810382371061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12216666609537206921580707 18324999914305810382371061)
    ·
      refine ⟨1717968741966169723347287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18324999914305810382371061 1717968741966169723347287)
      ·
        refine ⟨2576953112949254585020931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1717968741966169723347287 2576953112949254585020931)
        ·
          refine ⟨3865429669423881877531397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2576953112949254585020931 3865429669423881877531397)
          ·
            refine ⟨724768063016977852037137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3865429669423881877531397 724768063016977852037137)
            ·
              refine ⟨543576047262733389027853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724768063016977852037137 543576047262733389027853)
              ·
                refine ⟨203841017723525020885445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 543576047262733389027853 203841017723525020885445)
                ·
                  refine ⟨38220190823160941416021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203841017723525020885445 38220190823160941416021)
                  ·
                    rfl

theorem cell22_334951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 4].length) (baseStart_334951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334951 prefixEnd_334951 := by exact prefixLift 334951
  have htrace : WordTrace (prefixWord ++ tailWord_334951) baseStart_334951 baseEnd_334951 := by
    simpa [prefixWord, tailWord_334951, baseEnd_334951] using wordTrace_append hprefix tailTrace_334951
  have hstable : (prefixWord ++ tailWord_334951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334951).length < 2 ^ (prefixWord ++ tailWord_334951).sum := by decide
  have hdescent : baseEnd_334951 < baseStart_334951 := by decide
  rcases family_descends (prefixWord ++ tailWord_334951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334962 : List Nat := [3, 2, 1, 2, 2, 1, 11]
def baseStart_334962 : Nat := 118140960795 + 334962 * 2 ^ 59
def prefixEnd_334962 : Nat := 4983230072969 + 3 ^ 40 * 334962 * 2
def baseEnd_334962 : Nat := 4246827333121572674927

theorem tailTrace_334962 : CollatzResearch.WordTrace tailWord_334962 prefixEnd_334962 4246827333121572674927 := by
  unfold tailWord_334962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3054266953124338950057785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8144711874998237200154093 3054266953124338950057785)
  ·
    refine ⟨2290700214843254212543339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3054266953124338950057785 2290700214843254212543339)
    ·
      refine ⟨3436050322264881318815009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2290700214843254212543339 3436050322264881318815009)
      ·
        refine ⟨2577037741698660989111257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3436050322264881318815009 2577037741698660989111257)
        ·
          refine ⟨1932778306273995741833443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2577037741698660989111257 1932778306273995741833443)
          ·
            refine ⟨2899167459410993612750165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932778306273995741833443 2899167459410993612750165)
            ·
              refine ⟨4246827333121572674927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2899167459410993612750165 4246827333121572674927)
              ·
                rfl

theorem cell22_334962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 11].length) (baseStart_334962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334962 prefixEnd_334962 := by exact prefixLift 334962
  have htrace : WordTrace (prefixWord ++ tailWord_334962) baseStart_334962 baseEnd_334962 := by
    simpa [prefixWord, tailWord_334962, baseEnd_334962] using wordTrace_append hprefix tailTrace_334962
  have hstable : (prefixWord ++ tailWord_334962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334962).length < 2 ^ (prefixWord ++ tailWord_334962).sum := by decide
  have hdescent : baseEnd_334962 < baseStart_334962 := by decide
  rcases family_descends (prefixWord ++ tailWord_334962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334966 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_334966 : Nat := 118140960795 + 334966 * 2 ^ 59
def prefixEnd_334966 : Nat := 4983230072969 + 3 ^ 40 * 334966 * 2
def baseEnd_334966 : Nat := 114665707276027785123017

theorem tailTrace_334966 : CollatzResearch.WordTrace tailWord_334966 prefixEnd_334966 114665707276027785123017 := by
  unfold tailWord_334966
  simp only [CollatzResearch.WordTrace]
  refine ⟨763575856530179030211047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8144809136321909655584501 763575856530179030211047)
  ·
    refine ⟨1145363784795268545316571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 763575856530179030211047 1145363784795268545316571)
    ·
      refine ⟨1718045677192902817974857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1145363784795268545316571 1718045677192902817974857)
      ·
        refine ⟨1288534257894677113481143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1718045677192902817974857 1288534257894677113481143)
        ·
          refine ⟨1932801386842015670221715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1288534257894677113481143 1932801386842015670221715)
          ·
            refine ⟨2899202080263023505332573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932801386842015670221715 2899202080263023505332573)
            ·
              refine ⟨1087200780098633814499715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2899202080263023505332573 1087200780098633814499715)
              ·
                refine ⟨1630801170147950721749573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087200780098633814499715 1630801170147950721749573)
                ·
                  refine ⟨305775219402740760328045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1630801170147950721749573 305775219402740760328045)
                  ·
                    refine ⟨114665707276027785123017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305775219402740760328045 114665707276027785123017)
                    ·
                      rfl

theorem cell22_334966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_334966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_334966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_334966 prefixEnd_334966 := by exact prefixLift 334966
  have htrace : WordTrace (prefixWord ++ tailWord_334966) baseStart_334966 baseEnd_334966 := by
    simpa [prefixWord, tailWord_334966, baseEnd_334966] using wordTrace_append hprefix tailTrace_334966
  have hstable : (prefixWord ++ tailWord_334966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334966).length < 2 ^ (prefixWord ++ tailWord_334966).sum := by decide
  have hdescent : baseEnd_334966 < baseStart_334966 := by decide
  rcases family_descends (prefixWord ++ tailWord_334966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335067 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 2, 9]
def baseStart_335067 : Nat := 118140960795 + 335067 * 2 ^ 59
def prefixEnd_335067 : Nat := 4983230072969 + 3 ^ 40 * 335067 * 2
def baseEnd_335067 : Nat := 114700281640097188347707

theorem tailTrace_335067 : CollatzResearch.WordTrace tailWord_335067 prefixEnd_335067 114700281640097188347707 := by
  unfold tailWord_335067
  simp only [CollatzResearch.WordTrace]
  refine ⟨12220897477116958732803455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8147264984744639155202303 12220897477116958732803455)
  ·
    refine ⟨18331346215675438099205183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12220897477116958732803455 18331346215675438099205183)
    ·
      refine ⟨27497019323513157148807775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18331346215675438099205183 27497019323513157148807775)
      ·
        refine ⟨41245528985269735723211663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27497019323513157148807775 41245528985269735723211663)
        ·
          refine ⟨61868293477904603584817495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41245528985269735723211663 61868293477904603584817495)
          ·
            refine ⟨92802440216856905377226243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61868293477904603584817495 92802440216856905377226243)
            ·
              refine ⟨139203660325285358065839365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92802440216856905377226243 139203660325285358065839365)
              ·
                refine ⟨26100686310991004637344881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139203660325285358065839365 26100686310991004637344881)
                ·
                  refine ⟨19575514733243253478008661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26100686310991004637344881 19575514733243253478008661)
                  ·
                    refine ⟨114700281640097188347707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 19575514733243253478008661 114700281640097188347707)
                    ·
                      rfl

theorem cell22_335067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_335067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335067 prefixEnd_335067 := by exact prefixLift 335067
  have htrace : WordTrace (prefixWord ++ tailWord_335067) baseStart_335067 baseEnd_335067 := by
    simpa [prefixWord, tailWord_335067, baseEnd_335067] using wordTrace_append hprefix tailTrace_335067
  have hstable : (prefixWord ++ tailWord_335067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335067).length < 2 ^ (prefixWord ++ tailWord_335067).sum := by decide
  have hdescent : baseEnd_335067 < baseStart_335067 := by decide
  rcases family_descends (prefixWord ++ tailWord_335067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335079 : List Nat := [1, 1, 5, 3, 3, 1, 2, 2, 1, 3]
def baseStart_335079 : Nat := 118140960795 + 335079 * 2 ^ 59
def prefixEnd_335079 : Nat := 4983230072969 + 3 ^ 40 * 335079 * 2
def baseEnd_335079 : Nat := 114704389485333157047671

theorem tailTrace_335079 : CollatzResearch.WordTrace tailWord_335079 prefixEnd_335079 114704389485333157047671 := by
  unfold tailWord_335079
  simp only [CollatzResearch.WordTrace]
  refine ⟨12221335153073484782240291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8147556768715656521493527 12221335153073484782240291)
  ·
    refine ⟨18332002729610227173360437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12221335153073484782240291 18332002729610227173360437)
    ·
      refine ⟨1718625255900958797502541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18332002729610227173360437 1718625255900958797502541)
      ·
        refine ⟨644484470962859549063453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1718625255900958797502541 644484470962859549063453)
        ·
          refine ⟨241681676611072330898795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 644484470962859549063453 241681676611072330898795)
          ·
            refine ⟨362522514916608496348193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241681676611072330898795 362522514916608496348193)
            ·
              refine ⟨271891886187456372261145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362522514916608496348193 271891886187456372261145)
              ·
                refine ⟨203918914640592279195859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271891886187456372261145 203918914640592279195859)
                ·
                  refine ⟨305878371960888418793789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203918914640592279195859 305878371960888418793789)
                  ·
                    refine ⟨114704389485333157047671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305878371960888418793789 114704389485333157047671)
                    ·
                      rfl

theorem cell22_335079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_335079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335079 prefixEnd_335079 := by exact prefixLift 335079
  have htrace : WordTrace (prefixWord ++ tailWord_335079) baseStart_335079 baseEnd_335079 := by
    simpa [prefixWord, tailWord_335079, baseEnd_335079] using wordTrace_append hprefix tailTrace_335079
  have hstable : (prefixWord ++ tailWord_335079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335079).length < 2 ^ (prefixWord ++ tailWord_335079).sum := by decide
  have hdescent : baseEnd_335079 < baseStart_335079 := by decide
  rcases family_descends (prefixWord ++ tailWord_335079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335116 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_335116 : Nat := 118140960795 + 335116 * 2 ^ 59
def prefixEnd_335116 : Nat := 4983230072969 + 3 ^ 40 * 335116 * 2
def baseEnd_335116 : Nat := 114717055341477393872557

theorem tailTrace_335116 : CollatzResearch.WordTrace tailWord_335116 prefixEnd_335116 114717055341477393872557 := by
  unfold tailWord_335116
  simp only [CollatzResearch.WordTrace]
  refine ⟨6111342326969720050668601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8148456435959626734224801 6111342326969720050668601)
  ·
    refine ⟨4583506745227290038001451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6111342326969720050668601 4583506745227290038001451)
    ·
      refine ⟨6875260117840935057002177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4583506745227290038001451 6875260117840935057002177)
      ·
        refine ⟨5156445088380701292751633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6875260117840935057002177 5156445088380701292751633)
        ·
          refine ⟨3867333816285525969563725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5156445088380701292751633 3867333816285525969563725)
          ·
            refine ⟨1450250181107072238586397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3867333816285525969563725 1450250181107072238586397)
            ·
              refine ⟨543843817915152089469899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1450250181107072238586397 543843817915152089469899)
              ·
                refine ⟨815765726872728134204849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543843817915152089469899 815765726872728134204849)
                ·
                  refine ⟨611824295154546100653637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 815765726872728134204849 611824295154546100653637)
                  ·
                    refine ⟨114717055341477393872557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 611824295154546100653637 114717055341477393872557)
                    ·
                      rfl

theorem cell22_335116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_335116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335116 prefixEnd_335116 := by exact prefixLift 335116
  have htrace : WordTrace (prefixWord ++ tailWord_335116) baseStart_335116 baseEnd_335116 := by
    simpa [prefixWord, tailWord_335116, baseEnd_335116] using wordTrace_append hprefix tailTrace_335116
  have hstable : (prefixWord ++ tailWord_335116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335116).length < 2 ^ (prefixWord ++ tailWord_335116).sum := by decide
  have hdescent : baseEnd_335116 < baseStart_335116 := by decide
  rcases family_descends (prefixWord ++ tailWord_335116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335135 : List Nat := [1, 1, 2, 4, 4, 2, 1, 2, 2, 3]
def baseStart_335135 : Nat := 118140960795 + 335135 * 2 ^ 59
def prefixEnd_335135 : Nat := 4983230072969 + 3 ^ 40 * 335135 * 2
def baseEnd_335135 : Nat := 114723559429767677647499

theorem tailTrace_335135 : CollatzResearch.WordTrace tailWord_335135 prefixEnd_335135 114723559429767677647499 := by
  unfold tailWord_335135
  simp only [CollatzResearch.WordTrace]
  refine ⟨12223377640870606346278859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8148918427247070897519239 12223377640870606346278859)
  ·
    refine ⟨18335066461305909519418289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12223377640870606346278859 18335066461305909519418289)
    ·
      refine ⟨13751299845979432139563717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18335066461305909519418289 13751299845979432139563717)
      ·
        refine ⟨2578368721121143526168197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13751299845979432139563717 2578368721121143526168197)
        ·
          refine ⟨483444135210214411156537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2578368721121143526168197 483444135210214411156537)
          ·
            refine ⟨362583101407660808367403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483444135210214411156537 362583101407660808367403)
            ·
              refine ⟨543874652111491212551105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362583101407660808367403 543874652111491212551105)
              ·
                refine ⟨407905989083618409413329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543874652111491212551105 407905989083618409413329)
                ·
                  refine ⟨305929491812713807059997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407905989083618409413329 305929491812713807059997)
                  ·
                    refine ⟨114723559429767677647499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305929491812713807059997 114723559429767677647499)
                    ·
                      rfl

theorem cell22_335135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 3].length) (baseStart_335135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335135 prefixEnd_335135 := by exact prefixLift 335135
  have htrace : WordTrace (prefixWord ++ tailWord_335135) baseStart_335135 baseEnd_335135 := by
    simpa [prefixWord, tailWord_335135, baseEnd_335135] using wordTrace_append hprefix tailTrace_335135
  have hstable : (prefixWord ++ tailWord_335135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335135).length < 2 ^ (prefixWord ++ tailWord_335135).sum := by decide
  have hdescent : baseEnd_335135 < baseStart_335135 := by decide
  rcases family_descends (prefixWord ++ tailWord_335135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335165 : List Nat := [1, 4, 1, 5, 1, 2, 2, 6]
def baseStart_335165 : Nat := 118140960795 + 335165 * 2 ^ 59
def prefixEnd_335165 : Nat := 4983230072969 + 3 ^ 40 * 335165 * 2
def baseEnd_335165 : Nat := 12748203226984177710823

theorem tailTrace_335165 : CollatzResearch.WordTrace tailWord_335165 prefixEnd_335165 12748203226984177710823 := by
  unfold tailWord_335165
  simp only [CollatzResearch.WordTrace]
  refine ⟨12224471830761921469870949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8149647887174614313247299 12224471830761921469870949)
  ·
    refine ⟨2292088468267860275600803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12224471830761921469870949 2292088468267860275600803)
    ·
      refine ⟨3438132702401790413401205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2292088468267860275600803 3438132702401790413401205)
      ·
        refine ⟨322324940850167851256363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3438132702401790413401205 322324940850167851256363)
        ·
          refine ⟨483487411275251776884545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322324940850167851256363 483487411275251776884545)
          ·
            refine ⟨362615558456438832663409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483487411275251776884545 362615558456438832663409)
            ·
              refine ⟨271961668842329124497557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362615558456438832663409 271961668842329124497557)
              ·
                refine ⟨12748203226984177710823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 271961668842329124497557 12748203226984177710823)
                ·
                  rfl

theorem cell22_335165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 6].length) (baseStart_335165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335165 prefixEnd_335165 := by exact prefixLift 335165
  have htrace : WordTrace (prefixWord ++ tailWord_335165) baseStart_335165 baseEnd_335165 := by
    simpa [prefixWord, tailWord_335165, baseEnd_335165] using wordTrace_append hprefix tailTrace_335165
  have hstable : (prefixWord ++ tailWord_335165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335165).length < 2 ^ (prefixWord ++ tailWord_335165).sum := by decide
  have hdescent : baseEnd_335165 < baseStart_335165 := by decide
  rcases family_descends (prefixWord ++ tailWord_335165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335180 : List Nat := [2, 2, 1, 3, 2, 2, 3, 3, 1, 3]
def baseStart_335180 : Nat := 118140960795 + 335180 * 2 ^ 59
def prefixEnd_335180 : Nat := 4983230072969 + 3 ^ 40 * 335180 * 2
def baseEnd_335180 : Nat := 114738963849402560272361

theorem tailTrace_335180 : CollatzResearch.WordTrace tailWord_335180 prefixEnd_335180 114738963849402560272361 := by
  unfold tailWord_335180
  simp only [CollatzResearch.WordTrace]
  refine ⟨6112509462853789515833497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8150012617138386021111329 6112509462853789515833497)
  ·
    refine ⟨4584382097140342136875123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6112509462853789515833497 4584382097140342136875123)
    ·
      refine ⟨6876573145710513205312685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4584382097140342136875123 6876573145710513205312685)
      ·
        refine ⟨2578714929641442451992257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6876573145710513205312685 2578714929641442451992257)
        ·
          refine ⟨1934036197231081838994193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2578714929641442451992257 1934036197231081838994193)
          ·
            refine ⟨1450527147923311379245645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1934036197231081838994193 1450527147923311379245645)
            ·
              refine ⟨543947680471241767217117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1450527147923311379245645 543947680471241767217117)
              ·
                refine ⟨203980380176715662706419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 543947680471241767217117 203980380176715662706419)
                ·
                  refine ⟨305970570265073494059629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203980380176715662706419 305970570265073494059629)
                  ·
                    refine ⟨114738963849402560272361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305970570265073494059629 114738963849402560272361)
                    ·
                      rfl

theorem cell22_335180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_335180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335180 prefixEnd_335180 := by exact prefixLift 335180
  have htrace : WordTrace (prefixWord ++ tailWord_335180) baseStart_335180 baseEnd_335180 := by
    simpa [prefixWord, tailWord_335180, baseEnd_335180] using wordTrace_append hprefix tailTrace_335180
  have hstable : (prefixWord ++ tailWord_335180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335180).length < 2 ^ (prefixWord ++ tailWord_335180).sum := by decide
  have hdescent : baseEnd_335180 < baseStart_335180 := by decide
  rcases family_descends (prefixWord ++ tailWord_335180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335236 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_335236 : Nat := 118140960795 + 335236 * 2 ^ 59
def prefixEnd_335236 : Nat := 4983230072969 + 3 ^ 40 * 335236 * 2
def baseEnd_335236 : Nat := 114758133793837080872189

theorem tailTrace_335236 : CollatzResearch.WordTrace tailWord_335236 prefixEnd_335236 114758133793837080872189 := by
  unfold tailWord_335236
  simp only [CollatzResearch.WordTrace]
  refine ⟨6113530706752350297852781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8151374275669800397137041 6113530706752350297852781)
  ·
    refine ⟨2292574015032131361694793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6113530706752350297852781 2292574015032131361694793)
    ·
      refine ⟨1719430511274098521271095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2292574015032131361694793 1719430511274098521271095)
      ·
        refine ⟨2579145766911147781906643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1719430511274098521271095 2579145766911147781906643)
        ·
          refine ⟨3868718650366721672859965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2579145766911147781906643 3868718650366721672859965)
          ·
            refine ⟨1450769493887520627322487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3868718650366721672859965 1450769493887520627322487)
            ·
              refine ⟨2176154240831280940983731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1450769493887520627322487 2176154240831280940983731)
              ·
                refine ⟨3264231361246921411475597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2176154240831280940983731 3264231361246921411475597)
                ·
                  refine ⟨1224086760467595529303349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3264231361246921411475597 1224086760467595529303349)
                  ·
                    refine ⟨114758133793837080872189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1224086760467595529303349 114758133793837080872189)
                    ·
                      rfl

theorem cell22_335236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_335236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335236 prefixEnd_335236 := by exact prefixLift 335236
  have htrace : WordTrace (prefixWord ++ tailWord_335236) baseStart_335236 baseEnd_335236 := by
    simpa [prefixWord, tailWord_335236, baseEnd_335236] using wordTrace_append hprefix tailTrace_335236
  have hstable : (prefixWord ++ tailWord_335236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335236).length < 2 ^ (prefixWord ++ tailWord_335236).sum := by decide
  have hdescent : baseEnd_335236 < baseStart_335236 := by decide
  rcases family_descends (prefixWord ++ tailWord_335236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335240 : List Nat := [2, 1, 3, 3, 1, 3, 3, 1, 1, 4]
def baseStart_335240 : Nat := 118140960795 + 335240 * 2 ^ 59
def prefixEnd_335240 : Nat := 4983230072969 + 3 ^ 40 * 335240 * 2
def baseEnd_335240 : Nat := 114759503075582403772177

theorem tailTrace_335240 : CollatzResearch.WordTrace tailWord_335240 prefixEnd_335240 114759503075582403772177 := by
  unfold tailWord_335240
  simp only [CollatzResearch.WordTrace]
  refine ⟨6113603652745104639425587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8151471536993472852567449 6113603652745104639425587)
  ·
    refine ⟨9170405479117656959138381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6113603652745104639425587 9170405479117656959138381)
    ·
      refine ⟨3438902054669121359676893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9170405479117656959138381 3438902054669121359676893)
      ·
        refine ⟨1289588270500920509878835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3438902054669121359676893 1289588270500920509878835)
        ·
          refine ⟨1934382405751380764818253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289588270500920509878835 1934382405751380764818253)
          ·
            refine ⟨725393402156767786806845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1934382405751380764818253 725393402156767786806845)
            ·
              refine ⟨272022525808787920052567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 725393402156767786806845 272022525808787920052567)
              ·
                refine ⟨408033788713181880078851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272022525808787920052567 408033788713181880078851)
                ·
                  refine ⟨612050683069772820118277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408033788713181880078851 612050683069772820118277)
                  ·
                    refine ⟨114759503075582403772177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 612050683069772820118277 114759503075582403772177)
                    ·
                      rfl

theorem cell22_335240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_335240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335240 prefixEnd_335240 := by exact prefixLift 335240
  have htrace : WordTrace (prefixWord ++ tailWord_335240) baseStart_335240 baseEnd_335240 := by
    simpa [prefixWord, tailWord_335240, baseEnd_335240] using wordTrace_append hprefix tailTrace_335240
  have hstable : (prefixWord ++ tailWord_335240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335240).length < 2 ^ (prefixWord ++ tailWord_335240).sum := by decide
  have hdescent : baseEnd_335240 < baseStart_335240 := by decide
  rcases family_descends (prefixWord ++ tailWord_335240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335253 : List Nat := [1, 3, 2, 1, 1, 2, 3, 4, 2, 3]
def baseStart_335253 : Nat := 118140960795 + 335253 * 2 ^ 59
def prefixEnd_335253 : Nat := 4983230072969 + 3 ^ 40 * 335253 * 2
def baseEnd_335253 : Nat := 114763953241254703197137

theorem tailTrace_335253 : CollatzResearch.WordTrace tailWord_335253 prefixEnd_335253 114763953241254703197137 := by
  unfold tailWord_335253
  simp only [CollatzResearch.WordTrace]
  refine ⟨12227681454443112499074413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8151787636295408332716275 12227681454443112499074413)
  ·
    refine ⟨4585380545416167187152905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12227681454443112499074413 4585380545416167187152905)
    ·
      refine ⟨3439035409062125390364679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4585380545416167187152905 3439035409062125390364679)
      ·
        refine ⟨5158553113593188085547019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3439035409062125390364679 5158553113593188085547019)
        ·
          refine ⟨7737829670389782128320529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5158553113593188085547019 7737829670389782128320529)
          ·
            refine ⟨5803372252792336596240397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7737829670389782128320529 5803372252792336596240397)
            ·
              refine ⟨2176264594797126223590149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5803372252792336596240397 2176264594797126223590149)
              ·
                refine ⟨408049611524461166923153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2176264594797126223590149 408049611524461166923153)
                ·
                  refine ⟨306037208643345875192365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408049611524461166923153 306037208643345875192365)
                  ·
                    refine ⟨114763953241254703197137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306037208643345875192365 114763953241254703197137)
                    ·
                      rfl

theorem cell22_335253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_335253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335253 prefixEnd_335253 := by exact prefixLift 335253
  have htrace : WordTrace (prefixWord ++ tailWord_335253) baseStart_335253 baseEnd_335253 := by
    simpa [prefixWord, tailWord_335253, baseEnd_335253] using wordTrace_append hprefix tailTrace_335253
  have hstable : (prefixWord ++ tailWord_335253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335253).length < 2 ^ (prefixWord ++ tailWord_335253).sum := by decide
  have hdescent : baseEnd_335253 < baseStart_335253 := by decide
  rcases family_descends (prefixWord ++ tailWord_335253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335285 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 2, 4]
def baseStart_335285 : Nat := 118140960795 + 335285 * 2 ^ 59
def prefixEnd_335285 : Nat := 4983230072969 + 3 ^ 40 * 335285 * 2
def baseEnd_335285 : Nat := 114774907495217286397039

theorem tailTrace_335285 : CollatzResearch.WordTrace tailWord_335285 prefixEnd_335285 114774907495217286397039 := by
  unfold tailWord_335285
  simp only [CollatzResearch.WordTrace]
  refine ⟨12228848590327181964239309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8152565726884787976159539 12228848590327181964239309)
  ·
    refine ⟨4585818221372693236589741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12228848590327181964239309 4585818221372693236589741)
    ·
      refine ⟨1719681833014759963721153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4585818221372693236589741 1719681833014759963721153)
      ·
        refine ⟨1289761374761069972790865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1719681833014759963721153 1289761374761069972790865)
        ·
          refine ⟨967321031070802479593149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1289761374761069972790865 967321031070802479593149)
          ·
            refine ⟨362745386651550929847431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 967321031070802479593149 362745386651550929847431)
            ·
              refine ⟨544118079977326394771147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362745386651550929847431 544118079977326394771147)
              ·
                refine ⟨816177119965989592156721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544118079977326394771147 816177119965989592156721)
                ·
                  refine ⟨612132839974492194117541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 816177119965989592156721 612132839974492194117541)
                  ·
                    refine ⟨114774907495217286397039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 612132839974492194117541 114774907495217286397039)
                    ·
                      rfl

theorem cell22_335285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_335285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335285 prefixEnd_335285 := by exact prefixLift 335285
  have htrace : WordTrace (prefixWord ++ tailWord_335285) baseStart_335285 baseEnd_335285 := by
    simpa [prefixWord, tailWord_335285, baseEnd_335285] using wordTrace_append hprefix tailTrace_335285
  have hstable : (prefixWord ++ tailWord_335285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335285).length < 2 ^ (prefixWord ++ tailWord_335285).sum := by decide
  have hdescent : baseEnd_335285 < baseStart_335285 := by decide
  rcases family_descends (prefixWord ++ tailWord_335285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335349 : List Nat := [1, 3, 5, 1, 1, 1, 3, 3, 1, 3]
def baseStart_335349 : Nat := 118140960795 + 335349 * 2 ^ 59
def prefixEnd_335349 : Nat := 4983230072969 + 3 ^ 40 * 335349 * 2
def baseEnd_335349 : Nat := 114796816003142452796843

theorem tailTrace_335349 : CollatzResearch.WordTrace tailWord_335349 prefixEnd_335349 114796816003142452796843 := by
  unfold tailWord_335349
  simp only [CollatzResearch.WordTrace]
  refine ⟨12231182862095320894569101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8154121908063547263046067 12231182862095320894569101)
  ·
    refine ⟨4586693573285745335463413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12231182862095320894569101 4586693573285745335463413)
    ·
      refine ⟨430002522495538625199695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4586693573285745335463413 430002522495538625199695)
      ·
        refine ⟨645003783743307937799543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430002522495538625199695 645003783743307937799543)
        ·
          refine ⟨967505675614961906699315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645003783743307937799543 967505675614961906699315)
          ·
            refine ⟨1451258513422442860048973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967505675614961906699315 1451258513422442860048973)
            ·
              refine ⟨544221942533416072518365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1451258513422442860048973 544221942533416072518365)
              ·
                refine ⟨204083228450031027194387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 544221942533416072518365 204083228450031027194387)
                ·
                  refine ⟨306124842675046540791581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204083228450031027194387 306124842675046540791581)
                  ·
                    refine ⟨114796816003142452796843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306124842675046540791581 114796816003142452796843)
                    ·
                      rfl

theorem cell22_335349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_335349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335349 prefixEnd_335349 := by exact prefixLift 335349
  have htrace : WordTrace (prefixWord ++ tailWord_335349) baseStart_335349 baseEnd_335349 := by
    simpa [prefixWord, tailWord_335349, baseEnd_335349] using wordTrace_append hprefix tailTrace_335349
  have hstable : (prefixWord ++ tailWord_335349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335349).length < 2 ^ (prefixWord ++ tailWord_335349).sum := by decide
  have hdescent : baseEnd_335349 < baseStart_335349 := by decide
  rcases family_descends (prefixWord ++ tailWord_335349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335356 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 8]
def baseStart_335356 : Nat := 118140960795 + 335356 * 2 ^ 59
def prefixEnd_335356 : Nat := 4983230072969 + 3 ^ 40 * 335356 * 2
def baseEnd_335356 : Nat := 38266404082065589290607

theorem tailTrace_335356 : CollatzResearch.WordTrace tailWord_335356 prefixEnd_335356 38266404082065589290607 := by
  unfold tailWord_335356
  simp only [CollatzResearch.WordTrace]
  refine ⟨6115719086534980545036961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8154292115379974060049281 6115719086534980545036961)
  ·
    refine ⟨4586789314901235408777721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6115719086534980545036961 4586789314901235408777721)
    ·
      refine ⟨3440091986175926556583291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4586789314901235408777721 3440091986175926556583291)
      ·
        refine ⟨5160137979263889834874937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3440091986175926556583291 5160137979263889834874937)
        ·
          refine ⟨3870103484447917376156203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5160137979263889834874937 3870103484447917376156203)
          ·
            refine ⟨5805155226671876064234305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3870103484447917376156203 5805155226671876064234305)
            ·
              refine ⟨4353866420003907048175729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5805155226671876064234305 4353866420003907048175729)
              ·
                refine ⟨3265399815002930286131797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4353866420003907048175729 3265399815002930286131797)
                ·
                  refine ⟨38266404082065589290607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3265399815002930286131797 38266404082065589290607)
                  ·
                    rfl

theorem cell22_335356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_335356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335356 prefixEnd_335356 := by exact prefixLift 335356
  have htrace : WordTrace (prefixWord ++ tailWord_335356) baseStart_335356 baseEnd_335356 := by
    simpa [prefixWord, tailWord_335356, baseEnd_335356] using wordTrace_append hprefix tailTrace_335356
  have hstable : (prefixWord ++ tailWord_335356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335356).length < 2 ^ (prefixWord ++ tailWord_335356).sum := by decide
  have hdescent : baseEnd_335356 < baseStart_335356 := by decide
  rcases family_descends (prefixWord ++ tailWord_335356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335388 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_335388 : Nat := 118140960795 + 335388 * 2 ^ 59
def prefixEnd_335388 : Nat := 4983230072969 + 3 ^ 40 * 335388 * 2
def baseEnd_335388 : Nat := 114810166500159351071723

theorem tailTrace_335388 : CollatzResearch.WordTrace tailWord_335388 prefixEnd_335388 114810166500159351071723 := by
  unfold tailWord_335388
  simp only [CollatzResearch.WordTrace]
  refine ⟨6116302654477015277619409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8155070205969353703492545 6116302654477015277619409)
  ·
    refine ⟨4587226990857761458214557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6116302654477015277619409 4587226990857761458214557)
    ·
      refine ⟨1720210121571660546830459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4587226990857761458214557 1720210121571660546830459)
      ·
        refine ⟨2580315182357490820245689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1720210121571660546830459 2580315182357490820245689)
        ·
          refine ⟨1935236386768118115184267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2580315182357490820245689 1935236386768118115184267)
          ·
            refine ⟨2902854580152177172776401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1935236386768118115184267 2902854580152177172776401)
            ·
              refine ⟨2177140935114132879582301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2902854580152177172776401 2177140935114132879582301)
              ·
                refine ⟨816427850667799829843363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2177140935114132879582301 816427850667799829843363)
                ·
                  refine ⟨1224641776001699744765045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 816427850667799829843363 1224641776001699744765045)
                  ·
                    refine ⟨114810166500159351071723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1224641776001699744765045 114810166500159351071723)
                    ·
                      rfl

theorem cell22_335388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_335388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335388 prefixEnd_335388 := by exact prefixLift 335388
  have htrace : WordTrace (prefixWord ++ tailWord_335388) baseStart_335388 baseEnd_335388 := by
    simpa [prefixWord, tailWord_335388, baseEnd_335388] using wordTrace_append hprefix tailTrace_335388
  have hstable : (prefixWord ++ tailWord_335388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335388).length < 2 ^ (prefixWord ++ tailWord_335388).sum := by decide
  have hdescent : baseEnd_335388 < baseStart_335388 := by decide
  rcases family_descends (prefixWord ++ tailWord_335388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335392 : List Nat := [2, 1, 1, 6, 1, 3, 1, 2, 1, 4]
def baseStart_335392 : Nat := 118140960795 + 335392 * 2 ^ 59
def prefixEnd_335392 : Nat := 4983230072969 + 3 ^ 40 * 335392 * 2
def baseEnd_335392 : Nat := 114811535781904673971711

theorem tailTrace_335392 : CollatzResearch.WordTrace tailWord_335392 prefixEnd_335392 114811535781904673971711 := by
  unfold tailWord_335392
  simp only [CollatzResearch.WordTrace]
  refine ⟨6116375600469769619192215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8155167467293026158922953 6116375600469769619192215)
  ·
    refine ⟨9174563400704654428788323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6116375600469769619192215 9174563400704654428788323)
    ·
      refine ⟨13761845101056981643182485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9174563400704654428788323 13761845101056981643182485)
      ·
        refine ⟨645086489112046014524179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13761845101056981643182485 645086489112046014524179)
        ·
          refine ⟨967629733668069021786269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645086489112046014524179 967629733668069021786269)
          ·
            refine ⟨362861150125525883169851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 967629733668069021786269 362861150125525883169851)
            ·
              refine ⟨544291725188288824754777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362861150125525883169851 544291725188288824754777)
              ·
                refine ⟨408218793891216618566083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544291725188288824754777 408218793891216618566083)
                ·
                  refine ⟨612328190836824927849125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408218793891216618566083 612328190836824927849125)
                  ·
                    refine ⟨114811535781904673971711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 612328190836824927849125 114811535781904673971711)
                    ·
                      rfl

theorem cell22_335392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 1, 4].length) (baseStart_335392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335392 prefixEnd_335392 := by exact prefixLift 335392
  have htrace : WordTrace (prefixWord ++ tailWord_335392) baseStart_335392 baseEnd_335392 := by
    simpa [prefixWord, tailWord_335392, baseEnd_335392] using wordTrace_append hprefix tailTrace_335392
  have hstable : (prefixWord ++ tailWord_335392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335392).length < 2 ^ (prefixWord ++ tailWord_335392).sum := by decide
  have hdescent : baseEnd_335392 < baseStart_335392 := by decide
  rcases family_descends (prefixWord ++ tailWord_335392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335433 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 7, 3]
def baseStart_335433 : Nat := 118140960795 + 335433 * 2 ^ 59
def prefixEnd_335433 : Nat := 4983230072969 + 3 ^ 40 * 335433 * 2
def baseEnd_335433 : Nat := 114825570919794233696585

theorem tailTrace_335433 : CollatzResearch.WordTrace tailWord_335433 prefixEnd_335433 114825570919794233696585 := by
  unfold tailWord_335433
  simp only [CollatzResearch.WordTrace]
  refine ⟨12234246593791003240626953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8156164395860668827084635 12234246593791003240626953)
  ·
    refine ⟨9175684945343252430470215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12234246593791003240626953 9175684945343252430470215)
    ·
      refine ⟨13763527418014878645705323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9175684945343252430470215 13763527418014878645705323)
      ·
        refine ⟨20645291127022317968557985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13763527418014878645705323 20645291127022317968557985)
        ·
          refine ⟨15483968345266738476418489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20645291127022317968557985 15483968345266738476418489)
          ·
            refine ⟨11612976258950053857313867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15483968345266738476418489 11612976258950053857313867)
            ·
              refine ⟨17419464388425080785970801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11612976258950053857313867 17419464388425080785970801)
              ·
                refine ⟨13064598291318810589478101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17419464388425080785970801 13064598291318810589478101)
                ·
                  refine ⟨306201522452784623190893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13064598291318810589478101 306201522452784623190893)
                  ·
                    refine ⟨114825570919794233696585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306201522452784623190893 114825570919794233696585)
                    ·
                      rfl

theorem cell22_335433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 3].length) (baseStart_335433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335433 prefixEnd_335433 := by exact prefixLift 335433
  have htrace : WordTrace (prefixWord ++ tailWord_335433) baseStart_335433 baseEnd_335433 := by
    simpa [prefixWord, tailWord_335433, baseEnd_335433] using wordTrace_append hprefix tailTrace_335433
  have hstable : (prefixWord ++ tailWord_335433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335433).length < 2 ^ (prefixWord ++ tailWord_335433).sum := by decide
  have hdescent : baseEnd_335433 < baseStart_335433 := by decide
  rcases family_descends (prefixWord ++ tailWord_335433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335523 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 3, 5]
def baseStart_335523 : Nat := 118140960795 + 335523 * 2 ^ 59
def prefixEnd_335523 : Nat := 4983230072969 + 3 ^ 40 * 335523 * 2
def baseEnd_335523 : Nat := 114856379759063998946309

theorem tailTrace_335523 : CollatzResearch.WordTrace tailWord_335523 prefixEnd_335523 114856379759063998946309 := by
  unfold tailWord_335523
  simp only [CollatzResearch.WordTrace]
  refine ⟨12237529163464948611403223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8158352775643299074268815 12237529163464948611403223)
  ·
    refine ⟨18356293745197422917104835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12237529163464948611403223 18356293745197422917104835)
    ·
      refine ⟨27534440617796134375657253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18356293745197422917104835 27534440617796134375657253)
      ·
        refine ⟨5162707615836775195435735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27534440617796134375657253 5162707615836775195435735)
        ·
          refine ⟨7744061423755162793153603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5162707615836775195435735 7744061423755162793153603)
          ·
            refine ⟨11616092135632744189730405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7744061423755162793153603 11616092135632744189730405)
            ·
              refine ⟨2178017275431139535574451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11616092135632744189730405 2178017275431139535574451)
              ·
                refine ⟨3267025913146709303361677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178017275431139535574451 3267025913146709303361677)
                ·
                  refine ⟨1225134717430015988760629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3267025913146709303361677 1225134717430015988760629)
                  ·
                    refine ⟨114856379759063998946309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1225134717430015988760629 114856379759063998946309)
                    ·
                      rfl

theorem cell22_335523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 5].length) (baseStart_335523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335523 prefixEnd_335523 := by exact prefixLift 335523
  have htrace : WordTrace (prefixWord ++ tailWord_335523) baseStart_335523 baseEnd_335523 := by
    simpa [prefixWord, tailWord_335523, baseEnd_335523] using wordTrace_append hprefix tailTrace_335523
  have hstable : (prefixWord ++ tailWord_335523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335523).length < 2 ^ (prefixWord ++ tailWord_335523).sum := by decide
  have hdescent : baseEnd_335523 < baseStart_335523 := by decide
  rcases family_descends (prefixWord ++ tailWord_335523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335570 : List Nat := [3, 2, 2, 2, 2, 1, 2, 8]
def baseStart_335570 : Nat := 118140960795 + 335570 * 2 ^ 59
def prefixEnd_335570 : Nat := 4983230072969 + 3 ^ 40 * 335570 * 2
def baseEnd_335570 : Nat := 12763607646619060335685

theorem tailTrace_335570 : CollatzResearch.WordTrace tailWord_335570 prefixEnd_335570 12763607646619060335685 := by
  unfold tailWord_335570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3059810848573668909591041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8159495596196450425576109 3059810848573668909591041)
  ·
    refine ⟨2294858136430251682193281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3059810848573668909591041 2294858136430251682193281)
    ·
      refine ⟨1721143602322688761644961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2294858136430251682193281 1721143602322688761644961)
      ·
        refine ⟨1290857701742016571233721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1721143602322688761644961 1290857701742016571233721)
        ·
          refine ⟨968143276306512428425291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1290857701742016571233721 968143276306512428425291)
          ·
            refine ⟨1452214914459768642637937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968143276306512428425291 1452214914459768642637937)
            ·
              refine ⟨1089161185844826481978453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1452214914459768642637937 1089161185844826481978453)
              ·
                refine ⟨12763607646619060335685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1089161185844826481978453 12763607646619060335685)
                ·
                  rfl

theorem cell22_335570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_335570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335570 prefixEnd_335570 := by exact prefixLift 335570
  have htrace : WordTrace (prefixWord ++ tailWord_335570) baseStart_335570 baseEnd_335570 := by
    simpa [prefixWord, tailWord_335570, baseEnd_335570] using wordTrace_append hprefix tailTrace_335570
  have hstable : (prefixWord ++ tailWord_335570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335570).length < 2 ^ (prefixWord ++ tailWord_335570).sum := by decide
  have hdescent : baseEnd_335570 < baseStart_335570 := by decide
  rcases family_descends (prefixWord ++ tailWord_335570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335572 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_335572 : Nat := 118140960795 + 335572 * 2 ^ 59
def prefixEnd_335572 : Nat := 4983230072969 + 3 ^ 40 * 335572 * 2
def baseEnd_335572 : Nat := 114873153460444204471159

theorem tailTrace_335572 : CollatzResearch.WordTrace tailWord_335572 prefixEnd_335572 114873153460444204471159 := by
  unfold tailWord_335572
  simp only [CollatzResearch.WordTrace]
  refine ⟨6119658170143714989968485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8159544226858286653291313 6119658170143714989968485)
  ·
    refine ⟨1147435906901946560619091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6119658170143714989968485 1147435906901946560619091)
    ·
      refine ⟨1721153860352919840928637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1147435906901946560619091 1721153860352919840928637)
      ·
        refine ⟨645432697632344940348239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1721153860352919840928637 645432697632344940348239)
        ·
          refine ⟨968149046448517410522359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645432697632344940348239 968149046448517410522359)
          ·
            refine ⟨1452223569672776115783539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968149046448517410522359 1452223569672776115783539)
            ·
              refine ⟨2178335354509164173675309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452223569672776115783539 2178335354509164173675309)
              ·
                refine ⟨816875757940936565128241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2178335354509164173675309 816875757940936565128241)
                ·
                  refine ⟨612656818455702423846181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 816875757940936565128241 612656818455702423846181)
                  ·
                    refine ⟨114873153460444204471159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 612656818455702423846181 114873153460444204471159)
                    ·
                      rfl

theorem cell22_335572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_335572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335572 prefixEnd_335572 := by exact prefixLift 335572
  have htrace : WordTrace (prefixWord ++ tailWord_335572) baseStart_335572 baseEnd_335572 := by
    simpa [prefixWord, tailWord_335572, baseEnd_335572] using wordTrace_append hprefix tailTrace_335572
  have hstable : (prefixWord ++ tailWord_335572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335572).length < 2 ^ (prefixWord ++ tailWord_335572).sum := by decide
  have hdescent : baseEnd_335572 < baseStart_335572 := by decide
  rcases family_descends (prefixWord ++ tailWord_335572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335591 : List Nat := [1, 1, 5, 4, 1, 1, 2, 2, 2, 3]
def baseStart_335591 : Nat := 118140960795 + 335591 * 2 ^ 59
def prefixEnd_335591 : Nat := 4983230072969 + 3 ^ 40 * 335591 * 2
def baseEnd_335591 : Nat := 114879657548734488246101

theorem tailTrace_335591 : CollatzResearch.WordTrace tailWord_335591 prefixEnd_335591 114879657548734488246101 := by
  unfold tailWord_335591
  simp only [CollatzResearch.WordTrace]
  refine ⟨12240009327218596224878627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8160006218145730816585751 12240009327218596224878627)
  ·
    refine ⟨18360013990827894337317941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12240009327218596224878627 18360013990827894337317941)
    ·
      refine ⟨1721251311640115094123557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18360013990827894337317941 1721251311640115094123557)
      ·
        refine ⟨322734620932521580148167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1721251311640115094123557 322734620932521580148167)
        ·
          refine ⟨484101931398782370222251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322734620932521580148167 484101931398782370222251)
          ·
            refine ⟨726152897098173555333377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484101931398782370222251 726152897098173555333377)
            ·
              refine ⟨544614672823630166500033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726152897098173555333377 544614672823630166500033)
              ·
                refine ⟨408461004617722624875025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544614672823630166500033 408461004617722624875025)
                ·
                  refine ⟨306345753463291968656269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408461004617722624875025 306345753463291968656269)
                  ·
                    refine ⟨114879657548734488246101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306345753463291968656269 114879657548734488246101)
                    ·
                      rfl

theorem cell22_335591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_335591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335591 prefixEnd_335591 := by exact prefixLift 335591
  have htrace : WordTrace (prefixWord ++ tailWord_335591) baseStart_335591 baseEnd_335591 := by
    simpa [prefixWord, tailWord_335591, baseEnd_335591] using wordTrace_append hprefix tailTrace_335591
  have hstable : (prefixWord ++ tailWord_335591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335591).length < 2 ^ (prefixWord ++ tailWord_335591).sum := by decide
  have hdescent : baseEnd_335591 < baseStart_335591 := by decide
  rcases family_descends (prefixWord ++ tailWord_335591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335602 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_335602 : Nat := 118140960795 + 335602 * 2 ^ 59
def prefixEnd_335602 : Nat := 4983230072969 + 3 ^ 40 * 335602 * 2
def baseEnd_335602 : Nat := 114883423073534126221067

theorem tailTrace_335602 : CollatzResearch.WordTrace tailWord_335602 prefixEnd_335602 114883423073534126221067 := by
  unfold tailWord_335602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3060102632544686275882265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8160273686785830069019373 3060102632544686275882265)
  ·
    refine ⟨2295076974408514706911699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3060102632544686275882265 2295076974408514706911699)
    ·
      refine ⟨3442615461612772060367549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2295076974408514706911699 3442615461612772060367549)
      ·
        refine ⟨1290980798104789522637831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3442615461612772060367549 1290980798104789522637831)
        ·
          refine ⟨1936471197157184283956747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290980798104789522637831 1936471197157184283956747)
          ·
            refine ⟨2904706795735776425935121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936471197157184283956747 2904706795735776425935121)
            ·
              refine ⟨2178530096801832319451341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2904706795735776425935121 2178530096801832319451341)
              ·
                refine ⟨816948786300687119794253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2178530096801832319451341 816948786300687119794253)
                ·
                  refine ⟨306355794862757669922845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816948786300687119794253 306355794862757669922845)
                  ·
                    refine ⟨114883423073534126221067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306355794862757669922845 114883423073534126221067)
                    ·
                      rfl

theorem cell22_335602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_335602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335602 prefixEnd_335602 := by exact prefixLift 335602
  have htrace : WordTrace (prefixWord ++ tailWord_335602) baseStart_335602 baseEnd_335602 := by
    simpa [prefixWord, tailWord_335602, baseEnd_335602] using wordTrace_append hprefix tailTrace_335602
  have hstable : (prefixWord ++ tailWord_335602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335602).length < 2 ^ (prefixWord ++ tailWord_335602).sum := by decide
  have hdescent : baseEnd_335602 < baseStart_335602 := by decide
  rcases family_descends (prefixWord ++ tailWord_335602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335604 : List Nat := [2, 6, 1, 1, 1, 1, 3, 7]
def baseStart_335604 : Nat := 118140960795 + 335604 * 2 ^ 59
def prefixEnd_335604 : Nat := 4983230072969 + 3 ^ 40 * 335604 * 2
def baseEnd_335604 : Nat := 12764900857156309741229

theorem tailTrace_335604 : CollatzResearch.WordTrace tailWord_335604 prefixEnd_335604 12764900857156309741229 := by
  unfold tailWord_335604
  simp only [CollatzResearch.WordTrace]
  refine ⟨6120241738085749722550933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8160322317447666296734577 6120241738085749722550933)
  ·
    refine ⟨286886331472769518244575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6120241738085749722550933 286886331472769518244575)
    ·
      refine ⟨430329497209154277366863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286886331472769518244575 430329497209154277366863)
      ·
        refine ⟨645494245813731416050295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430329497209154277366863 645494245813731416050295)
        ·
          refine ⟨968241368720597124075443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645494245813731416050295 968241368720597124075443)
          ·
            refine ⟨1452362053080895686113165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968241368720597124075443 1452362053080895686113165)
            ·
              refine ⟨544635769905335882292437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1452362053080895686113165 544635769905335882292437)
              ·
                refine ⟨12764900857156309741229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 544635769905335882292437 12764900857156309741229)
                ·
                  rfl

theorem cell22_335604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 7].length) (baseStart_335604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335604 prefixEnd_335604 := by exact prefixLift 335604
  have htrace : WordTrace (prefixWord ++ tailWord_335604) baseStart_335604 baseEnd_335604 := by
    simpa [prefixWord, tailWord_335604, baseEnd_335604] using wordTrace_append hprefix tailTrace_335604
  have hstable : (prefixWord ++ tailWord_335604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335604).length < 2 ^ (prefixWord ++ tailWord_335604).sum := by decide
  have hdescent : baseEnd_335604 < baseStart_335604 := by decide
  rcases family_descends (prefixWord ++ tailWord_335604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335615 : List Nat := [1, 1, 2, 2, 1, 3, 4, 3, 5]
def baseStart_335615 : Nat := 118140960795 + 335615 * 2 ^ 59
def prefixEnd_335615 : Nat := 4983230072969 + 3 ^ 40 * 335615 * 2
def baseEnd_335615 : Nat := 38295957746402141882009

theorem tailTrace_335615 : CollatzResearch.WordTrace tailWord_335615 prefixEnd_335615 38295957746402141882009 := by
  unfold tailWord_335615
  simp only [CollatzResearch.WordTrace]
  refine ⟨12240884679131648323752299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8160589786087765549168199 12240884679131648323752299)
  ·
    refine ⟨18361327018697472485628449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12240884679131648323752299 18361327018697472485628449)
    ·
      refine ⟨13770995264023104364221337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18361327018697472485628449 13770995264023104364221337)
      ·
        refine ⟨10328246448017328273166003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13770995264023104364221337 10328246448017328273166003)
        ·
          refine ⟨15492369672025992409749005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10328246448017328273166003 15492369672025992409749005)
          ·
            refine ⟨5809638627009747153655877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15492369672025992409749005 5809638627009747153655877)
            ·
              refine ⟨1089307242564327591310477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5809638627009747153655877 1089307242564327591310477)
              ·
                refine ⟨408490215961622846741429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1089307242564327591310477 408490215961622846741429)
                ·
                  refine ⟨38295957746402141882009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 408490215961622846741429 38295957746402141882009)
                  ·
                    rfl

theorem cell22_335615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 5].length) (baseStart_335615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335615 prefixEnd_335615 := by exact prefixLift 335615
  have htrace : WordTrace (prefixWord ++ tailWord_335615) baseStart_335615 baseEnd_335615 := by
    simpa [prefixWord, tailWord_335615, baseEnd_335615] using wordTrace_append hprefix tailTrace_335615
  have hstable : (prefixWord ++ tailWord_335615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335615).length < 2 ^ (prefixWord ++ tailWord_335615).sum := by decide
  have hdescent : baseEnd_335615 < baseStart_335615 := by decide
  rcases family_descends (prefixWord ++ tailWord_335615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335660 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 6]
def baseStart_335660 : Nat := 118140960795 + 335660 * 2 ^ 59
def prefixEnd_335660 : Nat := 4983230072969 + 3 ^ 40 * 335660 * 2
def baseEnd_335660 : Nat := 38301092552947102756963

theorem tailTrace_335660 : CollatzResearch.WordTrace tailWord_335660 prefixEnd_335660 38301092552947102756963 := by
  unfold tailWord_335660
  simp only [CollatzResearch.WordTrace]
  refine ⟨6121262981984310504570217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8161683975979080672760289 6121262981984310504570217)
  ·
    refine ⟨4590947236488232878427663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6121262981984310504570217 4590947236488232878427663)
    ·
      refine ⟨6886420854732349317641495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4590947236488232878427663 6886420854732349317641495)
      ·
        refine ⟨10329631282098523976462243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6886420854732349317641495 10329631282098523976462243)
        ·
          refine ⟨15494446923147785964693365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10329631282098523976462243 15494446923147785964693365)
          ·
            refine ⟨1452604399045104934190003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15494446923147785964693365 1452604399045104934190003)
            ·
              refine ⟨2178906598567657401285005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452604399045104934190003 2178906598567657401285005)
              ·
                refine ⟨817089974462871525481877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2178906598567657401285005 817089974462871525481877)
                ·
                  refine ⟨38301092552947102756963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 817089974462871525481877 38301092552947102756963)
                  ·
                    rfl

theorem cell22_335660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_335660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335660 prefixEnd_335660 := by exact prefixLift 335660
  have htrace : WordTrace (prefixWord ++ tailWord_335660) baseStart_335660 baseEnd_335660 := by
    simpa [prefixWord, tailWord_335660, baseEnd_335660] using wordTrace_append hprefix tailTrace_335660
  have hstable : (prefixWord ++ tailWord_335660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335660).length < 2 ^ (prefixWord ++ tailWord_335660).sum := by decide
  have hdescent : baseEnd_335660 < baseStart_335660 := by decide
  rcases family_descends (prefixWord ++ tailWord_335660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335677 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 6]
def baseStart_335677 : Nat := 118140960795 + 335677 * 2 ^ 59
def prefixEnd_335677 : Nat := 4983230072969 + 3 ^ 40 * 335677 * 2
def baseEnd_335677 : Nat := 38303032368752976865279

theorem tailTrace_335677 : CollatzResearch.WordTrace tailWord_335677 prefixEnd_335677 38303032368752976865279 := by
  unfold tailWord_335677
  simp only [CollatzResearch.WordTrace]
  refine ⟨12243146004907032912509285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8162097336604688608339523 12243146004907032912509285)
  ·
    refine ⟨2295589875920068671095491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12243146004907032912509285 2295589875920068671095491)
    ·
      refine ⟨3443384813880103006643237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2295589875920068671095491 3443384813880103006643237)
      ·
        refine ⟨645634652602519313745607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3443384813880103006643237 645634652602519313745607)
        ·
          refine ⟨968451978903778970618411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645634652602519313745607 968451978903778970618411)
          ·
            refine ⟨1452677968355668455927617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968451978903778970618411 1452677968355668455927617)
            ·
              refine ⟨1089508476266751341945713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1452677968355668455927617 1089508476266751341945713)
              ·
                refine ⟨817131357200063506459285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089508476266751341945713 817131357200063506459285)
                ·
                  refine ⟨38303032368752976865279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 817131357200063506459285 38303032368752976865279)
                  ·
                    rfl

theorem cell22_335677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_335677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335677 prefixEnd_335677 := by exact prefixLift 335677
  have htrace : WordTrace (prefixWord ++ tailWord_335677) baseStart_335677 baseEnd_335677 := by
    simpa [prefixWord, tailWord_335677, baseEnd_335677] using wordTrace_append hprefix tailTrace_335677
  have hstable : (prefixWord ++ tailWord_335677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335677).length < 2 ^ (prefixWord ++ tailWord_335677).sum := by decide
  have hdescent : baseEnd_335677 < baseStart_335677 := by decide
  rcases family_descends (prefixWord ++ tailWord_335677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335679 : List Nat := [1, 1, 2, 2, 6, 1, 2, 2, 1, 4]
def baseStart_335679 : Nat := 118140960795 + 335679 * 2 ^ 59
def prefixEnd_335679 : Nat := 4983230072969 + 3 ^ 40 * 335679 * 2
def baseEnd_335679 : Nat := 114909781747131592045831

theorem tailTrace_335679 : CollatzResearch.WordTrace tailWord_335679 prefixEnd_335679 114909781747131592045831 := by
  unfold tailWord_335679
  simp only [CollatzResearch.WordTrace]
  refine ⟨12243218950899787254082091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8162145967266524836054727 12243218950899787254082091)
  ·
    refine ⟨18364828426349680881123137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12243218950899787254082091 18364828426349680881123137)
    ·
      refine ⟨13773621319762260660842353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18364828426349680881123137 13773621319762260660842353)
      ·
        refine ⟨10330215989821695495631765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13773621319762260660842353 10330215989821695495631765)
        ·
          refine ⟨484228874522891976357739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10330215989821695495631765 484228874522891976357739)
          ·
            refine ⟨726343311784337964536609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484228874522891976357739 726343311784337964536609)
            ·
              refine ⟨544757483838253473402457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726343311784337964536609 544757483838253473402457)
              ·
                refine ⟨408568112878690105051843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544757483838253473402457 408568112878690105051843)
                ·
                  refine ⟨612852169318035157577765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408568112878690105051843 612852169318035157577765)
                  ·
                    refine ⟨114909781747131592045831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 612852169318035157577765 114909781747131592045831)
                    ·
                      rfl

theorem cell22_335679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_335679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335679 prefixEnd_335679 := by exact prefixLift 335679
  have htrace : WordTrace (prefixWord ++ tailWord_335679) baseStart_335679 baseEnd_335679 := by
    simpa [prefixWord, tailWord_335679, baseEnd_335679] using wordTrace_append hprefix tailTrace_335679
  have hstable : (prefixWord ++ tailWord_335679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335679).length < 2 ^ (prefixWord ++ tailWord_335679).sum := by decide
  have hdescent : baseEnd_335679 < baseStart_335679 := by decide
  rcases family_descends (prefixWord ++ tailWord_335679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335690 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_335690 : Nat := 118140960795 + 335690 * 2 ^ 59
def prefixEnd_335690 : Nat := 4983230072969 + 3 ^ 40 * 335690 * 2
def baseEnd_335690 : Nat := 114913547271931230020797

theorem tailTrace_335690 : CollatzResearch.WordTrace tailWord_335690 prefixEnd_335690 114913547271931230020797 := by
  unfold tailWord_335690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3060905038464984033183131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8162413435906624088488349 3060905038464984033183131)
  ·
    refine ⟨4591357557697476049774697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3060905038464984033183131 4591357557697476049774697)
    ·
      refine ⟨3443518168273107037331023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4591357557697476049774697 3443518168273107037331023)
      ·
        refine ⟨5165277252409660555996535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3443518168273107037331023 5165277252409660555996535)
        ·
          refine ⟨7747915878614490833994803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5165277252409660555996535 7747915878614490833994803)
          ·
            refine ⟨11621873817921736250992205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7747915878614490833994803 11621873817921736250992205)
            ·
              refine ⟨4358202681720651094122077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11621873817921736250992205 4358202681720651094122077)
              ·
                refine ⟨1634326005645244160295779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4358202681720651094122077 1634326005645244160295779)
                ·
                  refine ⟨2451489008467866240443669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634326005645244160295779 2451489008467866240443669)
                  ·
                    refine ⟨114913547271931230020797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2451489008467866240443669 114913547271931230020797)
                    ·
                      rfl

theorem cell22_335690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_335690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335690 prefixEnd_335690 := by exact prefixLift 335690
  have htrace : WordTrace (prefixWord ++ tailWord_335690) baseStart_335690 baseEnd_335690 := by
    simpa [prefixWord, tailWord_335690, baseEnd_335690] using wordTrace_append hprefix tailTrace_335690
  have hstable : (prefixWord ++ tailWord_335690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335690).length < 2 ^ (prefixWord ++ tailWord_335690).sum := by decide
  have hdescent : baseEnd_335690 < baseStart_335690 := by decide
  rcases family_descends (prefixWord ++ tailWord_335690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335726 : List Nat := [4, 1, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_335726 : Nat := 118140960795 + 335726 * 2 ^ 59
def prefixEnd_335726 : Nat := 4983230072969 + 3 ^ 40 * 335726 * 2
def baseEnd_335726 : Nat := 114925870807639136120687

theorem tailTrace_335726 : CollatzResearch.WordTrace tailWord_335726 prefixEnd_335726 114925870807639136120687 := by
  unfold tailWord_335726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1530616647716189285130379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8163288787819676187362021 1530616647716189285130379)
  ·
    refine ⟨2295924971574283927695569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1530616647716189285130379 2295924971574283927695569)
    ·
      refine ⟨1721943728680712945771677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2295924971574283927695569 1721943728680712945771677)
      ·
        refine ⟨645728898255267354664379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1721943728680712945771677 645728898255267354664379)
        ·
          refine ⟨968593347382901031996569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645728898255267354664379 968593347382901031996569)
          ·
            refine ⟨726445010537175773997427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 968593347382901031996569 726445010537175773997427)
            ·
              refine ⟨1089667515805763660996141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726445010537175773997427 1089667515805763660996141)
              ·
                refine ⟨408625318427161372873553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1089667515805763660996141 408625318427161372873553)
                ·
                  refine ⟨306468988820371029655165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408625318427161372873553 306468988820371029655165)
                  ·
                    refine ⟨114925870807639136120687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306468988820371029655165 114925870807639136120687)
                    ·
                      rfl

theorem cell22_335726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_335726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335726 prefixEnd_335726 := by exact prefixLift 335726
  have htrace : WordTrace (prefixWord ++ tailWord_335726) baseStart_335726 baseEnd_335726 := by
    simpa [prefixWord, tailWord_335726, baseEnd_335726] using wordTrace_append hprefix tailTrace_335726
  have hstable : (prefixWord ++ tailWord_335726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335726).length < 2 ^ (prefixWord ++ tailWord_335726).sum := by decide
  have hdescent : baseEnd_335726 < baseStart_335726 := by decide
  rcases family_descends (prefixWord ++ tailWord_335726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335737 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 5, 3]
def baseStart_335737 : Nat := 118140960795 + 335737 * 2 ^ 59
def prefixEnd_335737 : Nat := 4983230072969 + 3 ^ 40 * 335737 * 2
def baseEnd_335737 : Nat := 114929636332438774095653

theorem tailTrace_335737 : CollatzResearch.WordTrace tailWord_335737 prefixEnd_335737 114929636332438774095653 := by
  unfold tailWord_335737
  simp only [CollatzResearch.WordTrace]
  refine ⟨12245334384689663159693465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8163556256459775439795643 12245334384689663159693465)
  ·
    refine ⟨9184000788517247369770099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12245334384689663159693465 9184000788517247369770099)
    ·
      refine ⟨13776001182775871054655149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9184000788517247369770099 13776001182775871054655149)
      ·
        refine ⟨5166000443540951645495681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13776001182775871054655149 5166000443540951645495681)
        ·
          refine ⟨3874500332655713734121761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5166000443540951645495681 3874500332655713734121761)
          ·
            refine ⟨2905875249491785300591321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3874500332655713734121761 2905875249491785300591321)
            ·
              refine ⟨2179406437118838975443491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2905875249491785300591321 2179406437118838975443491)
              ·
                refine ⟨3269109655678258463165237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179406437118838975443491 3269109655678258463165237)
                ·
                  refine ⟨306479030219836730921741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3269109655678258463165237 306479030219836730921741)
                  ·
                    refine ⟨114929636332438774095653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306479030219836730921741 114929636332438774095653)
                    ·
                      rfl

theorem cell22_335737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 3].length) (baseStart_335737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335737 prefixEnd_335737 := by exact prefixLift 335737
  have htrace : WordTrace (prefixWord ++ tailWord_335737) baseStart_335737 baseEnd_335737 := by
    simpa [prefixWord, tailWord_335737, baseEnd_335737] using wordTrace_append hprefix tailTrace_335737
  have hstable : (prefixWord ++ tailWord_335737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335737).length < 2 ^ (prefixWord ++ tailWord_335737).sum := by decide
  have hdescent : baseEnd_335737 < baseStart_335737 := by decide
  rcases family_descends (prefixWord ++ tailWord_335737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335767 : List Nat := [1, 1, 3, 3, 1, 3, 1, 4, 5]
def baseStart_335767 : Nat := 118140960795 + 335767 * 2 ^ 59
def prefixEnd_335767 : Nat := 4983230072969 + 3 ^ 40 * 335767 * 2
def baseEnd_335767 : Nat := 38313301981842898615187

theorem tailTrace_335767 : CollatzResearch.WordTrace tailWord_335767 prefixEnd_335767 38313301981842898615187 := by
  unfold tailWord_335767
  simp only [CollatzResearch.WordTrace]
  refine ⟨12246428574580978283285555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8164285716387318855523703 12246428574580978283285555)
  ·
    refine ⟨18369642861871467424928333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12246428574580978283285555 18369642861871467424928333)
    ·
      refine ⟨6888616073201800284348125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18369642861871467424928333 6888616073201800284348125)
      ·
        refine ⟨2583231027450675106630547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6888616073201800284348125 2583231027450675106630547)
        ·
          refine ⟨3874846541176012659945821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583231027450675106630547 3874846541176012659945821)
          ·
            refine ⟨1453067452941004747479683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3874846541176012659945821 1453067452941004747479683)
            ·
              refine ⟨2179601179411507121219525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1453067452941004747479683 2179601179411507121219525)
              ·
                refine ⟨408675221139657585228661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2179601179411507121219525 408675221139657585228661)
                ·
                  refine ⟨38313301981842898615187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 408675221139657585228661 38313301981842898615187)
                  ·
                    rfl

theorem cell22_335767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 5].length) (baseStart_335767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335767 prefixEnd_335767 := by exact prefixLift 335767
  have htrace : WordTrace (prefixWord ++ tailWord_335767) baseStart_335767 baseEnd_335767 := by
    simpa [prefixWord, tailWord_335767, baseEnd_335767] using wordTrace_append hprefix tailTrace_335767
  have hstable : (prefixWord ++ tailWord_335767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335767).length < 2 ^ (prefixWord ++ tailWord_335767).sum := by decide
  have hdescent : baseEnd_335767 < baseStart_335767 := by decide
  rcases family_descends (prefixWord ++ tailWord_335767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335829 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 6]
def baseStart_335829 : Nat := 118140960795 + 335829 * 2 ^ 59
def prefixEnd_335829 : Nat := 4983230072969 + 3 ^ 40 * 335829 * 2
def baseEnd_335829 : Nat := 38320376604193733598457

theorem tailTrace_335829 : CollatzResearch.WordTrace tailWord_335829 prefixEnd_335829 38320376604193733598457 := by
  unfold tailWord_335829
  simp only [CollatzResearch.WordTrace]
  refine ⟨12248689900356362872042541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8165793266904241914695027 12248689900356362872042541)
  ·
    refine ⟨4593258712633636077015953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12248689900356362872042541 4593258712633636077015953)
    ·
      refine ⟨3444944034475227057761965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4593258712633636077015953 3444944034475227057761965)
      ·
        refine ⟨1291854012928210146660737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3444944034475227057761965 1291854012928210146660737)
        ·
          refine ⟨968890509696157609995553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1291854012928210146660737 968890509696157609995553)
          ·
            refine ⟨726667882272118207496665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 968890509696157609995553 726667882272118207496665)
            ·
              refine ⟨545000911704088655622499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726667882272118207496665 545000911704088655622499)
              ·
                refine ⟨817501367556132983433749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545000911704088655622499 817501367556132983433749)
                ·
                  refine ⟨38320376604193733598457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 817501367556132983433749 38320376604193733598457)
                  ·
                    rfl

theorem cell22_335829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_335829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335829 prefixEnd_335829 := by exact prefixLift 335829
  have htrace : WordTrace (prefixWord ++ tailWord_335829) baseStart_335829 baseEnd_335829 := by
    simpa [prefixWord, tailWord_335829, baseEnd_335829] using wordTrace_append hprefix tailTrace_335829
  have hstable : (prefixWord ++ tailWord_335829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335829).length < 2 ^ (prefixWord ++ tailWord_335829).sum := by decide
  have hdescent : baseEnd_335829 < baseStart_335829 := by decide
  rcases family_descends (prefixWord ++ tailWord_335829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335895 : List Nat := [1, 1, 3, 5, 2, 2, 2, 1, 2, 3]
def baseStart_335895 : Nat := 118140960795 + 335895 * 2 ^ 59
def prefixEnd_335895 : Nat := 4983230072969 + 3 ^ 40 * 335895 * 2
def baseEnd_335895 : Nat := 114983722961379028645169

theorem tailTrace_335895 : CollatzResearch.WordTrace tailWord_335895 prefixEnd_335895 114983722961379028645169 := by
  unfold tailWord_335895
  simp only [CollatzResearch.WordTrace]
  refine ⟨12251097118117256143945139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8167398078744837429296759 12251097118117256143945139)
  ·
    refine ⟨18376645677175884215917709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12251097118117256143945139 18376645677175884215917709)
    ·
      refine ⟨6891242128940956580969141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18376645677175884215917709 6891242128940956580969141)
      ·
        refine ⟨646053949588214679465857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6891242128940956580969141 646053949588214679465857)
        ·
          refine ⟨484540462191161009599393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646053949588214679465857 484540462191161009599393)
          ·
            refine ⟨363405346643370757199545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484540462191161009599393 363405346643370757199545)
            ·
              refine ⟨272554009982528067899659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363405346643370757199545 272554009982528067899659)
              ·
                refine ⟨408831014973792101849489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272554009982528067899659 408831014973792101849489)
                ·
                  refine ⟨306623261230344076387117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408831014973792101849489 306623261230344076387117)
                  ·
                    refine ⟨114983722961379028645169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306623261230344076387117 114983722961379028645169)
                    ·
                      rfl

theorem cell22_335895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_335895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335895 prefixEnd_335895 := by exact prefixLift 335895
  have htrace : WordTrace (prefixWord ++ tailWord_335895) baseStart_335895 baseEnd_335895 := by
    simpa [prefixWord, tailWord_335895, baseEnd_335895] using wordTrace_append hprefix tailTrace_335895
  have hstable : (prefixWord ++ tailWord_335895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335895).length < 2 ^ (prefixWord ++ tailWord_335895).sum := by decide
  have hdescent : baseEnd_335895 < baseStart_335895 := by decide
  rcases family_descends (prefixWord ++ tailWord_335895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335964 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 8]
def baseStart_335964 : Nat := 118140960795 + 335964 * 2 ^ 59
def prefixEnd_335964 : Nat := 4983230072969 + 3 ^ 40 * 335964 * 2
def baseEnd_335964 : Nat := 38335781023828616223319

theorem tailTrace_335964 : CollatzResearch.WordTrace tailWord_335964 prefixEnd_335964 38335781023828616223319 := by
  unfold tailWord_335964
  simp only [CollatzResearch.WordTrace]
  refine ⟨6126806877433640464103473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8169075836578187285471297 6126806877433640464103473)
  ·
    refine ⟨4595105158075230348077605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6126806877433640464103473 4595105158075230348077605)
    ·
      refine ⟨861582217139105690264551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4595105158075230348077605 861582217139105690264551)
      ·
        refine ⟨1292373325708658535396827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 861582217139105690264551 1292373325708658535396827)
        ·
          refine ⟨1938559988562987803095241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1292373325708658535396827 1938559988562987803095241)
          ·
            refine ⟨1453919991422240852321431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1938559988562987803095241 1453919991422240852321431)
            ·
              refine ⟨2180879987133361278482147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1453919991422240852321431 2180879987133361278482147)
              ·
                refine ⟨3271319980700041917723221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2180879987133361278482147 3271319980700041917723221)
                ·
                  refine ⟨38335781023828616223319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3271319980700041917723221 38335781023828616223319)
                  ·
                    rfl

theorem cell22_335964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_335964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335964 prefixEnd_335964 := by exact prefixLift 335964
  have htrace : WordTrace (prefixWord ++ tailWord_335964) baseStart_335964 baseEnd_335964 := by
    simpa [prefixWord, tailWord_335964, baseEnd_335964] using wordTrace_append hprefix tailTrace_335964
  have hstable : (prefixWord ++ tailWord_335964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335964).length < 2 ^ (prefixWord ++ tailWord_335964).sum := by decide
  have hdescent : baseEnd_335964 < baseStart_335964 := by decide
  rcases family_descends (prefixWord ++ tailWord_335964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335983 : List Nat := [1, 1, 2, 1, 3, 6, 2, 1, 1, 4]
def baseStart_335983 : Nat := 118140960795 + 335983 * 2 ^ 59
def prefixEnd_335983 : Nat := 4983230072969 + 3 ^ 40 * 335983 * 2
def baseEnd_335983 : Nat := 115013847159776132444899

theorem tailTrace_335983 : CollatzResearch.WordTrace tailWord_335983 prefixEnd_335983 115013847159776132444899 := by
  unfold tailWord_335983
  simp only [CollatzResearch.WordTrace]
  refine ⟨12254306741798447173148603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8169537827865631448765735 12254306741798447173148603)
  ·
    refine ⟨18381460112697670759722905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12254306741798447173148603 18381460112697670759722905)
    ·
      refine ⟨13786095084523253069792179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18381460112697670759722905 13786095084523253069792179)
      ·
        refine ⟨20679142626784879604688269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13786095084523253069792179 20679142626784879604688269)
        ·
          refine ⟨7754678485044329851758101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20679142626784879604688269 7754678485044329851758101)
          ·
            refine ⟨363500553986452961801161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7754678485044329851758101 363500553986452961801161)
            ·
              refine ⟨272625415489839721350871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363500553986452961801161 272625415489839721350871)
              ·
                refine ⟨408938123234759582026307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272625415489839721350871 408938123234759582026307)
                ·
                  refine ⟨613407184852139373039461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408938123234759582026307 613407184852139373039461)
                  ·
                    refine ⟨115013847159776132444899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 613407184852139373039461 115013847159776132444899)
                    ·
                      rfl

theorem cell22_335983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 1, 4].length) (baseStart_335983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335983 prefixEnd_335983 := by exact prefixLift 335983
  have htrace : WordTrace (prefixWord ++ tailWord_335983) baseStart_335983 baseEnd_335983 := by
    simpa [prefixWord, tailWord_335983, baseEnd_335983] using wordTrace_append hprefix tailTrace_335983
  have hstable : (prefixWord ++ tailWord_335983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335983).length < 2 ^ (prefixWord ++ tailWord_335983).sum := by decide
  have hdescent : baseEnd_335983 < baseStart_335983 := by decide
  rcases family_descends (prefixWord ++ tailWord_335983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335996 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 4, 3]
def baseStart_335996 : Nat := 118140960795 + 335996 * 2 ^ 59
def prefixEnd_335996 : Nat := 4983230072969 + 3 ^ 40 * 335996 * 2
def baseEnd_335996 : Nat := 115018297325448431869859

theorem tailTrace_335996 : CollatzResearch.WordTrace tailWord_335996 prefixEnd_335996 115018297325448431869859 := by
  unfold tailWord_335996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6127390445375675196685921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8169853927167566928914561 6127390445375675196685921)
  ·
    refine ⟨4595542834031756397514441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6127390445375675196685921 4595542834031756397514441)
    ·
      refine ⟨3446657125523817298135831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4595542834031756397514441 3446657125523817298135831)
      ·
        refine ⟨5169985688285725947203747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3446657125523817298135831 5169985688285725947203747)
        ·
          refine ⟨7754978532428588920805621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5169985688285725947203747 7754978532428588920805621)
          ·
            refine ⟨727029237415180211325527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7754978532428588920805621 727029237415180211325527)
            ·
              refine ⟨1090543856122770316988291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727029237415180211325527 1090543856122770316988291)
              ·
                refine ⟨1635815784184155475482437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1090543856122770316988291 1635815784184155475482437)
                ·
                  refine ⟨306715459534529151652957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1635815784184155475482437 306715459534529151652957)
                  ·
                    refine ⟨115018297325448431869859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306715459534529151652957 115018297325448431869859)
                    ·
                      rfl

theorem cell22_335996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_335996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_335996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_335996 prefixEnd_335996 := by exact prefixLift 335996
  have htrace : WordTrace (prefixWord ++ tailWord_335996) baseStart_335996 baseEnd_335996 := by
    simpa [prefixWord, tailWord_335996, baseEnd_335996] using wordTrace_append hprefix tailTrace_335996
  have hstable : (prefixWord ++ tailWord_335996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335996).length < 2 ^ (prefixWord ++ tailWord_335996).sum := by decide
  have hdescent : baseEnd_335996 < baseStart_335996 := by decide
  rcases family_descends (prefixWord ++ tailWord_335996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336026 : List Nat := [3, 1, 1, 5, 2, 1, 1, 8]
def baseStart_336026 : Nat := 118140960795 + 336026 * 2 ^ 59
def prefixEnd_336026 : Nat := 4983230072969 + 3 ^ 40 * 336026 * 2
def baseEnd_336026 : Nat := 12780951882059817068863

theorem tailTrace_336026 : CollatzResearch.WordTrace tailWord_336026 prefixEnd_336026 12780951882059817068863 := by
  unfold tailWord_336026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3063968770160666379240983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8170583387095110344642621 3063968770160666379240983)
  ·
    refine ⟨4595953155240999568861475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3063968770160666379240983 4595953155240999568861475)
    ·
      refine ⟨6893929732861499353292213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4595953155240999568861475 6893929732861499353292213)
      ·
        refine ⟨646305912455765564371145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6893929732861499353292213 646305912455765564371145)
        ·
          refine ⟨484729434341824173278359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646305912455765564371145 484729434341824173278359)
          ·
            refine ⟨727094151512736259917539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484729434341824173278359 727094151512736259917539)
            ·
              refine ⟨1090641227269104389876309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727094151512736259917539 1090641227269104389876309)
              ·
                refine ⟨12780951882059817068863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1090641227269104389876309 12780951882059817068863)
                ·
                  rfl

theorem cell22_336026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_336026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336026 prefixEnd_336026 := by exact prefixLift 336026
  have htrace : WordTrace (prefixWord ++ tailWord_336026) baseStart_336026 baseEnd_336026 := by
    simpa [prefixWord, tailWord_336026, baseEnd_336026] using wordTrace_append hprefix tailTrace_336026
  have hstable : (prefixWord ++ tailWord_336026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336026).length < 2 ^ (prefixWord ++ tailWord_336026).sum := by decide
  have hdescent : baseEnd_336026 < baseStart_336026 := by decide
  rcases family_descends (prefixWord ++ tailWord_336026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336058 : List Nat := [3, 1, 1, 1, 2, 2, 2, 6, 1, 3]
def baseStart_336058 : Nat := 118140960795 + 336058 * 2 ^ 59
def prefixEnd_336058 : Nat := 4983230072969 + 3 ^ 40 * 336058 * 2
def baseEnd_336058 : Nat := 115039521192500936819669

theorem tailTrace_336058 : CollatzResearch.WordTrace tailWord_336058 prefixEnd_336058 115039521192500936819669 := by
  unfold tailWord_336058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3064260554131683745532207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8171361477684489988085885 3064260554131683745532207)
  ·
    refine ⟨4596390831197525618298311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3064260554131683745532207 4596390831197525618298311)
    ·
      refine ⟨6894586246796288427447467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4596390831197525618298311 6894586246796288427447467)
      ·
        refine ⟨10341879370194432641171201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6894586246796288427447467 10341879370194432641171201)
        ·
          refine ⟨7756409527645824480878401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10341879370194432641171201 7756409527645824480878401)
          ·
            refine ⟨5817307145734368360658801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7756409527645824480878401 5817307145734368360658801)
            ·
              refine ⟨4362980359300776270494101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5817307145734368360658801 4362980359300776270494101)
              ·
                refine ⟨204514704342223887679411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4362980359300776270494101 204514704342223887679411)
                ·
                  refine ⟨306772056513335831519117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204514704342223887679411 306772056513335831519117)
                  ·
                    refine ⟨115039521192500936819669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306772056513335831519117 115039521192500936819669)
                    ·
                      rfl

theorem cell22_336058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_336058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336058 prefixEnd_336058 := by exact prefixLift 336058
  have htrace : WordTrace (prefixWord ++ tailWord_336058) baseStart_336058 baseEnd_336058 := by
    simpa [prefixWord, tailWord_336058, baseEnd_336058] using wordTrace_append hprefix tailTrace_336058
  have hstable : (prefixWord ++ tailWord_336058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336058).length < 2 ^ (prefixWord ++ tailWord_336058).sum := by decide
  have hdescent : baseEnd_336058 < baseStart_336058 := by decide
  rcases family_descends (prefixWord ++ tailWord_336058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336069 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_336069 : Nat := 118140960795 + 336069 * 2 ^ 59
def prefixEnd_336069 : Nat := 4983230072969 + 3 ^ 40 * 336069 * 2
def baseEnd_336069 : Nat := 115043286717300574794635

theorem tailTrace_336069 : CollatzResearch.WordTrace tailWord_336069 prefixEnd_336069 115043286717300574794635 := by
  unfold tailWord_336069
  simp only [CollatzResearch.WordTrace]
  refine ⟨12257443419486883860779261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8171628946324589240519507 12257443419486883860779261)
  ·
    refine ⟨4596541282307581447792223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12257443419486883860779261 4596541282307581447792223)
    ·
      refine ⟨6894811923461372171688335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4596541282307581447792223 6894811923461372171688335)
      ·
        refine ⟨10342217885192058257532503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6894811923461372171688335 10342217885192058257532503)
        ·
          refine ⟨15513326827788087386298755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10342217885192058257532503 15513326827788087386298755)
          ·
            refine ⟨23269990241682131079448133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15513326827788087386298755 23269990241682131079448133)
            ·
              refine ⟨4363123170315399577396525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23269990241682131079448133 4363123170315399577396525)
              ·
                refine ⟨1636171188868274841523697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4363123170315399577396525 1636171188868274841523697)
                ·
                  refine ⟨1227128391651206131142773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1636171188868274841523697 1227128391651206131142773)
                  ·
                    refine ⟨115043286717300574794635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1227128391651206131142773 115043286717300574794635)
                    ·
                      rfl

theorem cell22_336069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_336069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336069 prefixEnd_336069 := by exact prefixLift 336069
  have htrace : WordTrace (prefixWord ++ tailWord_336069) baseStart_336069 baseEnd_336069 := by
    simpa [prefixWord, tailWord_336069, baseEnd_336069] using wordTrace_append hprefix tailTrace_336069
  have hstable : (prefixWord ++ tailWord_336069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336069).length < 2 ^ (prefixWord ++ tailWord_336069).sum := by decide
  have hdescent : baseEnd_336069 < baseStart_336069 := by decide
  rcases family_descends (prefixWord ++ tailWord_336069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336109 : List Nat := [1, 5, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_336109 : Nat := 118140960795 + 336109 * 2 ^ 59
def prefixEnd_336109 : Nat := 4983230072969 + 3 ^ 40 * 336109 * 2
def baseEnd_336109 : Nat := 115056979534753803794513

theorem tailTrace_336109 : CollatzResearch.WordTrace tailWord_336109 prefixEnd_336109 115056979534753803794513 := by
  unfold tailWord_336109
  simp only [CollatzResearch.WordTrace]
  refine ⟨12258902339341970692235381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8172601559561313794823587 12258902339341970692235381)
  ·
    refine ⟨1149272094313309752397067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12258902339341970692235381 1149272094313309752397067)
    ·
      refine ⟨1723908141469964628595601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1149272094313309752397067 1723908141469964628595601)
      ·
        refine ⟨1292931106102473471446701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1723908141469964628595601 1292931106102473471446701)
        ·
          refine ⟨484849164788427551792513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1292931106102473471446701 484849164788427551792513)
          ·
            refine ⟨363636873591320663844385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484849164788427551792513 363636873591320663844385)
            ·
              refine ⟨272727655193490497883289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363636873591320663844385 272727655193490497883289)
              ·
                refine ⟨204545741395117873412467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272727655193490497883289 204545741395117873412467)
                ·
                  refine ⟨306818612092676810118701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204545741395117873412467 306818612092676810118701)
                  ·
                    refine ⟨115056979534753803794513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306818612092676810118701 115056979534753803794513)
                    ·
                      rfl

theorem cell22_336109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_336109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336109 prefixEnd_336109 := by exact prefixLift 336109
  have htrace : WordTrace (prefixWord ++ tailWord_336109) baseStart_336109 baseEnd_336109 := by
    simpa [prefixWord, tailWord_336109, baseEnd_336109] using wordTrace_append hprefix tailTrace_336109
  have hstable : (prefixWord ++ tailWord_336109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336109).length < 2 ^ (prefixWord ++ tailWord_336109).sum := by decide
  have hdescent : baseEnd_336109 < baseStart_336109 := by decide
  rcases family_descends (prefixWord ++ tailWord_336109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336131 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 1, 5]
def baseStart_336131 : Nat := 118140960795 + 336131 * 2 ^ 59
def prefixEnd_336131 : Nat := 4983230072969 + 3 ^ 40 * 336131 * 2
def baseEnd_336131 : Nat := 115064510584353079744445

theorem tailTrace_336131 : CollatzResearch.WordTrace tailWord_336131 prefixEnd_336131 115064510584353079744445 := by
  unfold tailWord_336131
  simp only [CollatzResearch.WordTrace]
  refine ⟨12259704745262268449536247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8173136496841512299690831 12259704745262268449536247)
  ·
    refine ⟨18389557117893402674304371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12259704745262268449536247 18389557117893402674304371)
    ·
      refine ⟨27584335676840104011456557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18389557117893402674304371 27584335676840104011456557)
      ·
        refine ⟨10344125878815039004296209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27584335676840104011456557 10344125878815039004296209)
        ·
          refine ⟨7758094409111279253222157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10344125878815039004296209 7758094409111279253222157)
          ·
            refine ⟨2909285403416729719958309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7758094409111279253222157 2909285403416729719958309)
            ·
              refine ⟨545491013140636822492183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2909285403416729719958309 545491013140636822492183)
              ·
                refine ⟨818236519710955233738275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545491013140636822492183 818236519710955233738275)
                ·
                  refine ⟨1227354779566432850607413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818236519710955233738275 1227354779566432850607413)
                  ·
                    refine ⟨115064510584353079744445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1227354779566432850607413 115064510584353079744445)
                    ·
                      rfl

theorem cell22_336131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 5].length) (baseStart_336131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336131 prefixEnd_336131 := by exact prefixLift 336131
  have htrace : WordTrace (prefixWord ++ tailWord_336131) baseStart_336131 baseEnd_336131 := by
    simpa [prefixWord, tailWord_336131, baseEnd_336131] using wordTrace_append hprefix tailTrace_336131
  have hstable : (prefixWord ++ tailWord_336131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336131).length < 2 ^ (prefixWord ++ tailWord_336131).sum := by decide
  have hdescent : baseEnd_336131 < baseStart_336131 := by decide
  rcases family_descends (prefixWord ++ tailWord_336131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336167 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 6]
def baseStart_336167 : Nat := 118140960795 + 336167 * 2 ^ 59
def prefixEnd_336167 : Nat := 4983230072969 + 3 ^ 40 * 336167 * 2
def baseEnd_336167 : Nat := 38358944706686995281445

theorem tailTrace_336167 : CollatzResearch.WordTrace tailWord_336167 prefixEnd_336167 38358944706686995281445 := by
  unfold tailWord_336167
  simp only [CollatzResearch.WordTrace]
  refine ⟨12261017773131846597846755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8174011848754564398564503 12261017773131846597846755)
  ·
    refine ⟨18391526659697769896770133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12261017773131846597846755 18391526659697769896770133)
    ·
      refine ⟨215525703043333240977775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 18391526659697769896770133 215525703043333240977775)
      ·
        refine ⟨323288554564999861466663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215525703043333240977775 323288554564999861466663)
        ·
          refine ⟨484932831847499792199995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323288554564999861466663 484932831847499792199995)
          ·
            refine ⟨727399247771249688299993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484932831847499792199995 727399247771249688299993)
            ·
              refine ⟨545549435828437266224995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727399247771249688299993 545549435828437266224995)
              ·
                refine ⟨818324153742655899337493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545549435828437266224995 818324153742655899337493)
                ·
                  refine ⟨38358944706686995281445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 818324153742655899337493 38358944706686995281445)
                  ·
                    rfl

theorem cell22_336167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 6].length) (baseStart_336167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336167 prefixEnd_336167 := by exact prefixLift 336167
  have htrace : WordTrace (prefixWord ++ tailWord_336167) baseStart_336167 baseEnd_336167 := by
    simpa [prefixWord, tailWord_336167, baseEnd_336167] using wordTrace_append hprefix tailTrace_336167
  have hstable : (prefixWord ++ tailWord_336167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336167).length < 2 ^ (prefixWord ++ tailWord_336167).sum := by decide
  have hdescent : baseEnd_336167 < baseStart_336167 := by decide
  rcases family_descends (prefixWord ++ tailWord_336167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336227 : List Nat := [1, 1, 1, 5, 2, 1, 5, 2, 1, 3]
def baseStart_336227 : Nat := 118140960795 + 336227 * 2 ^ 59
def prefixEnd_336227 : Nat := 4983230072969 + 3 ^ 40 * 336227 * 2
def baseEnd_336227 : Nat := 115097373346240829344151

theorem tailTrace_336227 : CollatzResearch.WordTrace tailWord_336227 prefixEnd_336227 115097373346240829344151 := by
  unfold tailWord_336227
  simp only [CollatzResearch.WordTrace]
  refine ⟨12263206152914476845030935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8175470768609651230020623 12263206152914476845030935)
  ·
    refine ⟨18394809229371715267546403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12263206152914476845030935 18394809229371715267546403)
    ·
      refine ⟨27592213844057572901319605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18394809229371715267546403 27592213844057572901319605)
      ·
        refine ⟨2586770047880397459498713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27592213844057572901319605 2586770047880397459498713)
        ·
          refine ⟨1940077535910298094624035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2586770047880397459498713 1940077535910298094624035)
          ·
            refine ⟨2910116303865447141936053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940077535910298094624035 2910116303865447141936053)
            ·
              refine ⟨272823403487385669556505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2910116303865447141936053 272823403487385669556505)
              ·
                refine ⟨204617552615539252167379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272823403487385669556505 204617552615539252167379)
                ·
                  refine ⟨306926328923308878251069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204617552615539252167379 306926328923308878251069)
                  ·
                    refine ⟨115097373346240829344151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306926328923308878251069 115097373346240829344151)
                    ·
                      rfl

theorem cell22_336227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 1, 3].length) (baseStart_336227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336227 prefixEnd_336227 := by exact prefixLift 336227
  have htrace : WordTrace (prefixWord ++ tailWord_336227) baseStart_336227 baseEnd_336227 := by
    simpa [prefixWord, tailWord_336227, baseEnd_336227] using wordTrace_append hprefix tailTrace_336227
  have hstable : (prefixWord ++ tailWord_336227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336227).length < 2 ^ (prefixWord ++ tailWord_336227).sum := by decide
  have hdescent : baseEnd_336227 < baseStart_336227 := by decide
  rcases family_descends (prefixWord ++ tailWord_336227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336240 : List Nat := [2, 1, 1, 1, 4, 5, 2, 1, 5]
def baseStart_336240 : Nat := 118140960795 + 336240 * 2 ^ 59
def prefixEnd_336240 : Nat := 4983230072969 + 3 ^ 40 * 336240 * 2
def baseEnd_336240 : Nat := 38367274503971042923037

theorem tailTrace_336240 : CollatzResearch.WordTrace tailWord_336240 prefixEnd_336240 38367274503971042923037 := by
  unfold tailWord_336240
  simp only [CollatzResearch.WordTrace]
  refine ⟨6131840150933690032627087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8175786867911586710169449 6131840150933690032627087)
  ·
    refine ⟨9197760226400535048940631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6131840150933690032627087 9197760226400535048940631)
    ·
      refine ⟨13796640339600802573410947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9197760226400535048940631 13796640339600802573410947)
      ·
        refine ⟨20694960509401203860116421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13796640339600802573410947 20694960509401203860116421)
        ·
          refine ⟨3880305095512725723771829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20694960509401203860116421 3880305095512725723771829)
          ·
            refine ⟨363778602704318036603609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3880305095512725723771829 363778602704318036603609)
            ·
              refine ⟨272833952028238527452707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363778602704318036603609 272833952028238527452707)
              ·
                refine ⟨409250928042357791179061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272833952028238527452707 409250928042357791179061)
                ·
                  refine ⟨38367274503971042923037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 409250928042357791179061 38367274503971042923037)
                  ·
                    rfl

theorem cell22_336240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 5].length) (baseStart_336240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336240 prefixEnd_336240 := by exact prefixLift 336240
  have htrace : WordTrace (prefixWord ++ tailWord_336240) baseStart_336240 baseEnd_336240 := by
    simpa [prefixWord, tailWord_336240, baseEnd_336240] using wordTrace_append hprefix tailTrace_336240
  have hstable : (prefixWord ++ tailWord_336240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336240).length < 2 ^ (prefixWord ++ tailWord_336240).sum := by decide
  have hdescent : baseEnd_336240 < baseStart_336240 := by decide
  rcases family_descends (prefixWord ++ tailWord_336240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336253 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_336253 : Nat := 118140960795 + 336253 * 2 ^ 59
def prefixEnd_336253 : Nat := 4983230072969 + 3 ^ 40 * 336253 * 2
def baseEnd_336253 : Nat := 115106273677585428194071

theorem tailTrace_336253 : CollatzResearch.WordTrace tailWord_336253 prefixEnd_336253 115106273677585428194071 := by
  unfold tailWord_336253
  simp only [CollatzResearch.WordTrace]
  refine ⟨12264154450820283285477413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8176102967213522190318275 12264154450820283285477413)
  ·
    refine ⟨2299528959528803116027015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12264154450820283285477413 2299528959528803116027015)
    ·
      refine ⟨3449293439293204674040523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299528959528803116027015 3449293439293204674040523)
      ·
        refine ⟨5173940158939807011060785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3449293439293204674040523 5173940158939807011060785)
        ·
          refine ⟨3880455119204855258295589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5173940158939807011060785 3880455119204855258295589)
          ·
            refine ⟨727585334850910360930423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3880455119204855258295589 727585334850910360930423)
            ·
              refine ⟨1091378002276365541395635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727585334850910360930423 1091378002276365541395635)
              ·
                refine ⟨1637067003414548312093453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091378002276365541395635 1637067003414548312093453)
                ·
                  refine ⟨613900126280455617035045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1637067003414548312093453 613900126280455617035045)
                  ·
                    refine ⟨115106273677585428194071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 613900126280455617035045 115106273677585428194071)
                    ·
                      rfl

theorem cell22_336253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_336253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336253 prefixEnd_336253 := by exact prefixLift 336253
  have htrace : WordTrace (prefixWord ++ tailWord_336253) baseStart_336253 baseEnd_336253 := by
    simpa [prefixWord, tailWord_336253, baseEnd_336253] using wordTrace_append hprefix tailTrace_336253
  have hstable : (prefixWord ++ tailWord_336253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336253).length < 2 ^ (prefixWord ++ tailWord_336253).sum := by decide
  have hdescent : baseEnd_336253 < baseStart_336253 := by decide
  rcases family_descends (prefixWord ++ tailWord_336253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336278 : List Nat := [5, 3, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_336278 : Nat := 118140960795 + 336278 * 2 ^ 59
def prefixEnd_336278 : Nat := 4983230072969 + 3 ^ 40 * 336278 * 2
def baseEnd_336278 : Nat := 115114831688493696318995

theorem tailTrace_336278 : CollatzResearch.WordTrace tailWord_336278 prefixEnd_336278 115114831688493696318995 := by
  unfold tailWord_336278
  simp only [CollatzResearch.WordTrace]
  refine ⟨766566642233107034696093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8176710850486475036758325 766566642233107034696093)
  ·
    refine ⟨287462490837415138011035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 766566642233107034696093 287462490837415138011035)
    ·
      refine ⟨431193736256122707016553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287462490837415138011035 431193736256122707016553)
      ·
        refine ⟨323395302192092030262415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431193736256122707016553 323395302192092030262415)
        ·
          refine ⟨485092953288138045393623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323395302192092030262415 485092953288138045393623)
          ·
            refine ⟨727639429932207068090435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485092953288138045393623 727639429932207068090435)
            ·
              refine ⟨1091459144898310602135653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727639429932207068090435 1091459144898310602135653)
              ·
                refine ⟨204648589668433237900435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1091459144898310602135653 204648589668433237900435)
                ·
                  refine ⟨306972884502649856850653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204648589668433237900435 306972884502649856850653)
                  ·
                    refine ⟨115114831688493696318995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 306972884502649856850653 115114831688493696318995)
                    ·
                      rfl

theorem cell22_336278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_336278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336278 prefixEnd_336278 := by exact prefixLift 336278
  have htrace : WordTrace (prefixWord ++ tailWord_336278) baseStart_336278 baseEnd_336278 := by
    simpa [prefixWord, tailWord_336278, baseEnd_336278] using wordTrace_append hprefix tailTrace_336278
  have hstable : (prefixWord ++ tailWord_336278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336278).length < 2 ^ (prefixWord ++ tailWord_336278).sum := by decide
  have hdescent : baseEnd_336278 < baseStart_336278 := by decide
  rcases family_descends (prefixWord ++ tailWord_336278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336345 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 3, 3]
def baseStart_336345 : Nat := 118140960795 + 336345 * 2 ^ 59
def prefixEnd_336345 : Nat := 4983230072969 + 3 ^ 40 * 336345 * 2
def baseEnd_336345 : Nat := 115137767157727854893789

theorem tailTrace_336345 : CollatzResearch.WordTrace tailWord_336345 prefixEnd_336345 115137767157727854893789 := by
  unfold tailWord_336345
  simp only [CollatzResearch.WordTrace]
  refine ⟨12267509966486982997826489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8178339977657988665217659 12267509966486982997826489)
  ·
    refine ⟨9200632474865237248369867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12267509966486982997826489 9200632474865237248369867)
    ·
      refine ⟨13800948712297855872554801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9200632474865237248369867 13800948712297855872554801)
      ·
        refine ⟨10350711534223391904416101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13800948712297855872554801 10350711534223391904416101)
        ·
          refine ⟨1940758412666885982078019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10350711534223391904416101 1940758412666885982078019)
          ·
            refine ⟨2911137619000328973117029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940758412666885982078019 2911137619000328973117029)
            ·
              refine ⟨545838303562561682459443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2911137619000328973117029 545838303562561682459443)
              ·
                refine ⟨818757455343842523689165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545838303562561682459443 818757455343842523689165)
                ·
                  refine ⟨307034045753940946383437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818757455343842523689165 307034045753940946383437)
                  ·
                    refine ⟨115137767157727854893789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 307034045753940946383437 115137767157727854893789)
                    ·
                      rfl

theorem cell22_336345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 3].length) (baseStart_336345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336345 prefixEnd_336345 := by exact prefixLift 336345
  have htrace : WordTrace (prefixWord ++ tailWord_336345) baseStart_336345 baseEnd_336345 := by
    simpa [prefixWord, tailWord_336345, baseEnd_336345] using wordTrace_append hprefix tailTrace_336345
  have hstable : (prefixWord ++ tailWord_336345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336345).length < 2 ^ (prefixWord ++ tailWord_336345).sum := by decide
  have hdescent : baseEnd_336345 < baseStart_336345 := by decide
  rcases family_descends (prefixWord ++ tailWord_336345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336433 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 1, 6]
def baseStart_336433 : Nat := 118140960795 + 336433 * 2 ^ 59
def prefixEnd_336433 : Nat := 4983230072969 + 3 ^ 40 * 336433 * 2
def baseEnd_336433 : Nat := 115167891356124958693519

theorem tailTrace_336433 : CollatzResearch.WordTrace tailWord_336433 prefixEnd_336433 115167891356124958693519 := by
  unfold tailWord_336433
  simp only [CollatzResearch.WordTrace]
  refine ⟨12270719590168174027029953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8180479726778782684686635 12270719590168174027029953)
  ·
    refine ⟨9203039692626130520272465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12270719590168174027029953 9203039692626130520272465)
    ·
      refine ⟨6902279769469597890204349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9203039692626130520272465 6902279769469597890204349)
      ·
        refine ⟨2588354913551099208826631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6902279769469597890204349 2588354913551099208826631)
        ·
          refine ⟨3882532370326648813239947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2588354913551099208826631 3882532370326648813239947)
          ·
            refine ⟨5823798555489973219859921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3882532370326648813239947 5823798555489973219859921)
            ·
              refine ⟨4367848916617479914894941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5823798555489973219859921 4367848916617479914894941)
              ·
                refine ⟨1637943343731554968085603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4367848916617479914894941 1637943343731554968085603)
                ·
                  refine ⟨2456915015597332452128405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637943343731554968085603 2456915015597332452128405)
                  ·
                    refine ⟨115167891356124958693519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2456915015597332452128405 115167891356124958693519)
                    ·
                      rfl

theorem cell22_336433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_336433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336433 prefixEnd_336433 := by exact prefixLift 336433
  have htrace : WordTrace (prefixWord ++ tailWord_336433) baseStart_336433 baseEnd_336433 := by
    simpa [prefixWord, tailWord_336433, baseEnd_336433] using wordTrace_append hprefix tailTrace_336433
  have hstable : (prefixWord ++ tailWord_336433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336433).length < 2 ^ (prefixWord ++ tailWord_336433).sum := by decide
  have hdescent : baseEnd_336433 < baseStart_336433 := by decide
  rcases family_descends (prefixWord ++ tailWord_336433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336465 : List Nat := [1, 2, 2, 1, 3, 5, 1, 7]
def baseStart_336465 : Nat := 118140960795 + 336465 * 2 ^ 59
def prefixEnd_336465 : Nat := 4983230072969 + 3 ^ 40 * 336465 * 2
def baseEnd_336465 : Nat := 12797649512231949099269

theorem tailTrace_336465 : CollatzResearch.WordTrace tailWord_336465 prefixEnd_336465 12797649512231949099269 := by
  unfold tailWord_336465
  simp only [CollatzResearch.WordTrace]
  refine ⟨12271886726052243492194849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8181257817368162328129899 12271886726052243492194849)
  ·
    refine ⟨9203915044539182619146137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12271886726052243492194849 9203915044539182619146137)
    ·
      refine ⟨6902936283404386964359603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9203915044539182619146137 6902936283404386964359603)
      ·
        refine ⟨10354404425106580446539405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6902936283404386964359603 10354404425106580446539405)
        ·
          refine ⟨3882901659414967667452277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10354404425106580446539405 3882901659414967667452277)
          ·
            refine ⟨364022030570153218823651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3882901659414967667452277 364022030570153218823651)
            ·
              refine ⟨546033045855229828235477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364022030570153218823651 546033045855229828235477)
              ·
                refine ⟨12797649512231949099269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 546033045855229828235477 12797649512231949099269)
                ·
                  rfl

theorem cell22_336465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 7].length) (baseStart_336465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336465 prefixEnd_336465 := by exact prefixLift 336465
  have htrace : WordTrace (prefixWord ++ tailWord_336465) baseStart_336465 baseEnd_336465 := by
    simpa [prefixWord, tailWord_336465, baseEnd_336465] using wordTrace_append hprefix tailTrace_336465
  have hstable : (prefixWord ++ tailWord_336465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336465).length < 2 ^ (prefixWord ++ tailWord_336465).sum := by decide
  have hdescent : baseEnd_336465 < baseStart_336465 := by decide
  rcases family_descends (prefixWord ++ tailWord_336465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336480 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 5, 3]
def baseStart_336480 : Nat := 118140960795 + 336480 * 2 ^ 59
def prefixEnd_336480 : Nat := 4983230072969 + 3 ^ 40 * 336480 * 2
def baseEnd_336480 : Nat := 115183980416632502768375

theorem tailTrace_336480 : CollatzResearch.WordTrace tailWord_336480 prefixEnd_336480 115183980416632502768375 := by
  unfold tailWord_336480
  simp only [CollatzResearch.WordTrace]
  refine ⟨6136216910498950526995447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8181622547331934035993929 6136216910498950526995447)
  ·
    refine ⟨9204325365748425790493171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6136216910498950526995447 9204325365748425790493171)
    ·
      refine ⟨13806488048622638685739757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9204325365748425790493171 13806488048622638685739757)
      ·
        refine ⟨5177433018233489507152409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13806488048622638685739757 5177433018233489507152409)
        ·
          refine ⟨3883074763675117130364307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5177433018233489507152409 3883074763675117130364307)
          ·
            refine ⟨5824612145512675695546461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3883074763675117130364307 5824612145512675695546461)
            ·
              refine ⟨2184229554567253385829923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5824612145512675695546461 2184229554567253385829923)
              ·
                refine ⟨3276344331850880078744885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184229554567253385829923 3276344331850880078744885)
                ·
                  refine ⟨307157281111020007382333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3276344331850880078744885 307157281111020007382333)
                  ·
                    refine ⟨115183980416632502768375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 307157281111020007382333 115183980416632502768375)
                    ·
                      rfl

theorem cell22_336480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 5, 3].length) (baseStart_336480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336480 prefixEnd_336480 := by exact prefixLift 336480
  have htrace : WordTrace (prefixWord ++ tailWord_336480) baseStart_336480 baseEnd_336480 := by
    simpa [prefixWord, tailWord_336480, baseEnd_336480] using wordTrace_append hprefix tailTrace_336480
  have hstable : (prefixWord ++ tailWord_336480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336480).length < 2 ^ (prefixWord ++ tailWord_336480).sum := by decide
  have hdescent : baseEnd_336480 < baseStart_336480 := by decide
  rcases family_descends (prefixWord ++ tailWord_336480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336523 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 2, 8]
def baseStart_336523 : Nat := 118140960795 + 336523 * 2 ^ 59
def prefixEnd_336523 : Nat := 4983230072969 + 3 ^ 40 * 336523 * 2
def baseEnd_336523 : Nat := 115198700195394723943243

theorem tailTrace_336523 : CollatzResearch.WordTrace tailWord_336523 prefixEnd_336523 115198700195394723943243 := by
  unfold tailWord_336523
  simp only [CollatzResearch.WordTrace]
  refine ⟨12274002159842119397806223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8182668106561412931870815 12274002159842119397806223)
  ·
    refine ⟨18411003239763179096709335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12274002159842119397806223 18411003239763179096709335)
    ·
      refine ⟨27616504859644768645064003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18411003239763179096709335 27616504859644768645064003)
      ·
        refine ⟨41424757289467152967596005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27616504859644768645064003 41424757289467152967596005)
        ·
          refine ⟨7767141991775091181424251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41424757289467152967596005 7767141991775091181424251)
          ·
            refine ⟨11650712987662636772136377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7767141991775091181424251 11650712987662636772136377)
            ·
              refine ⟨8738034740746977579102283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11650712987662636772136377 8738034740746977579102283)
              ·
                refine ⟨13107052111120466368653425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8738034740746977579102283 13107052111120466368653425)
                ·
                  refine ⟨9830289083340349776490069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13107052111120466368653425 9830289083340349776490069)
                  ·
                    refine ⟨115198700195394723943243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9830289083340349776490069 115198700195394723943243)
                    ·
                      rfl

theorem cell22_336523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_336523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336523 prefixEnd_336523 := by exact prefixLift 336523
  have htrace : WordTrace (prefixWord ++ tailWord_336523) baseStart_336523 baseEnd_336523 := by
    simpa [prefixWord, tailWord_336523, baseEnd_336523] using wordTrace_append hprefix tailTrace_336523
  have hstable : (prefixWord ++ tailWord_336523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336523).length < 2 ^ (prefixWord ++ tailWord_336523).sum := by decide
  have hdescent : baseEnd_336523 < baseStart_336523 := by decide
  rcases family_descends (prefixWord ++ tailWord_336523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336600 : List Nat := [2, 1, 2, 2, 3, 2, 2, 8]
def baseStart_336600 : Nat := 118140960795 + 336600 * 2 ^ 59
def prefixEnd_336600 : Nat := 4983230072969 + 3 ^ 40 * 336600 * 2
def baseEnd_336600 : Nat := 12802784318776909974223

theorem tailTrace_336600 : CollatzResearch.WordTrace tailWord_336600 prefixEnd_336600 12802784318776909974223 := by
  unfold tailWord_336600
  simp only [CollatzResearch.WordTrace]
  refine ⟨6138405290281580774179627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8184540387042107698906169 6138405290281580774179627)
  ·
    refine ⟨9207607935422371161269441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6138405290281580774179627 9207607935422371161269441)
    ·
      refine ⟨6905705951566778370952081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9207607935422371161269441 6905705951566778370952081)
      ·
        refine ⟨5179279463675083778214061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6905705951566778370952081 5179279463675083778214061)
        ·
          refine ⟨1942229798878156416830273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5179279463675083778214061 1942229798878156416830273)
          ·
            refine ⟨1456672349158617312622705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1942229798878156416830273 1456672349158617312622705)
            ·
              refine ⟨1092504261868962984467029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1456672349158617312622705 1092504261868962984467029)
              ·
                refine ⟨12802784318776909974223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1092504261868962984467029 12802784318776909974223)
                ·
                  rfl

theorem cell22_336600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 8].length) (baseStart_336600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336600 prefixEnd_336600 := by exact prefixLift 336600
  have htrace : WordTrace (prefixWord ++ tailWord_336600) baseStart_336600 baseEnd_336600 := by
    simpa [prefixWord, tailWord_336600, baseEnd_336600] using wordTrace_append hprefix tailTrace_336600
  have hstable : (prefixWord ++ tailWord_336600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336600).length < 2 ^ (prefixWord ++ tailWord_336600).sum := by decide
  have hdescent : baseEnd_336600 < baseStart_336600 := by decide
  rcases family_descends (prefixWord ++ tailWord_336600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336602 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_336602 : Nat := 118140960795 + 336602 * 2 ^ 59
def prefixEnd_336602 : Nat := 4983230072969 + 3 ^ 40 * 336602 * 2
def baseEnd_336602 : Nat := 115225743509864851218001

theorem tailTrace_336602 : CollatzResearch.WordTrace tailWord_336602 prefixEnd_336602 115225743509864851218001 := by
  unfold tailWord_336602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3069220881638978972483015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8184589017703943926621373 3069220881638978972483015)
  ·
    refine ⟨4603831322458468458724523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3069220881638978972483015 4603831322458468458724523)
    ·
      refine ⟨6905746983687702688086785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4603831322458468458724523 6905746983687702688086785)
      ·
        refine ⟨5179310237765777016065089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6905746983687702688086785 5179310237765777016065089)
        ·
          refine ⟨3884482678324332762048817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5179310237765777016065089 3884482678324332762048817)
          ·
            refine ⟨2913362008743249571536613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3884482678324332762048817 2913362008743249571536613)
            ·
              refine ⟨546255376639359294663115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2913362008743249571536613 546255376639359294663115)
              ·
                refine ⟨819383064959038941994673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546255376639359294663115 819383064959038941994673)
                ·
                  refine ⟨614537298719279206496005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 819383064959038941994673 614537298719279206496005)
                  ·
                    refine ⟨115225743509864851218001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 614537298719279206496005 115225743509864851218001)
                    ·
                      rfl

theorem cell22_336602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_336602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336602 prefixEnd_336602 := by exact prefixLift 336602
  have htrace : WordTrace (prefixWord ++ tailWord_336602) baseStart_336602 baseEnd_336602 := by
    simpa [prefixWord, tailWord_336602, baseEnd_336602] using wordTrace_append hprefix tailTrace_336602
  have hstable : (prefixWord ++ tailWord_336602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336602).length < 2 ^ (prefixWord ++ tailWord_336602).sum := by decide
  have hdescent : baseEnd_336602 < baseStart_336602 := by decide
  rcases family_descends (prefixWord ++ tailWord_336602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336604 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_336604 : Nat := 118140960795 + 336604 * 2 ^ 59
def prefixEnd_336604 : Nat := 4983230072969 + 3 ^ 40 * 336604 * 2
def baseEnd_336604 : Nat := 115226428150737512667995

theorem tailTrace_336604 : CollatzResearch.WordTrace tailWord_336604 prefixEnd_336604 115226428150737512667995 := by
  unfold tailWord_336604
  simp only [CollatzResearch.WordTrace]
  refine ⟨6138478236274335115752433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8184637648365780154336577 6138478236274335115752433)
  ·
    refine ⟨4603858677205751336814325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6138478236274335115752433 4603858677205751336814325)
    ·
      refine ⟨431611750988039187826343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4603858677205751336814325 431611750988039187826343)
      ·
        refine ⟨647417626482058781739515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431611750988039187826343 647417626482058781739515)
        ·
          refine ⟨971126439723088172609273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647417626482058781739515 971126439723088172609273)
          ·
            refine ⟨728344829792316129456955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 971126439723088172609273 728344829792316129456955)
            ·
              refine ⟨1092517244688474194185433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728344829792316129456955 1092517244688474194185433)
              ·
                refine ⟨819387933516355645639075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1092517244688474194185433 819387933516355645639075)
                ·
                  refine ⟨1229081900274533468458613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 819387933516355645639075 1229081900274533468458613)
                  ·
                    refine ⟨115226428150737512667995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1229081900274533468458613 115226428150737512667995)
                    ·
                      rfl

theorem cell22_336604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_336604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336604 prefixEnd_336604 := by exact prefixLift 336604
  have htrace : WordTrace (prefixWord ++ tailWord_336604) baseStart_336604 baseEnd_336604 := by
    simpa [prefixWord, tailWord_336604, baseEnd_336604] using wordTrace_append hprefix tailTrace_336604
  have hstable : (prefixWord ++ tailWord_336604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336604).length < 2 ^ (prefixWord ++ tailWord_336604).sum := by decide
  have hdescent : baseEnd_336604 < baseStart_336604 := by decide
  rcases family_descends (prefixWord ++ tailWord_336604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336632 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 3, 3]
def baseStart_336632 : Nat := 118140960795 + 336632 * 2 ^ 59
def prefixEnd_336632 : Nat := 4983230072969 + 3 ^ 40 * 336632 * 2
def baseEnd_336632 : Nat := 115236013122954772967909

theorem tailTrace_336632 : CollatzResearch.WordTrace tailWord_336632 prefixEnd_336632 115236013122954772967909 := by
  unfold tailWord_336632
  simp only [CollatzResearch.WordTrace]
  refine ⟨6138988858223615506762075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8185318477631487342349433 6138988858223615506762075)
  ·
    refine ⟨9208483287335423260143113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6138988858223615506762075 9208483287335423260143113)
    ·
      refine ⟨6906362465501567445107335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9208483287335423260143113 6906362465501567445107335)
      ·
        refine ⟨10359543698252351167661003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6906362465501567445107335 10359543698252351167661003)
        ·
          refine ⟨15539315547378526751491505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10359543698252351167661003 15539315547378526751491505)
          ·
            refine ⟨11654486660533895063618629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15539315547378526751491505 11654486660533895063618629)
            ·
              refine ⟨2185216248850105324428493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11654486660533895063618629 2185216248850105324428493)
              ·
                refine ⟨819456093318789496660685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2185216248850105324428493 819456093318789496660685)
                ·
                  refine ⟨307296034994546061247757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819456093318789496660685 307296034994546061247757)
                  ·
                    refine ⟨115236013122954772967909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 307296034994546061247757 115236013122954772967909)
                    ·
                      rfl

theorem cell22_336632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_336632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336632 prefixEnd_336632 := by exact prefixLift 336632
  have htrace : WordTrace (prefixWord ++ tailWord_336632) baseStart_336632 baseEnd_336632 := by
    simpa [prefixWord, tailWord_336632, baseEnd_336632] using wordTrace_append hprefix tailTrace_336632
  have hstable : (prefixWord ++ tailWord_336632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336632).length < 2 ^ (prefixWord ++ tailWord_336632).sum := by decide
  have hdescent : baseEnd_336632 < baseStart_336632 := by decide
  rcases family_descends (prefixWord ++ tailWord_336632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336666 : List Nat := [3, 1, 1, 3, 2, 1, 4, 3, 1, 3]
def baseStart_336666 : Nat := 118140960795 + 336666 * 2 ^ 59
def prefixEnd_336666 : Nat := 4983230072969 + 3 ^ 40 * 336666 * 2
def baseEnd_336666 : Nat := 115247652017790017617805

theorem tailTrace_336666 : CollatzResearch.WordTrace tailWord_336666 prefixEnd_336666 115247652017790017617805 := by
  unfold tailWord_336666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3069804449581013705065463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8186145198882703213507901 3069804449581013705065463)
  ·
    refine ⟨4604706674371520557598195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3069804449581013705065463 4604706674371520557598195)
    ·
      refine ⟨6907060011557280836397293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4604706674371520557598195 6907060011557280836397293)
      ·
        refine ⟨2590147504333980313648985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6907060011557280836397293 2590147504333980313648985)
        ·
          refine ⟨1942610628250485235236739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2590147504333980313648985 1942610628250485235236739)
          ·
            refine ⟨2913915942375727852855109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1942610628250485235236739 2913915942375727852855109)
            ·
              refine ⟨546359239195448972410333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2913915942375727852855109 546359239195448972410333)
              ·
                refine ⟨204884714698293364653875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 546359239195448972410333 204884714698293364653875)
                ·
                  refine ⟨307327072047440046980813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204884714698293364653875 307327072047440046980813)
                  ·
                    refine ⟨115247652017790017617805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 307327072047440046980813 115247652017790017617805)
                    ·
                      rfl

theorem cell22_336666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_336666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336666 prefixEnd_336666 := by exact prefixLift 336666
  have htrace : WordTrace (prefixWord ++ tailWord_336666) baseStart_336666 baseEnd_336666 := by
    simpa [prefixWord, tailWord_336666, baseEnd_336666] using wordTrace_append hprefix tailTrace_336666
  have hstable : (prefixWord ++ tailWord_336666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336666).length < 2 ^ (prefixWord ++ tailWord_336666).sum := by decide
  have hdescent : baseEnd_336666 < baseStart_336666 := by decide
  rcases family_descends (prefixWord ++ tailWord_336666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336717 : List Nat := [1, 6, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_336717 : Nat := 118140960795 + 336717 * 2 ^ 59
def prefixEnd_336717 : Nat := 4983230072969 + 3 ^ 40 * 336717 * 2
def baseEnd_336717 : Nat := 115265110360042884592649

theorem tailTrace_336717 : CollatzResearch.WordTrace tailWord_336717 prefixEnd_336717 115265110360042884592649 := by
  unfold tailWord_336717
  simp only [CollatzResearch.WordTrace]
  refine ⟨12281077921139290530368405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8187385280759527020245603 12281077921139290530368405)
  ·
    refine ⟨575675527553404243611019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12281077921139290530368405 575675527553404243611019)
    ·
      refine ⟨863513291330106365416529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575675527553404243611019 863513291330106365416529)
      ·
        refine ⟨647634968497579774062397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 863513291330106365416529 647634968497579774062397)
        ·
          refine ⟨242863113186592415273399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 647634968497579774062397 242863113186592415273399)
          ·
            refine ⟨364294669779888622910099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242863113186592415273399 364294669779888622910099)
            ·
              refine ⟨546442004669832934365149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364294669779888622910099 546442004669832934365149)
              ·
                refine ⟨204915751751187350386931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 546442004669832934365149 204915751751187350386931)
                ·
                  refine ⟨307373627626781025580397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204915751751187350386931 307373627626781025580397)
                  ·
                    refine ⟨115265110360042884592649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 307373627626781025580397 115265110360042884592649)
                    ·
                      rfl

theorem cell22_336717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_336717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336717 prefixEnd_336717 := by exact prefixLift 336717
  have htrace : WordTrace (prefixWord ++ tailWord_336717) baseStart_336717 baseEnd_336717 := by
    simpa [prefixWord, tailWord_336717, baseEnd_336717] using wordTrace_append hprefix tailTrace_336717
  have hstable : (prefixWord ++ tailWord_336717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336717).length < 2 ^ (prefixWord ++ tailWord_336717).sum := by decide
  have hdescent : baseEnd_336717 < baseStart_336717 := by decide
  rcases family_descends (prefixWord ++ tailWord_336717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336722 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_336722 : Nat := 118140960795 + 336722 * 2 ^ 59
def prefixEnd_336722 : Nat := 4983230072969 + 3 ^ 40 * 336722 * 2
def baseEnd_336722 : Nat := 115266821962224538217633

theorem tailTrace_336722 : CollatzResearch.WordTrace tailWord_336722 prefixEnd_336722 115266821962224538217633 := by
  unfold tailWord_336722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3070315071530294096075105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8187506857414117589533613 3070315071530294096075105)
  ·
    refine ⟨2302736303647720572056329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3070315071530294096075105 2302736303647720572056329)
    ·
      refine ⟨1727052227735790429042247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2302736303647720572056329 1727052227735790429042247)
      ·
        refine ⟨2590578341603685643563371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1727052227735790429042247 2590578341603685643563371)
        ·
          refine ⟨3885867512405528465345057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590578341603685643563371 3885867512405528465345057)
          ·
            refine ⟨2914400634304146349008793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3885867512405528465345057 2914400634304146349008793)
            ·
              refine ⟨2185800475728109761756595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2914400634304146349008793 2185800475728109761756595)
              ·
                refine ⟨3278700713592164642634893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185800475728109761756595 3278700713592164642634893)
                ·
                  refine ⟨1229512767597061740988085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3278700713592164642634893 1229512767597061740988085)
                  ·
                    refine ⟨115266821962224538217633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1229512767597061740988085 115266821962224538217633)
                    ·
                      rfl

theorem cell22_336722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_336722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336722 prefixEnd_336722 := by exact prefixLift 336722
  have htrace : WordTrace (prefixWord ++ tailWord_336722) baseStart_336722 baseEnd_336722 := by
    simpa [prefixWord, tailWord_336722, baseEnd_336722] using wordTrace_append hprefix tailTrace_336722
  have hstable : (prefixWord ++ tailWord_336722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336722).length < 2 ^ (prefixWord ++ tailWord_336722).sum := by decide
  have hdescent : baseEnd_336722 < baseStart_336722 := by decide
  rcases family_descends (prefixWord ++ tailWord_336722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336739 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 4, 3]
def baseStart_336739 : Nat := 118140960795 + 336739 * 2 ^ 59
def prefixEnd_336739 : Nat := 4983230072969 + 3 ^ 40 * 336739 * 2
def baseEnd_336739 : Nat := 115272641409642160542581

theorem tailTrace_336739 : CollatzResearch.WordTrace tailWord_336739 prefixEnd_336739 115272641409642160542581 := by
  unfold tailWord_336739
  simp only [CollatzResearch.WordTrace]
  refine ⟨12281880327059588287669271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8187920218039725525112847 12281880327059588287669271)
  ·
    refine ⟨18422820490589382431503907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12281880327059588287669271 18422820490589382431503907)
    ·
      refine ⟨27634230735884073647255861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18422820490589382431503907 27634230735884073647255861)
      ·
        refine ⟨2590709131489131904430237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27634230735884073647255861 2590709131489131904430237)
        ·
          refine ⟨971515924308424464161339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2590709131489131904430237 971515924308424464161339)
          ·
            refine ⟨1457273886462636696242009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971515924308424464161339 1457273886462636696242009)
            ·
              refine ⟨1092955414846977522181507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1457273886462636696242009 1092955414846977522181507)
              ·
                refine ⟨1639433122270466283272261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1092955414846977522181507 1639433122270466283272261)
                ·
                  refine ⟨307393710425712428113549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1639433122270466283272261 307393710425712428113549)
                  ·
                    refine ⟨115272641409642160542581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 307393710425712428113549 115272641409642160542581)
                    ·
                      rfl

theorem cell22_336739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 3].length) (baseStart_336739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336739 prefixEnd_336739 := by exact prefixLift 336739
  have htrace : WordTrace (prefixWord ++ tailWord_336739) baseStart_336739 baseEnd_336739 := by
    simpa [prefixWord, tailWord_336739, baseEnd_336739] using wordTrace_append hprefix tailTrace_336739
  have hstable : (prefixWord ++ tailWord_336739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336739).length < 2 ^ (prefixWord ++ tailWord_336739).sum := by decide
  have hdescent : baseEnd_336739 < baseStart_336739 := by decide
  rcases family_descends (prefixWord ++ tailWord_336739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336790 : List Nat := [5, 3, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_336790 : Nat := 118140960795 + 336790 * 2 ^ 59
def prefixEnd_336790 : Nat := 4983230072969 + 3 ^ 40 * 336790 * 2
def baseEnd_336790 : Nat := 115290099751895027517425

theorem tailTrace_336790 : CollatzResearch.WordTrace tailWord_336790 prefixEnd_336790 115290099751895027517425 := by
  unfold tailWord_336790
  simp only [CollatzResearch.WordTrace]
  refine ⟨767733778117176499860989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8189160299916549331850549 767733778117176499860989)
  ·
    refine ⟨287900166793941187447871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 767733778117176499860989 287900166793941187447871)
    ·
      refine ⟨431850250190911781171807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287900166793941187447871 431850250190911781171807)
      ·
        refine ⟨647775375286367671757711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431850250190911781171807 647775375286367671757711)
        ·
          refine ⟨971663062929551507636567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647775375286367671757711 971663062929551507636567)
          ·
            refine ⟨1457494594394327261454851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971663062929551507636567 1457494594394327261454851)
            ·
              refine ⟨2186241891591490892182277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457494594394327261454851 2186241891591490892182277)
              ·
                refine ⟨409920354673404542284177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2186241891591490892182277 409920354673404542284177)
                ·
                  refine ⟨307440266005053406713133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409920354673404542284177 307440266005053406713133)
                  ·
                    refine ⟨115290099751895027517425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 307440266005053406713133 115290099751895027517425)
                    ·
                      rfl

theorem cell22_336790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_336790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336790 prefixEnd_336790 := by exact prefixLift 336790
  have htrace : WordTrace (prefixWord ++ tailWord_336790) baseStart_336790 baseEnd_336790 := by
    simpa [prefixWord, tailWord_336790, baseEnd_336790] using wordTrace_append hprefix tailTrace_336790
  have hstable : (prefixWord ++ tailWord_336790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336790).length < 2 ^ (prefixWord ++ tailWord_336790).sum := by decide
  have hdescent : baseEnd_336790 < baseStart_336790 := by decide
  rcases family_descends (prefixWord ++ tailWord_336790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336812 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_336812 : Nat := 118140960795 + 336812 * 2 ^ 59
def prefixEnd_336812 : Nat := 4983230072969 + 3 ^ 40 * 336812 * 2
def baseEnd_336812 : Nat := 115297630801494303467357

theorem tailTrace_336812 : CollatzResearch.WordTrace tailWord_336812 prefixEnd_336812 115297630801494303467357 := by
  unfold tailWord_336812
  simp only [CollatzResearch.WordTrace]
  refine ⟨6142271427897560877538345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8189695237196747836717793 6142271427897560877538345)
  ·
    refine ⟨4606703570923170658153759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6142271427897560877538345 4606703570923170658153759)
    ·
      refine ⟨6910055356384755987230639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4606703570923170658153759 6910055356384755987230639)
      ·
        refine ⟨10365083034577133980845959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6910055356384755987230639 10365083034577133980845959)
        ·
          refine ⟨15547624551865700971268939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10365083034577133980845959 15547624551865700971268939)
          ·
            refine ⟨23321436827798551456903409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15547624551865700971268939 23321436827798551456903409)
            ·
              refine ⟨17491077620848913592677557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23321436827798551456903409 17491077620848913592677557)
              ·
                refine ⟨1639788526954585649313521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17491077620848913592677557 1639788526954585649313521)
                ·
                  refine ⟨1229841395215939236985141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1639788526954585649313521 1229841395215939236985141)
                  ·
                    refine ⟨115297630801494303467357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1229841395215939236985141 115297630801494303467357)
                    ·
                      rfl

theorem cell22_336812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_336812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336812 prefixEnd_336812 := by exact prefixLift 336812
  have htrace : WordTrace (prefixWord ++ tailWord_336812) baseStart_336812 baseEnd_336812 := by
    simpa [prefixWord, tailWord_336812, baseEnd_336812] using wordTrace_append hprefix tailTrace_336812
  have hstable : (prefixWord ++ tailWord_336812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336812).length < 2 ^ (prefixWord ++ tailWord_336812).sum := by decide
  have hdescent : baseEnd_336812 < baseStart_336812 := by decide
  rcases family_descends (prefixWord ++ tailWord_336812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336822 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_336822 : Nat := 118140960795 + 336822 * 2 ^ 59
def prefixEnd_336822 : Nat := 4983230072969 + 3 ^ 40 * 336822 * 2
def baseEnd_336822 : Nat := 115301054005857610717327

theorem tailTrace_336822 : CollatzResearch.WordTrace tailWord_336822 prefixEnd_336822 115301054005857610717327 := by
  unfold tailWord_336822
  simp only [CollatzResearch.WordTrace]
  refine ⟨767806724109930841433795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8189938390505928975293813 767806724109930841433795)
  ·
    refine ⟨1151710086164896262150693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 767806724109930841433795 1151710086164896262150693)
    ·
      refine ⟨215945641155918049153255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1151710086164896262150693 215945641155918049153255)
      ·
        refine ⟨323918461733877073729883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215945641155918049153255 323918461733877073729883)
        ·
          refine ⟨485877692600815610594825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323918461733877073729883 485877692600815610594825)
          ·
            refine ⟨364408269450611707946119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 485877692600815610594825 364408269450611707946119)
            ·
              refine ⟨546612404175917561919179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364408269450611707946119 546612404175917561919179)
              ·
                refine ⟨819918606263876342878769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546612404175917561919179 819918606263876342878769)
                ·
                  refine ⟨614938954697907257159077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 819918606263876342878769 614938954697907257159077)
                  ·
                    refine ⟨115301054005857610717327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 614938954697907257159077 115301054005857610717327)
                    ·
                      rfl

theorem cell22_336822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_336822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336822 prefixEnd_336822 := by exact prefixLift 336822
  have htrace : WordTrace (prefixWord ++ tailWord_336822) baseStart_336822 baseEnd_336822 := by
    simpa [prefixWord, tailWord_336822, baseEnd_336822] using wordTrace_append hprefix tailTrace_336822
  have hstable : (prefixWord ++ tailWord_336822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336822).length < 2 ^ (prefixWord ++ tailWord_336822).sum := by decide
  have hdescent : baseEnd_336822 < baseStart_336822 := by decide
  rcases family_descends (prefixWord ++ tailWord_336822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336827 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 7, 4]
def baseStart_336827 : Nat := 118140960795 + 336827 * 2 ^ 59
def prefixEnd_336827 : Nat := 4983230072969 + 3 ^ 40 * 336827 * 2
def baseEnd_336827 : Nat := 115302765608039264342311

theorem tailTrace_336827 : CollatzResearch.WordTrace tailWord_336827 prefixEnd_336827 115302765608039264342311 := by
  unfold tailWord_336827
  simp only [CollatzResearch.WordTrace]
  refine ⟨12285089950740779316872735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8190059967160519544581823 12285089950740779316872735)
  ·
    refine ⟨18427634926111168975309103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12285089950740779316872735 18427634926111168975309103)
    ·
      refine ⟨27641452389166753462963655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18427634926111168975309103 27641452389166753462963655)
      ·
        refine ⟨41462178583750130194445483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27641452389166753462963655 41462178583750130194445483)
        ·
          refine ⟨62193267875625195291668225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41462178583750130194445483 62193267875625195291668225)
          ·
            refine ⟨46644950906718896468751169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62193267875625195291668225 46644950906718896468751169)
            ·
              refine ⟨34983713180039172351563377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46644950906718896468751169 34983713180039172351563377)
              ·
                refine ⟨26237784885029379263672533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34983713180039172351563377 26237784885029379263672533)
                ·
                  refine ⟨614948083242876076492325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 26237784885029379263672533 614948083242876076492325)
                  ·
                    refine ⟨115302765608039264342311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 614948083242876076492325 115302765608039264342311)
                    ·
                      rfl

theorem cell22_336827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 4].length) (baseStart_336827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336827 prefixEnd_336827 := by exact prefixLift 336827
  have htrace : WordTrace (prefixWord ++ tailWord_336827) baseStart_336827 baseEnd_336827 := by
    simpa [prefixWord, tailWord_336827, baseEnd_336827] using wordTrace_append hprefix tailTrace_336827
  have hstable : (prefixWord ++ tailWord_336827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336827).length < 2 ^ (prefixWord ++ tailWord_336827).sum := by decide
  have hdescent : baseEnd_336827 < baseStart_336827 := by decide
  rcases family_descends (prefixWord ++ tailWord_336827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336842 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 10]
def baseStart_336842 : Nat := 118140960795 + 336842 * 2 ^ 59
def prefixEnd_336842 : Nat := 4983230072969 + 3 ^ 40 * 336842 * 2
def baseEnd_336842 : Nat := 38435966804861408405755

theorem tailTrace_336842 : CollatzResearch.WordTrace tailWord_336842 prefixEnd_336842 38435966804861408405755 := by
  unfold tailWord_336842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3071409261421609219667195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8190424697124291252445853 3071409261421609219667195)
  ·
    refine ⟨4607113892132413829500793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3071409261421609219667195 4607113892132413829500793)
    ·
      refine ⟨3455335419099310372125595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4607113892132413829500793 3455335419099310372125595)
      ·
        refine ⟨5183003128648965558188393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3455335419099310372125595 5183003128648965558188393)
        ·
          refine ⟨3887252346486724168641295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5183003128648965558188393 3887252346486724168641295)
          ·
            refine ⟨5830878519730086252961943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3887252346486724168641295 5830878519730086252961943)
            ·
              refine ⟨8746317779595129379442915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5830878519730086252961943 8746317779595129379442915)
              ·
                refine ⟨13119476669392694069164373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8746317779595129379442915 13119476669392694069164373)
                ·
                  refine ⟨38435966804861408405755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 13119476669392694069164373 38435966804861408405755)
                  ·
                    rfl

theorem cell22_336842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_336842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336842 prefixEnd_336842 := by exact prefixLift 336842
  have htrace : WordTrace (prefixWord ++ tailWord_336842) baseStart_336842 baseEnd_336842 := by
    simpa [prefixWord, tailWord_336842, baseEnd_336842] using wordTrace_append hprefix tailTrace_336842
  have hstable : (prefixWord ++ tailWord_336842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336842).length < 2 ^ (prefixWord ++ tailWord_336842).sum := by decide
  have hdescent : baseEnd_336842 < baseStart_336842 := by decide
  rcases family_descends (prefixWord ++ tailWord_336842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336878 : List Nat := [4, 1, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_336878 : Nat := 118140960795 + 336878 * 2 ^ 59
def prefixEnd_336878 : Nat := 4983230072969 + 3 ^ 40 * 336878 * 2
def baseEnd_336878 : Nat := 115320223950292131317155

theorem tailTrace_336878 : CollatzResearch.WordTrace tailWord_336878 prefixEnd_336878 115320223950292131317155 := by
  unfold tailWord_336878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1535868759194501878372411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8191300049037343351319525 1535868759194501878372411)
  ·
    refine ⟨2303803138791752817558617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1535868759194501878372411 2303803138791752817558617)
    ·
      refine ⟨1727852354093814613168963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2303803138791752817558617 1727852354093814613168963)
      ·
        refine ⟨2591778531140721919753445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1727852354093814613168963 2591778531140721919753445)
        ·
          refine ⟨485958474588885359953771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2591778531140721919753445 485958474588885359953771)
          ·
            refine ⟨728937711883328039930657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485958474588885359953771 728937711883328039930657)
            ·
              refine ⟨546703283912496029947993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 728937711883328039930657 546703283912496029947993)
              ·
                refine ⟨410027462934372022460995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546703283912496029947993 410027462934372022460995)
                ·
                  refine ⟨615041194401558033691493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410027462934372022460995 615041194401558033691493)
                  ·
                    refine ⟨115320223950292131317155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 615041194401558033691493 115320223950292131317155)
                    ·
                      rfl

theorem cell22_336878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_336878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336878 prefixEnd_336878 := by exact prefixLift 336878
  have htrace : WordTrace (prefixWord ++ tailWord_336878) baseStart_336878 baseEnd_336878 := by
    simpa [prefixWord, tailWord_336878, baseEnd_336878] using wordTrace_append hprefix tailTrace_336878
  have hstable : (prefixWord ++ tailWord_336878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336878).length < 2 ^ (prefixWord ++ tailWord_336878).sum := by decide
  have hdescent : baseEnd_336878 < baseStart_336878 := by decide
  rcases family_descends (prefixWord ++ tailWord_336878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336889 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 2, 4]
def baseStart_336889 : Nat := 118140960795 + 336889 * 2 ^ 59
def prefixEnd_336889 : Nat := 4983230072969 + 3 ^ 40 * 336889 * 2
def baseEnd_336889 : Nat := 115323989475091769292121

theorem tailTrace_336889 : CollatzResearch.WordTrace tailWord_336889 prefixEnd_336889 115323989475091769292121 := by
  unfold tailWord_336889
  simp only [CollatzResearch.WordTrace]
  refine ⟨12287351276516163905629721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8191567517677442603753147 12287351276516163905629721)
  ·
    refine ⟨9215513457387122929222291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12287351276516163905629721 9215513457387122929222291)
    ·
      refine ⟨13823270186080684393833437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9215513457387122929222291 13823270186080684393833437)
      ·
        refine ⟨5183726319780256647687539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13823270186080684393833437 5183726319780256647687539)
        ·
          refine ⟨7775589479670384971531309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5183726319780256647687539 7775589479670384971531309)
          ·
            refine ⟨2915846054876394364324241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7775589479670384971531309 2915846054876394364324241)
            ·
              refine ⟨2186884541157295773243181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2915846054876394364324241 2186884541157295773243181)
              ·
                refine ⟨820081702933985914966193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2186884541157295773243181 820081702933985914966193)
                ·
                  refine ⟨615061277200489436224645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 820081702933985914966193 615061277200489436224645)
                  ·
                    refine ⟨115323989475091769292121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 615061277200489436224645 115323989475091769292121)
                    ·
                      rfl

theorem cell22_336889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_336889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336889 prefixEnd_336889 := by exact prefixLift 336889
  have htrace : WordTrace (prefixWord ++ tailWord_336889) baseStart_336889 baseEnd_336889 := by
    simpa [prefixWord, tailWord_336889, baseEnd_336889] using wordTrace_append hprefix tailTrace_336889
  have hstable : (prefixWord ++ tailWord_336889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336889).length < 2 ^ (prefixWord ++ tailWord_336889).sum := by decide
  have hdescent : baseEnd_336889 < baseStart_336889 := by decide
  rcases family_descends (prefixWord ++ tailWord_336889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336904 : List Nat := [2, 1, 3, 2, 1, 5, 8]
def baseStart_336904 : Nat := 118140960795 + 336904 * 2 ^ 59
def prefixEnd_336904 : Nat := 4983230072969 + 3 ^ 40 * 336904 * 2
def baseEnd_336904 : Nat := 4271449047468027043225

theorem tailTrace_336904 : CollatzResearch.WordTrace tailWord_336904 prefixEnd_336904 4271449047468027043225 := by
  unfold tailWord_336904
  simp only [CollatzResearch.WordTrace]
  refine ⟨6143949185730910733712883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8191932247641214311617177 6143949185730910733712883)
  ·
    refine ⟨9215923778596366100569325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6143949185730910733712883 9215923778596366100569325)
    ·
      refine ⟨3455971416973637287713497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9215923778596366100569325 3455971416973637287713497)
      ·
        refine ⟨2591978562730227965785123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3455971416973637287713497 2591978562730227965785123)
        ·
          refine ⟨3887967844095341948677685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591978562730227965785123 3887967844095341948677685)
          ·
            refine ⟨364496985383938307688533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3887967844095341948677685 364496985383938307688533)
            ·
              refine ⟨4271449047468027043225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 364496985383938307688533 4271449047468027043225)
              ·
                rfl

theorem cell22_336904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 8].length) (baseStart_336904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336904 prefixEnd_336904 := by exact prefixLift 336904
  have htrace : WordTrace (prefixWord ++ tailWord_336904) baseStart_336904 baseEnd_336904 := by
    simpa [prefixWord, tailWord_336904, baseEnd_336904] using wordTrace_append hprefix tailTrace_336904
  have hstable : (prefixWord ++ tailWord_336904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336904).length < 2 ^ (prefixWord ++ tailWord_336904).sum := by decide
  have hdescent : baseEnd_336904 < baseStart_336904 := by decide
  rcases family_descends (prefixWord ++ tailWord_336904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336906 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_336906 : Nat := 118140960795 + 336906 * 2 ^ 59
def prefixEnd_336906 : Nat := 4983230072969 + 3 ^ 40 * 336906 * 2
def baseEnd_336906 : Nat := 115329808922509391617069

theorem tailTrace_336906 : CollatzResearch.WordTrace tailWord_336906 prefixEnd_336906 115329808922509391617069 := by
  unfold tailWord_336906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3071992829363643952249643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8191980878303050539332381 3071992829363643952249643)
  ·
    refine ⟨4607989244045465928374465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3071992829363643952249643 4607989244045465928374465)
    ·
      refine ⟨3455991933034099446280849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4607989244045465928374465 3455991933034099446280849)
      ·
        refine ⟨2591993949775574584710637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3455991933034099446280849 2591993949775574584710637)
        ·
          refine ⟨971997731165840469266489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2591993949775574584710637 971997731165840469266489)
          ·
            refine ⟨728998298374380351949867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 971997731165840469266489 728998298374380351949867)
            ·
              refine ⟨1093497447561570527924801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728998298374380351949867 1093497447561570527924801)
              ·
                refine ⟨820123085671177895943601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1093497447561570527924801 820123085671177895943601)
                ·
                  refine ⟨615092314253383421957701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 820123085671177895943601 615092314253383421957701)
                  ·
                    refine ⟨115329808922509391617069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 615092314253383421957701 115329808922509391617069)
                    ·
                      rfl

theorem cell22_336906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_336906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336906 prefixEnd_336906 := by exact prefixLift 336906
  have htrace : WordTrace (prefixWord ++ tailWord_336906) baseStart_336906 baseEnd_336906 := by
    simpa [prefixWord, tailWord_336906, baseEnd_336906] using wordTrace_append hprefix tailTrace_336906
  have hstable : (prefixWord ++ tailWord_336906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336906).length < 2 ^ (prefixWord ++ tailWord_336906).sum := by decide
  have hdescent : baseEnd_336906 < baseStart_336906 := by decide
  rcases family_descends (prefixWord ++ tailWord_336906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336970 : List Nat := [3, 1, 2, 1, 1, 2, 6, 2, 1, 3]
def baseStart_336970 : Nat := 118140960795 + 336970 * 2 ^ 59
def prefixEnd_336970 : Nat := 4983230072969 + 3 ^ 40 * 336970 * 2
def baseEnd_336970 : Nat := 115351717430434558016873

theorem tailTrace_336970 : CollatzResearch.WordTrace tailWord_336970 prefixEnd_336970 115351717430434558016873 := by
  unfold tailWord_336970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3072576397305678684832091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8193537059481809826218909 3072576397305678684832091)
  ·
    refine ⟨4608864595958518027248137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3072576397305678684832091 4608864595958518027248137)
    ·
      refine ⟨3456648446968888520436103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4608864595958518027248137 3456648446968888520436103)
      ·
        refine ⟨5184972670453332780654155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3456648446968888520436103 5184972670453332780654155)
        ·
          refine ⟨7777459005679999170981233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5184972670453332780654155 7777459005679999170981233)
          ·
            refine ⟨5833094254259999378235925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7777459005679999170981233 5833094254259999378235925)
            ·
              refine ⟨273426293168437470854809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5833094254259999378235925 273426293168437470854809)
              ·
                refine ⟨205069719876328103141107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273426293168437470854809 205069719876328103141107)
                ·
                  refine ⟨307604579814492154711661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205069719876328103141107 307604579814492154711661)
                  ·
                    refine ⟨115351717430434558016873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 307604579814492154711661 115351717430434558016873)
                    ·
                      rfl

theorem cell22_336970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_336970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336970 prefixEnd_336970 := by exact prefixLift 336970
  have htrace : WordTrace (prefixWord ++ tailWord_336970) baseStart_336970 baseEnd_336970 := by
    simpa [prefixWord, tailWord_336970, baseEnd_336970] using wordTrace_append hprefix tailTrace_336970
  have hstable : (prefixWord ++ tailWord_336970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336970).length < 2 ^ (prefixWord ++ tailWord_336970).sum := by decide
  have hdescent : baseEnd_336970 < baseStart_336970 := by decide
  rcases family_descends (prefixWord ++ tailWord_336970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336979 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 3, 4]
def baseStart_336979 : Nat := 118140960795 + 336979 * 2 ^ 59
def prefixEnd_336979 : Nat := 4983230072969 + 3 ^ 40 * 336979 * 2
def baseEnd_336979 : Nat := 115354798314361534541845

theorem tailTrace_336979 : CollatzResearch.WordTrace tailWord_336979 prefixEnd_336979 115354798314361534541845 := by
  unfold tailWord_336979
  simp only [CollatzResearch.WordTrace]
  refine ⟨12290633846190109276405991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8193755897460072850937327 12290633846190109276405991)
  ·
    refine ⟨18435950769285163914608987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12290633846190109276405991 18435950769285163914608987)
    ·
      refine ⟨27653926153927745871913481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18435950769285163914608987 27653926153927745871913481)
      ·
        refine ⟨20740444615445809403935111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27653926153927745871913481 20740444615445809403935111)
        ·
          refine ⟨31110666923168714105902667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20740444615445809403935111 31110666923168714105902667)
          ·
            refine ⟨46666000384753071158854001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31110666923168714105902667 46666000384753071158854001)
            ·
              refine ⟨34999500288564803369140501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46666000384753071158854001 34999500288564803369140501)
              ·
                refine ⟨1640601576026475157928461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34999500288564803369140501 1640601576026475157928461)
                ·
                  refine ⟨615225591009928184223173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1640601576026475157928461 615225591009928184223173)
                  ·
                    refine ⟨115354798314361534541845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 615225591009928184223173 115354798314361534541845)
                    ·
                      rfl

theorem cell22_336979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 4].length) (baseStart_336979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336979 prefixEnd_336979 := by exact prefixLift 336979
  have htrace : WordTrace (prefixWord ++ tailWord_336979) baseStart_336979 baseEnd_336979 := by
    simpa [prefixWord, tailWord_336979, baseEnd_336979] using wordTrace_append hprefix tailTrace_336979
  have hstable : (prefixWord ++ tailWord_336979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336979).length < 2 ^ (prefixWord ++ tailWord_336979).sum := by decide
  have hdescent : baseEnd_336979 < baseStart_336979 := by decide
  rcases family_descends (prefixWord ++ tailWord_336979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336996 : List Nat := [2, 3, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_336996 : Nat := 118140960795 + 336996 * 2 ^ 59
def prefixEnd_336996 : Nat := 4983230072969 + 3 ^ 40 * 336996 * 2
def baseEnd_336996 : Nat := 115360617761779156866793

theorem tailTrace_336996 : CollatzResearch.WordTrace tailWord_336996 prefixEnd_336996 115360617761779156866793 := by
  unfold tailWord_336996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6145626943564260589887421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8194169258085680786516561 6145626943564260589887421)
  ·
    refine ⟨2304610103836597721207783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6145626943564260589887421 2304610103836597721207783)
    ·
      refine ⟨3456915155754896581811675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2304610103836597721207783 3456915155754896581811675)
      ·
        refine ⟨5185372733632344872717513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3456915155754896581811675 5185372733632344872717513)
        ·
          refine ⟨3889029550224258654538135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5185372733632344872717513 3889029550224258654538135)
          ·
            refine ⟨5833544325336387981807203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3889029550224258654538135 5833544325336387981807203)
            ·
              refine ⟨8750316488004581972710805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5833544325336387981807203 8750316488004581972710805)
              ·
                refine ⟨410171085375214779970819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8750316488004581972710805 410171085375214779970819)
                ·
                  refine ⟨615256628062822169956229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410171085375214779970819 615256628062822169956229)
                  ·
                    refine ⟨115360617761779156866793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 615256628062822169956229 115360617761779156866793)
                    ·
                      rfl

theorem cell22_336996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_336996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_336996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_336996 prefixEnd_336996 := by exact prefixLift 336996
  have htrace : WordTrace (prefixWord ++ tailWord_336996) baseStart_336996 baseEnd_336996 := by
    simpa [prefixWord, tailWord_336996, baseEnd_336996] using wordTrace_append hprefix tailTrace_336996
  have hstable : (prefixWord ++ tailWord_336996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336996).length < 2 ^ (prefixWord ++ tailWord_336996).sum := by decide
  have hdescent : baseEnd_336996 < baseStart_336996 := by decide
  rcases family_descends (prefixWord ++ tailWord_336996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337009 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 3, 5]
def baseStart_337009 : Nat := 118140960795 + 337009 * 2 ^ 59
def prefixEnd_337009 : Nat := 4983230072969 + 3 ^ 40 * 337009 * 2
def baseEnd_337009 : Nat := 115365067927451456291753

theorem tailTrace_337009 : CollatzResearch.WordTrace tailWord_337009 prefixEnd_337009 115365067927451456291753 := by
  unfold tailWord_337009
  simp only [CollatzResearch.WordTrace]
  refine ⟨12291728036081424399998081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8194485357387616266665387 12291728036081424399998081)
  ·
    refine ⟨9218796027061068299998561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12291728036081424399998081 9218796027061068299998561)
    ·
      refine ⟨6914097020295801224998921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9218796027061068299998561 6914097020295801224998921)
      ·
        refine ⟨5185572765221850918749191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6914097020295801224998921 5185572765221850918749191)
        ·
          refine ⟨7778359147832776378123787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5185572765221850918749191 7778359147832776378123787)
          ·
            refine ⟨11667538721749164567185681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7778359147832776378123787 11667538721749164567185681)
            ·
              refine ⟨8750654041311873425389261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11667538721749164567185681 8750654041311873425389261)
              ·
                refine ⟨3281495265491952534520973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8750654041311873425389261 3281495265491952534520973)
                ·
                  refine ⟨1230560724559482200445365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3281495265491952534520973 1230560724559482200445365)
                  ·
                    refine ⟨115365067927451456291753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1230560724559482200445365 115365067927451456291753)
                    ·
                      rfl

theorem cell22_337009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_337009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337009 prefixEnd_337009 := by exact prefixLift 337009
  have htrace : WordTrace (prefixWord ++ tailWord_337009) baseStart_337009 baseEnd_337009 := by
    simpa [prefixWord, tailWord_337009, baseEnd_337009] using wordTrace_append hprefix tailTrace_337009
  have hstable : (prefixWord ++ tailWord_337009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337009).length < 2 ^ (prefixWord ++ tailWord_337009).sum := by decide
  have hdescent : baseEnd_337009 < baseStart_337009 := by decide
  rcases family_descends (prefixWord ++ tailWord_337009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337028 : List Nat := [2, 3, 2, 1, 2, 2, 2, 4, 4]
def baseStart_337028 : Nat := 118140960795 + 337028 * 2 ^ 59
def prefixEnd_337028 : Nat := 4983230072969 + 3 ^ 40 * 337028 * 2
def baseEnd_337028 : Nat := 38457190671913913355565

theorem tailTrace_337028 : CollatzResearch.WordTrace tailWord_337028 prefixEnd_337028 38457190671913913355565 := by
  unfold tailWord_337028
  simp only [CollatzResearch.WordTrace]
  refine ⟨6146210511506295322469869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8194947348675060429959825 6146210511506295322469869)
  ·
    refine ⟨2304828941814860745926201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6146210511506295322469869 2304828941814860745926201)
    ·
      refine ⟨1728621706361145559444651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2304828941814860745926201 1728621706361145559444651)
      ·
        refine ⟨2592932559541718339166977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1728621706361145559444651 2592932559541718339166977)
        ·
          refine ⟨1944699419656288754375233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2592932559541718339166977 1944699419656288754375233)
          ·
            refine ⟨1458524564742216565781425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1944699419656288754375233 1458524564742216565781425)
            ·
              refine ⟨1093893423556662424336069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1458524564742216565781425 1093893423556662424336069)
              ·
                refine ⟨205105016916874204563013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1093893423556662424336069 205105016916874204563013)
                ·
                  refine ⟨38457190671913913355565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205105016916874204563013 38457190671913913355565)
                  ·
                    rfl

theorem cell22_337028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_337028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337028 prefixEnd_337028 := by exact prefixLift 337028
  have htrace : WordTrace (prefixWord ++ tailWord_337028) baseStart_337028 baseEnd_337028 := by
    simpa [prefixWord, tailWord_337028, baseEnd_337028] using wordTrace_append hprefix tailTrace_337028
  have hstable : (prefixWord ++ tailWord_337028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337028).length < 2 ^ (prefixWord ++ tailWord_337028).sum := by decide
  have hdescent : baseEnd_337028 < baseStart_337028 := by decide
  rcases family_descends (prefixWord ++ tailWord_337028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337071 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 5, 3]
def baseStart_337071 : Nat := 118140960795 + 337071 * 2 ^ 59
def prefixEnd_337071 : Nat := 4983230072969 + 3 ^ 40 * 337071 * 2
def baseEnd_337071 : Nat := 115386291794503961241563

theorem tailTrace_337071 : CollatzResearch.WordTrace tailWord_337071 prefixEnd_337071 115386291794503961241563 := by
  unfold tailWord_337071
  simp only [CollatzResearch.WordTrace]
  refine ⟨12293989361856808988755067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8195992907904539325836711 12293989361856808988755067)
  ·
    refine ⟨18440984042785213483132601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12293989361856808988755067 18440984042785213483132601)
    ·
      refine ⟨13830738032088910112349451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18440984042785213483132601 13830738032088910112349451)
      ·
        refine ⟨20746107048133365168524177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13830738032088910112349451 20746107048133365168524177)
        ·
          refine ⟨15559580286100023876393133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20746107048133365168524177 15559580286100023876393133)
          ·
            refine ⟨5834842607287508953647425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15559580286100023876393133 5834842607287508953647425)
            ·
              refine ⟨4376131955465631715235569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5834842607287508953647425 4376131955465631715235569)
              ·
                refine ⟨3282098966599223786426677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4376131955465631715235569 3282098966599223786426677)
                ·
                  refine ⟨307696778118677229977501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3282098966599223786426677 307696778118677229977501)
                  ·
                    refine ⟨115386291794503961241563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 307696778118677229977501 115386291794503961241563)
                    ·
                      rfl

theorem cell22_337071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 3].length) (baseStart_337071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337071 prefixEnd_337071 := by exact prefixLift 337071
  have htrace : WordTrace (prefixWord ++ tailWord_337071) baseStart_337071 baseEnd_337071 := by
    simpa [prefixWord, tailWord_337071, baseEnd_337071] using wordTrace_append hprefix tailTrace_337071
  have hstable : (prefixWord ++ tailWord_337071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337071).length < 2 ^ (prefixWord ++ tailWord_337071).sum := by decide
  have hdescent : baseEnd_337071 < baseStart_337071 := by decide
  rcases family_descends (prefixWord ++ tailWord_337071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337146 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 6]
def baseStart_337146 : Nat := 118140960795 + 337146 * 2 ^ 59
def prefixEnd_337146 : Nat := 4983230072969 + 3 ^ 40 * 337146 * 2
def baseEnd_337146 : Nat := 38470655275742921872111

theorem tailTrace_337146 : CollatzResearch.WordTrace tailWord_337146 prefixEnd_337146 38470655275742921872111 := by
  unfold tailWord_337146
  simp only [CollatzResearch.WordTrace]
  refine ⟨3074181209146274199433823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8197816557723397865156861 3074181209146274199433823)
  ·
    refine ⟨4611271813719411299150735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3074181209146274199433823 4611271813719411299150735)
    ·
      refine ⟨6916907720579116948726103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4611271813719411299150735 6916907720579116948726103)
      ·
        refine ⟨10375361580868675423089155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6916907720579116948726103 10375361580868675423089155)
        ·
          refine ⟨15563042371303013134633733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10375361580868675423089155 15563042371303013134633733)
          ·
            refine ⟨2918070444619314962743825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15563042371303013134633733 2918070444619314962743825)
            ·
              refine ⟨2188552833464486222057869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2918070444619314962743825 2188552833464486222057869)
              ·
                refine ⟨820707312549182333271701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2188552833464486222057869 820707312549182333271701)
                ·
                  refine ⟨38470655275742921872111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 820707312549182333271701 38470655275742921872111)
                  ·
                    rfl

theorem cell22_337146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_337146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337146 prefixEnd_337146 := by exact prefixLift 337146
  have htrace : WordTrace (prefixWord ++ tailWord_337146) baseStart_337146 baseEnd_337146 := by
    simpa [prefixWord, tailWord_337146, baseEnd_337146] using wordTrace_append hprefix tailTrace_337146
  have hstable : (prefixWord ++ tailWord_337146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337146).length < 2 ^ (prefixWord ++ tailWord_337146).sum := by decide
  have hdescent : baseEnd_337146 < baseStart_337146 := by decide
  rcases family_descends (prefixWord ++ tailWord_337146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337178 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_337178 : Nat := 118140960795 + 337178 * 2 ^ 59
def prefixEnd_337178 : Nat := 4983230072969 + 3 ^ 40 * 337178 * 2
def baseEnd_337178 : Nat := 115422920081191348816235

theorem tailTrace_337178 : CollatzResearch.WordTrace tailWord_337178 prefixEnd_337178 115422920081191348816235 := by
  unfold tailWord_337178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3074472993117291565725047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8198594648312777508600125 3074472993117291565725047)
  ·
    refine ⟨4611709489675937348587571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3074472993117291565725047 4611709489675937348587571)
    ·
      refine ⟨6917564234513906022881357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4611709489675937348587571 6917564234513906022881357)
      ·
        refine ⟨2594086587942714758580509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6917564234513906022881357 2594086587942714758580509)
        ·
          refine ⟨972782470478518034467691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2594086587942714758580509 972782470478518034467691)
          ·
            refine ⟨1459173705717777051701537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972782470478518034467691 1459173705717777051701537)
            ·
              refine ⟨1094380279288332788776153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459173705717777051701537 1094380279288332788776153)
              ·
                refine ⟨820785209466249591582115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1094380279288332788776153 820785209466249591582115)
                ·
                  refine ⟨1231177814199374387373173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 820785209466249591582115 1231177814199374387373173)
                  ·
                    refine ⟨115422920081191348816235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1231177814199374387373173 115422920081191348816235)
                    ·
                      rfl

theorem cell22_337178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_337178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337178 prefixEnd_337178 := by exact prefixLift 337178
  have htrace : WordTrace (prefixWord ++ tailWord_337178) baseStart_337178 baseEnd_337178 := by
    simpa [prefixWord, tailWord_337178, baseEnd_337178] using wordTrace_append hprefix tailTrace_337178
  have hstable : (prefixWord ++ tailWord_337178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337178).length < 2 ^ (prefixWord ++ tailWord_337178).sum := by decide
  have hdescent : baseEnd_337178 < baseStart_337178 := by decide
  rcases family_descends (prefixWord ++ tailWord_337178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337197 : List Nat := [1, 5, 3, 1, 1, 1, 2, 4, 4]
def baseStart_337197 : Nat := 118140960795 + 337197 * 2 ^ 59
def prefixEnd_337197 : Nat := 4983230072969 + 3 ^ 40 * 337197 * 2
def baseEnd_337197 : Nat := 38476474723160544197059

theorem tailTrace_337197 : CollatzResearch.WordTrace tailWord_337197 prefixEnd_337197 38476474723160544197059 := by
  unfold tailWord_337197
  simp only [CollatzResearch.WordTrace]
  refine ⟨12298584959400332507841845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8199056639600221671894563 12298584959400332507841845)
  ·
    refine ⟨1152992339943781172610173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12298584959400332507841845 1152992339943781172610173)
    ·
      refine ⟨432372127478917939728815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1152992339943781172610173 432372127478917939728815)
      ·
        refine ⟨648558191218376909593223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432372127478917939728815 648558191218376909593223)
        ·
          refine ⟨972837286827565364389835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648558191218376909593223 972837286827565364389835)
          ·
            refine ⟨1459255930241348046584753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972837286827565364389835 1459255930241348046584753)
            ·
              refine ⟨1094441947681011034938565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459255930241348046584753 1094441947681011034938565)
              ·
                refine ⟨205207865190189569050981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1094441947681011034938565 205207865190189569050981)
                ·
                  refine ⟨38476474723160544197059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205207865190189569050981 38476474723160544197059)
                  ·
                    rfl

theorem cell22_337197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_337197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337197 prefixEnd_337197 := by exact prefixLift 337197
  have htrace : WordTrace (prefixWord ++ tailWord_337197) baseStart_337197 baseEnd_337197 := by
    simpa [prefixWord, tailWord_337197, baseEnd_337197] using wordTrace_append hprefix tailTrace_337197
  have hstable : (prefixWord ++ tailWord_337197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337197).length < 2 ^ (prefixWord ++ tailWord_337197).sum := by decide
  have hdescent : baseEnd_337197 < baseStart_337197 := by decide
  rcases family_descends (prefixWord ++ tailWord_337197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337212 : List Nat := [2, 2, 2, 2, 1, 4, 3, 1, 2, 3]
def baseStart_337212 : Nat := 118140960795 + 337212 * 2 ^ 59
def prefixEnd_337212 : Nat := 4983230072969 + 3 ^ 40 * 337212 * 2
def baseEnd_337212 : Nat := 115434558976026593466131

theorem tailTrace_337212 : CollatzResearch.WordTrace tailWord_337212 prefixEnd_337212 115434558976026593466131 := by
  unfold tailWord_337212
  simp only [CollatzResearch.WordTrace]
  refine ⟨6149566027172995034818945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8199421369563993379758593 6149566027172995034818945)
  ·
    refine ⟨4612174520379746276114209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6149566027172995034818945 4612174520379746276114209)
    ·
      refine ⟨3459130890284809707085657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4612174520379746276114209 3459130890284809707085657)
      ·
        refine ⟨2594348167713607280314243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3459130890284809707085657 2594348167713607280314243)
        ·
          refine ⟨3891522251570410920471365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2594348167713607280314243 3891522251570410920471365)
          ·
            refine ⟨729660422169452047588381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3891522251570410920471365 729660422169452047588381)
            ·
              refine ⟨273622658313544517845643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 729660422169452047588381 273622658313544517845643)
              ·
                refine ⟨410433987470316776768465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273622658313544517845643 410433987470316776768465)
                ·
                  refine ⟨307825490602737582576349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410433987470316776768465 307825490602737582576349)
                  ·
                    refine ⟨115434558976026593466131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 307825490602737582576349 115434558976026593466131)
                    ·
                      rfl

theorem cell22_337212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_337212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337212 prefixEnd_337212 := by exact prefixLift 337212
  have htrace : WordTrace (prefixWord ++ tailWord_337212) baseStart_337212 baseEnd_337212 := by
    simpa [prefixWord, tailWord_337212, baseEnd_337212] using wordTrace_append hprefix tailTrace_337212
  have hstable : (prefixWord ++ tailWord_337212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337212).length < 2 ^ (prefixWord ++ tailWord_337212).sum := by decide
  have hdescent : baseEnd_337212 < baseStart_337212 := by decide
  rcases family_descends (prefixWord ++ tailWord_337212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337221 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_337221 : Nat := 118140960795 + 337221 * 2 ^ 59
def prefixEnd_337221 : Nat := 4983230072969 + 3 ^ 40 * 337221 * 2
def baseEnd_337221 : Nat := 115437639859953569991103

theorem tailTrace_337221 : CollatzResearch.WordTrace tailWord_337221 prefixEnd_337221 115437639859953569991103 := by
  unfold tailWord_337221
  simp only [CollatzResearch.WordTrace]
  refine ⟨12299460311313384606715517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8199640207542256404477011 12299460311313384606715517)
  ·
    refine ⟨4612297616742519227518319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12299460311313384606715517 4612297616742519227518319)
    ·
      refine ⟨6918446425113778841277479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4612297616742519227518319 6918446425113778841277479)
      ·
        refine ⟨10377669637670668261916219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6918446425113778841277479 10377669637670668261916219)
        ·
          refine ⟨15566504456506002392874329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10377669637670668261916219 15566504456506002392874329)
          ·
            refine ⟨11674878342379501794655747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15566504456506002392874329 11674878342379501794655747)
            ·
              refine ⟨17512317513569252691983621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11674878342379501794655747 17512317513569252691983621)
              ·
                refine ⟨3283559533794234879746929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17512317513569252691983621 3283559533794234879746929)
                ·
                  refine ⟨2462669650345676159810197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3283559533794234879746929 2462669650345676159810197)
                  ·
                    refine ⟨115437639859953569991103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2462669650345676159810197 115437639859953569991103)
                    ·
                      rfl

theorem cell22_337221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_337221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337221 prefixEnd_337221 := by exact prefixLift 337221
  have htrace : WordTrace (prefixWord ++ tailWord_337221) baseStart_337221 baseEnd_337221 := by
    simpa [prefixWord, tailWord_337221, baseEnd_337221] using wordTrace_append hprefix tailTrace_337221
  have hstable : (prefixWord ++ tailWord_337221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337221).length < 2 ^ (prefixWord ++ tailWord_337221).sum := by decide
  have hdescent : baseEnd_337221 < baseStart_337221 := by decide
  rcases family_descends (prefixWord ++ tailWord_337221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337253 : List Nat := [1, 3, 1, 3, 1, 2, 2, 4, 5]
def baseStart_337253 : Nat := 118140960795 + 337253 * 2 ^ 59
def prefixEnd_337253 : Nat := 4983230072969 + 3 ^ 40 * 337253 * 2
def baseEnd_337253 : Nat := 38482864704638717730335

theorem tailTrace_337253 : CollatzResearch.WordTrace tailWord_337253 prefixEnd_337253 38482864704638717730335 := by
  unfold tailWord_337253
  simp only [CollatzResearch.WordTrace]
  refine ⟨12300627447197454071880413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8200418298131636047920275 12300627447197454071880413)
  ·
    refine ⟨4612735292699045276955155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12300627447197454071880413 4612735292699045276955155)
    ·
      refine ⟨6919102939048567915432733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4612735292699045276955155 6919102939048567915432733)
      ·
        refine ⟨2594663602143212968287275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6919102939048567915432733 2594663602143212968287275)
        ·
          refine ⟨3891995403214819452430913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2594663602143212968287275 3891995403214819452430913)
          ·
            refine ⟨2918996552411114589323185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3891995403214819452430913 2918996552411114589323185)
            ·
              refine ⟨2189247414308335941992389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2918996552411114589323185 2189247414308335941992389)
              ·
                refine ⟨410483890182812989123573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2189247414308335941992389 410483890182812989123573)
                ·
                  refine ⟨38482864704638717730335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 410483890182812989123573 38482864704638717730335)
                  ·
                    rfl

theorem cell22_337253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_337253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337253 prefixEnd_337253 := by exact prefixLift 337253
  have htrace : WordTrace (prefixWord ++ tailWord_337253) baseStart_337253 baseEnd_337253 := by
    simpa [prefixWord, tailWord_337253, baseEnd_337253] using wordTrace_append hprefix tailTrace_337253
  have hstable : (prefixWord ++ tailWord_337253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337253).length < 2 ^ (prefixWord ++ tailWord_337253).sum := by decide
  have hdescent : baseEnd_337253 < baseStart_337253 := by decide
  rcases family_descends (prefixWord ++ tailWord_337253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337308 : List Nat := [2, 2, 3, 4, 1, 2, 2, 2, 1, 3]
def baseStart_337308 : Nat := 118140960795 + 337308 * 2 ^ 59
def prefixEnd_337308 : Nat := 4983230072969 + 3 ^ 40 * 337308 * 2
def baseEnd_337308 : Nat := 115467421737914343065837

theorem tailTrace_337308 : CollatzResearch.WordTrace tailWord_337308 prefixEnd_337308 115467421737914343065837 := by
  unfold tailWord_337308
  simp only [CollatzResearch.WordTrace]
  refine ⟨6151316730999099232566289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8201755641332132310088385 6151316730999099232566289)
  ·
    refine ⟨4613487548249324424424717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6151316730999099232566289 4613487548249324424424717)
    ·
      refine ⟨1730057830593496659159269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4613487548249324424424717 1730057830593496659159269)
      ·
        refine ⟨324385843236280623592363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1730057830593496659159269 324385843236280623592363)
        ·
          refine ⟨486578764854420935388545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324385843236280623592363 486578764854420935388545)
          ·
            refine ⟨364934073640815701541409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486578764854420935388545 364934073640815701541409)
            ·
              refine ⟨273700555230611776156057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364934073640815701541409 273700555230611776156057)
              ·
                refine ⟨205275416422958832117043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273700555230611776156057 205275416422958832117043)
                ·
                  refine ⟨307913124634438248175565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205275416422958832117043 307913124634438248175565)
                  ·
                    refine ⟨115467421737914343065837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 307913124634438248175565 115467421737914343065837)
                    ·
                      rfl

theorem cell22_337308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_337308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337308 prefixEnd_337308 := by exact prefixLift 337308
  have htrace : WordTrace (prefixWord ++ tailWord_337308) baseStart_337308 baseEnd_337308 := by
    simpa [prefixWord, tailWord_337308, baseEnd_337308] using wordTrace_append hprefix tailTrace_337308
  have hstable : (prefixWord ++ tailWord_337308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337308).length < 2 ^ (prefixWord ++ tailWord_337308).sum := by decide
  have hdescent : baseEnd_337308 < baseStart_337308 := by decide
  rcases family_descends (prefixWord ++ tailWord_337308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337315 : List Nat := [1, 1, 1, 4, 1, 3, 3, 4, 4]
def baseStart_337315 : Nat := 118140960795 + 337315 * 2 ^ 59
def prefixEnd_337315 : Nat := 4983230072969 + 3 ^ 40 * 337315 * 2
def baseEnd_337315 : Nat := 38489939326989552713605

theorem tailTrace_337315 : CollatzResearch.WordTrace tailWord_337315 prefixEnd_337315 38489939326989552713605 := by
  unfold tailWord_337315
  simp only [CollatzResearch.WordTrace]
  refine ⟨12302888772972838660637399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8201925848648559107091599 12302888772972838660637399)
  ·
    refine ⟨18454333159459257990956099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12302888772972838660637399 18454333159459257990956099)
    ·
      refine ⟨27681499739188886986434149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18454333159459257990956099 27681499739188886986434149)
      ·
        refine ⟨5190281201097916309956403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27681499739188886986434149 5190281201097916309956403)
        ·
          refine ⟨7785421801646874464934605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5190281201097916309956403 7785421801646874464934605)
          ·
            refine ⟨2919533175617577924350477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7785421801646874464934605 2919533175617577924350477)
            ·
              refine ⟨1094824940856591721631429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2919533175617577924350477 1094824940856591721631429)
              ·
                refine ⟨205279676410610947805893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1094824940856591721631429 205279676410610947805893)
                ·
                  refine ⟨38489939326989552713605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205279676410610947805893 38489939326989552713605)
                  ·
                    rfl

theorem cell22_337315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 4].length) (baseStart_337315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337315 prefixEnd_337315 := by exact prefixLift 337315
  have htrace : WordTrace (prefixWord ++ tailWord_337315) baseStart_337315 baseEnd_337315 := by
    simpa [prefixWord, tailWord_337315, baseEnd_337315] using wordTrace_append hprefix tailTrace_337315
  have hstable : (prefixWord ++ tailWord_337315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337315).length < 2 ^ (prefixWord ++ tailWord_337315).sum := by decide
  have hdescent : baseEnd_337315 < baseStart_337315 := by decide
  rcases family_descends (prefixWord ++ tailWord_337315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337450 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 8]
def baseStart_337450 : Nat := 118140960795 + 337450 * 2 ^ 59
def prefixEnd_337450 : Nat := 4983230072969 + 3 ^ 40 * 337450 * 2
def baseEnd_337450 : Nat := 38505343746624435338467

theorem tailTrace_337450 : CollatzResearch.WordTrace tailWord_337450 prefixEnd_337450 38505343746624435338467 := by
  unfold tailWord_337450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076953156870939179200451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8205208418322504477867869 3076953156870939179200451)
  ·
    refine ⟨4615429735306408768800677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3076953156870939179200451 4615429735306408768800677)
    ·
      refine ⟨865393075369951644150127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4615429735306408768800677 865393075369951644150127)
      ·
        refine ⟨1298089613054927466225191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865393075369951644150127 1298089613054927466225191)
        ·
          refine ⟨1947134419582391199337787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298089613054927466225191 1947134419582391199337787)
          ·
            refine ⟨2920701629373586799006681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1947134419582391199337787 2920701629373586799006681)
            ·
              refine ⟨2190526222030190099255011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2920701629373586799006681 2190526222030190099255011)
              ·
                refine ⟨3285789333045285148882517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190526222030190099255011 3285789333045285148882517)
                ·
                  refine ⟨38505343746624435338467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3285789333045285148882517 38505343746624435338467)
                  ·
                    rfl

theorem cell22_337450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_337450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337450 prefixEnd_337450 := by exact prefixLift 337450
  have htrace : WordTrace (prefixWord ++ tailWord_337450) baseStart_337450 baseEnd_337450 := by
    simpa [prefixWord, tailWord_337450, baseEnd_337450] using wordTrace_append hprefix tailTrace_337450
  have hstable : (prefixWord ++ tailWord_337450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337450).length < 2 ^ (prefixWord ++ tailWord_337450).sum := by decide
  have hdescent : baseEnd_337450 < baseStart_337450 := by decide
  rcases family_descends (prefixWord ++ tailWord_337450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337465 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 3, 5]
def baseStart_337465 : Nat := 118140960795 + 337465 * 2 ^ 59
def prefixEnd_337465 : Nat := 4983230072969 + 3 ^ 40 * 337465 * 2
def baseEnd_337465 : Nat := 115521166046418266890355

theorem tailTrace_337465 : CollatzResearch.WordTrace tailWord_337465 prefixEnd_337465 115521166046418266890355 := by
  unfold tailWord_337465
  simp only [CollatzResearch.WordTrace]
  refine ⟨12308359722429414278597849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8205573148286276185731899 12308359722429414278597849)
  ·
    refine ⟨9231269791822060708948387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12308359722429414278597849 9231269791822060708948387)
    ·
      refine ⟨13846904687733091063422581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9231269791822060708948387 13846904687733091063422581)
      ·
        refine ⟨1298147314474977287195867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13846904687733091063422581 1298147314474977287195867)
        ·
          refine ⟨1947220971712465930793801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298147314474977287195867 1947220971712465930793801)
          ·
            refine ⟨1460415728784349448095351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1947220971712465930793801 1460415728784349448095351)
            ·
              refine ⟨2190623593176524172143027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460415728784349448095351 2190623593176524172143027)
              ·
                refine ⟨3285935389764786258214541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190623593176524172143027 3285935389764786258214541)
                ·
                  refine ⟨1232225771161794846830453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3285935389764786258214541 1232225771161794846830453)
                  ·
                    refine ⟨115521166046418266890355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1232225771161794846830453 115521166046418266890355)
                    ·
                      rfl

theorem cell22_337465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_337465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337465 prefixEnd_337465 := by exact prefixLift 337465
  have htrace : WordTrace (prefixWord ++ tailWord_337465) baseStart_337465 baseEnd_337465 := by
    simpa [prefixWord, tailWord_337465, baseEnd_337465] using wordTrace_append hprefix tailTrace_337465
  have hstable : (prefixWord ++ tailWord_337465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337465).length < 2 ^ (prefixWord ++ tailWord_337465).sum := by decide
  have hdescent : baseEnd_337465 < baseStart_337465 := by decide
  rcases family_descends (prefixWord ++ tailWord_337465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337484 : List Nat := [2, 2, 1, 3, 1, 3, 4, 2, 4]
def baseStart_337484 : Nat := 118140960795 + 337484 * 2 ^ 59
def prefixEnd_337484 : Nat := 4983230072969 + 3 ^ 40 * 337484 * 2
def baseEnd_337484 : Nat := 38509223378236183555099

theorem tailTrace_337484 : CollatzResearch.WordTrace tailWord_337484 prefixEnd_337484 38509223378236183555099 := by
  unfold tailWord_337484
  simp only [CollatzResearch.WordTrace]
  refine ⟨6154526354680290261769753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8206035139573720349026337 6154526354680290261769753)
  ·
    refine ⟨4615894766010217696327315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6154526354680290261769753 4615894766010217696327315)
    ·
      refine ⟨6923842149015326544490973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4615894766010217696327315 6923842149015326544490973)
      ·
        refine ⟨2596440805880747454184115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6923842149015326544490973 2596440805880747454184115)
        ·
          refine ⟨3894661208821121181276173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2596440805880747454184115 3894661208821121181276173)
          ·
            refine ⟨1460497953307920442978565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3894661208821121181276173 1460497953307920442978565)
            ·
              refine ⟨273843366245235083058481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1460497953307920442978565 273843366245235083058481)
              ·
                refine ⟨205382524683926312293861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273843366245235083058481 205382524683926312293861)
                ·
                  refine ⟨38509223378236183555099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205382524683926312293861 38509223378236183555099)
                  ·
                    rfl

theorem cell22_337484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_337484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337484 prefixEnd_337484 := by exact prefixLift 337484
  have htrace : WordTrace (prefixWord ++ tailWord_337484) baseStart_337484 baseEnd_337484 := by
    simpa [prefixWord, tailWord_337484, baseEnd_337484] using wordTrace_append hprefix tailTrace_337484
  have hstable : (prefixWord ++ tailWord_337484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337484).length < 2 ^ (prefixWord ++ tailWord_337484).sum := by decide
  have hdescent : baseEnd_337484 < baseStart_337484 := by decide
  rcases family_descends (prefixWord ++ tailWord_337484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337495 : List Nat := [1, 1, 3, 2, 2, 3, 3, 7]
def baseStart_337495 : Nat := 118140960795 + 337495 * 2 ^ 59
def prefixEnd_337495 : Nat := 4983230072969 + 3 ^ 40 * 337495 * 2
def baseEnd_337495 : Nat := 12836826184389798737807

theorem tailTrace_337495 : CollatzResearch.WordTrace tailWord_337495 prefixEnd_337495 12836826184389798737807 := by
  unfold tailWord_337495
  simp only [CollatzResearch.WordTrace]
  refine ⟨12309453912320729402189939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8206302608213819601459959 12309453912320729402189939)
  ·
    refine ⟨18464180868481094103284909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12309453912320729402189939 18464180868481094103284909)
    ·
      refine ⟨6924067825680410288731841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18464180868481094103284909 6924067825680410288731841)
      ·
        refine ⟨5193050869260307716548881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6924067825680410288731841 5193050869260307716548881)
        ·
          refine ⟨3894788151945230787411661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5193050869260307716548881 3894788151945230787411661)
          ·
            refine ⟨1460545556979461545279373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3894788151945230787411661 1460545556979461545279373)
            ·
              refine ⟨547704583867298079479765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1460545556979461545279373 547704583867298079479765)
              ·
                refine ⟨12836826184389798737807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 547704583867298079479765 12836826184389798737807)
                ·
                  rfl

theorem cell22_337495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 7].length) (baseStart_337495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337495 prefixEnd_337495 := by exact prefixLift 337495
  have htrace : WordTrace (prefixWord ++ tailWord_337495) baseStart_337495 baseEnd_337495 := by
    simpa [prefixWord, tailWord_337495, baseEnd_337495] using wordTrace_append hprefix tailTrace_337495
  have hstable : (prefixWord ++ tailWord_337495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337495).length < 2 ^ (prefixWord ++ tailWord_337495).sum := by decide
  have hdescent : baseEnd_337495 < baseStart_337495 := by decide
  rcases family_descends (prefixWord ++ tailWord_337495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337514 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 2, 4]
def baseStart_337514 : Nat := 118140960795 + 337514 * 2 ^ 59
def prefixEnd_337514 : Nat := 4983230072969 + 3 ^ 40 * 337514 * 2
def baseEnd_337514 : Nat := 115537939747798472415205

theorem tailTrace_337514 : CollatzResearch.WordTrace tailWord_337514 prefixEnd_337514 115537939747798472415205 := by
  unfold tailWord_337514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3077536724812973911782899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8206764599501263764754397 3077536724812973911782899)
  ·
    refine ⟨4616305087219460867674349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3077536724812973911782899 4616305087219460867674349)
    ·
      refine ⟨1731114407707297825377881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4616305087219460867674349 1731114407707297825377881)
      ·
        refine ⟨1298335805780473369033411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1731114407707297825377881 1298335805780473369033411)
        ·
          refine ⟨1947503708670710053550117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298335805780473369033411 1947503708670710053550117)
          ·
            refine ⟨365156945375758135040647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1947503708670710053550117 365156945375758135040647)
            ·
              refine ⟨547735418063637202560971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365156945375758135040647 547735418063637202560971)
              ·
                refine ⟨821603127095455803841457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547735418063637202560971 821603127095455803841457)
                ·
                  refine ⟨616202345321591852881093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 821603127095455803841457 616202345321591852881093)
                  ·
                    refine ⟨115537939747798472415205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 616202345321591852881093 115537939747798472415205)
                    ·
                      rfl

theorem cell22_337514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_337514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337514 prefixEnd_337514 := by exact prefixLift 337514
  have htrace : WordTrace (prefixWord ++ tailWord_337514) baseStart_337514 baseEnd_337514 := by
    simpa [prefixWord, tailWord_337514, baseEnd_337514] using wordTrace_append hprefix tailTrace_337514
  have hstable : (prefixWord ++ tailWord_337514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337514).length < 2 ^ (prefixWord ++ tailWord_337514).sum := by decide
  have hdescent : baseEnd_337514 < baseStart_337514 := by decide
  rcases family_descends (prefixWord ++ tailWord_337514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337587 : List Nat := [1, 1, 1, 2, 3, 3, 1, 5, 1, 4]
def baseStart_337587 : Nat := 118140960795 + 337587 * 2 ^ 59
def prefixEnd_337587 : Nat := 4983230072969 + 3 ^ 40 * 337587 * 2
def baseEnd_337587 : Nat := 115562929139650615339981

theorem tailTrace_337587 : CollatzResearch.WordTrace tailWord_337587 prefixEnd_337587 115562929139650615339981 := by
  unfold tailWord_337587
  simp only [CollatzResearch.WordTrace]
  refine ⟨12312809427987429114539015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8208539618658286076359343 12312809427987429114539015)
  ·
    refine ⟨18469214141981143671808523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12312809427987429114539015 18469214141981143671808523)
    ·
      refine ⟨27703821212971715507712785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18469214141981143671808523 27703821212971715507712785)
      ·
        refine ⟨20777865909728786630784589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27703821212971715507712785 20777865909728786630784589)
        ·
          refine ⟨7791699716148294986544221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20777865909728786630784589 7791699716148294986544221)
          ·
            refine ⟨2921887393555610619954083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7791699716148294986544221 2921887393555610619954083)
            ·
              refine ⟨4382831090333415929931125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2921887393555610619954083 4382831090333415929931125)
              ·
                refine ⟨410890414718757743431043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4382831090333415929931125 410890414718757743431043)
                ·
                  refine ⟨616335622078136615146565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410890414718757743431043 616335622078136615146565)
                  ·
                    refine ⟨115562929139650615339981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 616335622078136615146565 115562929139650615339981)
                    ·
                      rfl

theorem cell22_337587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 4].length) (baseStart_337587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337587 prefixEnd_337587 := by exact prefixLift 337587
  have htrace : WordTrace (prefixWord ++ tailWord_337587) baseStart_337587 baseEnd_337587 := by
    simpa [prefixWord, tailWord_337587, baseEnd_337587] using wordTrace_append hprefix tailTrace_337587
  have hstable : (prefixWord ++ tailWord_337587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337587).length < 2 ^ (prefixWord ++ tailWord_337587).sum := by decide
  have hdescent : baseEnd_337587 < baseStart_337587 := by decide
  rcases family_descends (prefixWord ++ tailWord_337587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337615 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 3, 6]
def baseStart_337615 : Nat := 118140960795 + 337615 * 2 ^ 59
def prefixEnd_337615 : Nat := 4983230072969 + 3 ^ 40 * 337615 * 2
def baseEnd_337615 : Nat := 115572514111867875639895

theorem tailTrace_337615 : CollatzResearch.WordTrace tailWord_337615 prefixEnd_337615 115572514111867875639895 := by
  unfold tailWord_337615
  simp only [CollatzResearch.WordTrace]
  refine ⟨12313830671885989896558299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8209220447923993264372199 12313830671885989896558299)
  ·
    refine ⟨18470746007828984844837449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12313830671885989896558299 18470746007828984844837449)
    ·
      refine ⟨13853059505871738633628087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18470746007828984844837449 13853059505871738633628087)
      ·
        refine ⟨20779589258807607950442131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13853059505871738633628087 20779589258807607950442131)
        ·
          refine ⟨31169383888211411925663197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20779589258807607950442131 31169383888211411925663197)
          ·
            refine ⟨11688518958079279472123699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31169383888211411925663197 11688518958079279472123699)
            ·
              refine ⟨17532778437118919208185549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11688518958079279472123699 17532778437118919208185549)
              ·
                refine ⟨6574791913919594703069581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17532778437118919208185549 6574791913919594703069581)
                ·
                  refine ⟨2465546967719848013651093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6574791913919594703069581 2465546967719848013651093)
                  ·
                    refine ⟨115572514111867875639895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2465546967719848013651093 115572514111867875639895)
                    ·
                      rfl

theorem cell22_337615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_337615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337615 prefixEnd_337615 := by exact prefixLift 337615
  have htrace : WordTrace (prefixWord ++ tailWord_337615) baseStart_337615 baseEnd_337615 := by
    simpa [prefixWord, tailWord_337615, baseEnd_337615] using wordTrace_append hprefix tailTrace_337615
  have hstable : (prefixWord ++ tailWord_337615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337615).length < 2 ^ (prefixWord ++ tailWord_337615).sum := by decide
  have hdescent : baseEnd_337615 < baseStart_337615 := by decide
  rcases family_descends (prefixWord ++ tailWord_337615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337632 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 2, 4]
def baseStart_337632 : Nat := 118140960795 + 337632 * 2 ^ 59
def prefixEnd_337632 : Nat := 4983230072969 + 3 ^ 40 * 337632 * 2
def baseEnd_337632 : Nat := 115578333559285497964843

theorem tailTrace_337632 : CollatzResearch.WordTrace tailWord_337632 prefixEnd_337632 115578333559285497964843 := by
  unfold tailWord_337632
  simp only [CollatzResearch.WordTrace]
  refine ⟨6157225356412200899963575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8209633808549601199951433 6157225356412200899963575)
  ·
    refine ⟨9235838034618301349945363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6157225356412200899963575 9235838034618301349945363)
    ·
      refine ⟨13853757051927452024918045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9235838034618301349945363 13853757051927452024918045)
      ·
        refine ⟨5195158894472794509344267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13853757051927452024918045 5195158894472794509344267)
        ·
          refine ⟨7792738341709191764016401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5195158894472794509344267 7792738341709191764016401)
          ·
            refine ⟨5844553756281893823012301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7792738341709191764016401 5844553756281893823012301)
            ·
              refine ⟨2191707658605710183629613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5844553756281893823012301 2191707658605710183629613)
              ·
                refine ⟨821890371977141318861105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2191707658605710183629613 821890371977141318861105)
                ·
                  refine ⟨616417778982855989145829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 821890371977141318861105 616417778982855989145829)
                  ·
                    refine ⟨115578333559285497964843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 616417778982855989145829 115578333559285497964843)
                    ·
                      rfl

theorem cell22_337632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_337632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337632 prefixEnd_337632 := by exact prefixLift 337632
  have htrace : WordTrace (prefixWord ++ tailWord_337632) baseStart_337632 baseEnd_337632 := by
    simpa [prefixWord, tailWord_337632, baseEnd_337632] using wordTrace_append hprefix tailTrace_337632
  have hstable : (prefixWord ++ tailWord_337632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337632).length < 2 ^ (prefixWord ++ tailWord_337632).sum := by decide
  have hdescent : baseEnd_337632 < baseStart_337632 := by decide
  rcases family_descends (prefixWord ++ tailWord_337632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337692 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 7]
def baseStart_337692 : Nat := 118140960795 + 337692 * 2 ^ 59
def prefixEnd_337692 : Nat := 4983230072969 + 3 ^ 40 * 337692 * 2
def baseEnd_337692 : Nat := 38532957595155113821553

theorem tailTrace_337692 : CollatzResearch.WordTrace tailWord_337692 prefixEnd_337692 38532957595155113821553 := by
  unfold tailWord_337692
  simp only [CollatzResearch.WordTrace]
  refine ⟨6158319546303516023555665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8211092728404688031407553 6158319546303516023555665)
  ·
    refine ⟨4618739659727637017666749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6158319546303516023555665 4618739659727637017666749)
    ·
      refine ⟨1732027372397863881625031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4618739659727637017666749 1732027372397863881625031)
      ·
        refine ⟨2598041058596795822437547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1732027372397863881625031 2598041058596795822437547)
        ·
          refine ⟨3897061587895193733656321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2598041058596795822437547 3897061587895193733656321)
          ·
            refine ⟨2922796190921395300242241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3897061587895193733656321 2922796190921395300242241)
            ·
              refine ⟨2192097143191046475181681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2922796190921395300242241 2192097143191046475181681)
              ·
                refine ⟨1644072857393284856386261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2192097143191046475181681 1644072857393284856386261)
                ·
                  refine ⟨38532957595155113821553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1644072857393284856386261 38532957595155113821553)
                  ·
                    rfl

theorem cell22_337692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_337692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337692 prefixEnd_337692 := by exact prefixLift 337692
  have htrace : WordTrace (prefixWord ++ tailWord_337692) baseStart_337692 baseEnd_337692 := by
    simpa [prefixWord, tailWord_337692, baseEnd_337692] using wordTrace_append hprefix tailTrace_337692
  have hstable : (prefixWord ++ tailWord_337692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337692).length < 2 ^ (prefixWord ++ tailWord_337692).sum := by decide
  have hdescent : baseEnd_337692 < baseStart_337692 := by decide
  rcases family_descends (prefixWord ++ tailWord_337692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337737 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 6]
def baseStart_337737 : Nat := 118140960795 + 337737 * 2 ^ 59
def prefixEnd_337737 : Nat := 4983230072969 + 3 ^ 40 * 337737 * 2
def baseEnd_337737 : Nat := 38538092401700074696507

theorem tailTrace_337737 : CollatzResearch.WordTrace tailWord_337737 prefixEnd_337737 38538092401700074696507 := by
  unfold tailWord_337737
  simp only [CollatzResearch.WordTrace]
  refine ⟨12318280377444004732499465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8212186918296003154999643 12318280377444004732499465)
  ·
    refine ⟨9238710283083003549374599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12318280377444004732499465 9238710283083003549374599)
    ·
      refine ⟨13858065424624505324061899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9238710283083003549374599 13858065424624505324061899)
      ·
        refine ⟨20787098136936757986092849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13858065424624505324061899 20787098136936757986092849)
        ·
          refine ⟨15590323602702568489569637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20787098136936757986092849 15590323602702568489569637)
          ·
            refine ⟨2923185675506731591794307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15590323602702568489569637 2923185675506731591794307)
            ·
              refine ⟨4384778513260097387691461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923185675506731591794307 4384778513260097387691461)
              ·
                refine ⟨822145971236268260192149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4384778513260097387691461 822145971236268260192149)
                ·
                  refine ⟨38538092401700074696507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 822145971236268260192149 38538092401700074696507)
                  ·
                    rfl

theorem cell22_337737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_337737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337737 prefixEnd_337737 := by exact prefixLift 337737
  have htrace : WordTrace (prefixWord ++ tailWord_337737) baseStart_337737 baseEnd_337737 := by
    simpa [prefixWord, tailWord_337737, baseEnd_337737] using wordTrace_append hprefix tailTrace_337737
  have hstable : (prefixWord ++ tailWord_337737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337737).length < 2 ^ (prefixWord ++ tailWord_337737).sum := by decide
  have hdescent : baseEnd_337737 < baseStart_337737 := by decide
  rcases family_descends (prefixWord ++ tailWord_337737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337790 : List Nat := [4, 2, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_337790 : Nat := 118140960795 + 337790 * 2 ^ 59
def prefixEnd_337790 : Nat := 4983230072969 + 3 ^ 40 * 337790 * 2
def baseEnd_337790 : Nat := 115632420188225752514359

theorem tailTrace_337790 : CollatzResearch.WordTrace tailWord_337790 prefixEnd_337790 115632420188225752514359 := by
  unfold tailWord_337790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1540026680781499348022353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8213475630834663189452549 1540026680781499348022353)
  ·
    refine ⟨1155020010586124511016765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1540026680781499348022353 1155020010586124511016765)
    ·
      refine ⟨433132503969796691631287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1155020010586124511016765 433132503969796691631287)
      ·
        refine ⟨649698755954695037446931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433132503969796691631287 649698755954695037446931)
        ·
          refine ⟨974548133932042556170397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 649698755954695037446931 974548133932042556170397)
          ·
            refine ⟨365455550224515958563899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 974548133932042556170397 365455550224515958563899)
            ·
              refine ⟨548183325336773937845849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365455550224515958563899 548183325336773937845849)
              ·
                refine ⟨411137494002580453384387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548183325336773937845849 411137494002580453384387)
                ·
                  refine ⟨616706241003870680076581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411137494002580453384387 616706241003870680076581)
                  ·
                    refine ⟨115632420188225752514359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 616706241003870680076581 115632420188225752514359)
                    ·
                      rfl

theorem cell22_337790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_337790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337790 prefixEnd_337790 := by exact prefixLift 337790
  have htrace : WordTrace (prefixWord ++ tailWord_337790) baseStart_337790 baseEnd_337790 := by
    simpa [prefixWord, tailWord_337790, baseEnd_337790] using wordTrace_append hprefix tailTrace_337790
  have hstable : (prefixWord ++ tailWord_337790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337790).length < 2 ^ (prefixWord ++ tailWord_337790).sum := by decide
  have hdescent : baseEnd_337790 < baseStart_337790 := by decide
  rcases family_descends (prefixWord ++ tailWord_337790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337816 : List Nat := [2, 1, 2, 6, 2, 9]
def baseStart_337816 : Nat := 118140960795 + 337816 * 2 ^ 59
def prefixEnd_337816 : Nat := 4983230072969 + 3 ^ 40 * 337816 * 2
def baseEnd_337816 : Nat := 1427670623698399399559

theorem tailTrace_337816 : CollatzResearch.WordTrace tailWord_337816 prefixEnd_337816 1427670623698399399559 := by
  unfold tailWord_337816
  simp only [CollatzResearch.WordTrace]
  refine ⟨6160580872078900612312651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8214107829438534149750201 6160580872078900612312651)
  ·
    refine ⟨9240871308118350918468977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6160580872078900612312651 9240871308118350918468977)
    ·
      refine ⟨6930653481088763188851733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9240871308118350918468977 6930653481088763188851733)
      ·
        refine ⟨324874381926035774477425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6930653481088763188851733 324874381926035774477425)
        ·
          refine ⟨243655786444526830858069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324874381926035774477425 243655786444526830858069)
          ·
            refine ⟨1427670623698399399559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 243655786444526830858069 1427670623698399399559)
            ·
              rfl

theorem cell22_337816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 9].length) (baseStart_337816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337816 prefixEnd_337816 := by exact prefixLift 337816
  have htrace : WordTrace (prefixWord ++ tailWord_337816) baseStart_337816 baseEnd_337816 := by
    simpa [prefixWord, tailWord_337816, baseEnd_337816] using wordTrace_append hprefix tailTrace_337816
  have hstable : (prefixWord ++ tailWord_337816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337816).length < 2 ^ (prefixWord ++ tailWord_337816).sum := by decide
  have hdescent : baseEnd_337816 < baseStart_337816 := by decide
  rcases family_descends (prefixWord ++ tailWord_337816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337878 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_337878 : Nat := 118140960795 + 337878 * 2 ^ 59
def prefixEnd_337878 : Nat := 4983230072969 + 3 ^ 40 * 337878 * 2
def baseEnd_337878 : Nat := 38554181462207618771363

theorem tailTrace_337878 : CollatzResearch.WordTrace tailWord_337878 prefixEnd_337878 38554181462207618771363 := by
  unfold tailWord_337878
  simp only [CollatzResearch.WordTrace]
  refine ⟨770213941870824113336393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8215615379955457208921525 770213941870824113336393)
  ·
    refine ⟨577660456403118085002295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 770213941870824113336393 577660456403118085002295)
    ·
      refine ⟨866490684604677127503443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 577660456403118085002295 866490684604677127503443)
      ·
        refine ⟨1299736026907015691255165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866490684604677127503443 1299736026907015691255165)
        ·
          refine ⟨487401010090130884220687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1299736026907015691255165 487401010090130884220687)
          ·
            refine ⟨731101515135196326331031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487401010090130884220687 731101515135196326331031)
            ·
              refine ⟨1096652272702794489496547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731101515135196326331031 1096652272702794489496547)
              ·
                refine ⟨1644978409054191734244821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096652272702794489496547 1644978409054191734244821)
                ·
                  refine ⟨38554181462207618771363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1644978409054191734244821 38554181462207618771363)
                  ·
                    rfl

theorem cell22_337878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_337878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337878 prefixEnd_337878 := by exact prefixLift 337878
  have htrace : WordTrace (prefixWord ++ tailWord_337878) baseStart_337878 baseEnd_337878 := by
    simpa [prefixWord, tailWord_337878, baseEnd_337878] using wordTrace_append hprefix tailTrace_337878
  have hstable : (prefixWord ++ tailWord_337878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337878).length < 2 ^ (prefixWord ++ tailWord_337878).sum := by decide
  have hdescent : baseEnd_337878 < baseStart_337878 := by decide
  rcases family_descends (prefixWord ++ tailWord_337878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337889 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 6]
def baseStart_337889 : Nat := 118140960795 + 337889 * 2 ^ 59
def prefixEnd_337889 : Nat := 4983230072969 + 3 ^ 40 * 337889 * 2
def baseEnd_337889 : Nat := 38555436637140831429685

theorem tailTrace_337889 : CollatzResearch.WordTrace tailWord_337889 prefixEnd_337889 38555436637140831429685 := by
  unfold tailWord_337889
  simp only [CollatzResearch.WordTrace]
  refine ⟨12323824272893334692032721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8215882848595556461355147 12323824272893334692032721)
  ·
    refine ⟨9242868204670001019024541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12323824272893334692032721 9242868204670001019024541)
    ·
      refine ⟨3466075576751250382134203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9242868204670001019024541 3466075576751250382134203)
      ·
        refine ⟨5199113365126875573201305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3466075576751250382134203 5199113365126875573201305)
        ·
          refine ⟨3899335023845156679900979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5199113365126875573201305 3899335023845156679900979)
          ·
            refine ⟨5849002535767735019851469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3899335023845156679900979 5849002535767735019851469)
            ·
              refine ⟨2193375950912900632444301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5849002535767735019851469 2193375950912900632444301)
              ·
                refine ⟨822515981592337737166613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2193375950912900632444301 822515981592337737166613)
                ·
                  refine ⟨38555436637140831429685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 822515981592337737166613 38555436637140831429685)
                  ·
                    rfl

theorem cell22_337889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_337889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337889 prefixEnd_337889 := by exact prefixLift 337889
  have htrace : WordTrace (prefixWord ++ tailWord_337889) baseStart_337889 baseEnd_337889 := by
    simpa [prefixWord, tailWord_337889, baseEnd_337889] using wordTrace_append hprefix tailTrace_337889
  have hstable : (prefixWord ++ tailWord_337889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337889).length < 2 ^ (prefixWord ++ tailWord_337889).sum := by decide
  have hdescent : baseEnd_337889 < baseStart_337889 := by decide
  rcases family_descends (prefixWord ++ tailWord_337889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337919 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 6, 4]
def baseStart_337919 : Nat := 118140960795 + 337919 * 2 ^ 59
def prefixEnd_337919 : Nat := 4983230072969 + 3 ^ 40 * 337919 * 2
def baseEnd_337919 : Nat := 115676579524512416038963

theorem tailTrace_337919 : CollatzResearch.WordTrace tailWord_337919 prefixEnd_337919 115676579524512416038963 := by
  unfold tailWord_337919
  simp only [CollatzResearch.WordTrace]
  refine ⟨12324918462784649815624811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8216612308523099877083207 12324918462784649815624811)
  ·
    refine ⟨18487377694176974723437217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12324918462784649815624811 18487377694176974723437217)
    ·
      refine ⟨13865533270632731042577913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18487377694176974723437217 13865533270632731042577913)
      ·
        refine ⟨10399149952974548281933435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13865533270632731042577913 10399149952974548281933435)
        ·
          refine ⟨15598724929461822422900153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10399149952974548281933435 15598724929461822422900153)
          ·
            refine ⟨11699043697096366817175115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15598724929461822422900153 11699043697096366817175115)
            ·
              refine ⟨17548565545644550225762673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11699043697096366817175115 17548565545644550225762673)
              ·
                refine ⟨13161424159233412669322005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17548565545644550225762673 13161424159233412669322005)
                ·
                  refine ⟨616941757464066218874469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13161424159233412669322005 616941757464066218874469)
                  ·
                    refine ⟨115676579524512416038963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 616941757464066218874469 115676579524512416038963)
                    ·
                      rfl

theorem cell22_337919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_337919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337919 prefixEnd_337919 := by exact prefixLift 337919
  have htrace : WordTrace (prefixWord ++ tailWord_337919) baseStart_337919 baseEnd_337919 := by
    simpa [prefixWord, tailWord_337919, baseEnd_337919] using wordTrace_append hprefix tailTrace_337919
  have hstable : (prefixWord ++ tailWord_337919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337919).length < 2 ^ (prefixWord ++ tailWord_337919).sum := by decide
  have hdescent : baseEnd_337919 < baseStart_337919 := by decide
  rcases family_descends (prefixWord ++ tailWord_337919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337921 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 6, 3]
def baseStart_337921 : Nat := 118140960795 + 337921 * 2 ^ 59
def prefixEnd_337921 : Nat := 4983230072969 + 3 ^ 40 * 337921 * 2
def baseEnd_337921 : Nat := 115677264165385077488957

theorem tailTrace_337921 : CollatzResearch.WordTrace tailWord_337921 prefixEnd_337921 115677264165385077488957 := by
  unfold tailWord_337921
  simp only [CollatzResearch.WordTrace]
  refine ⟨12324991408777404157197617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8216660939184936104798411 12324991408777404157197617)
  ·
    refine ⟨9243743556583053117898213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12324991408777404157197617 9243743556583053117898213)
    ·
      refine ⟨1733201916859322459605915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9243743556583053117898213 1733201916859322459605915)
      ·
        refine ⟨2599802875288983689408873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1733201916859322459605915 2599802875288983689408873)
        ·
          refine ⟨1949852156466737767056655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2599802875288983689408873 1949852156466737767056655)
          ·
            refine ⟨2924778234700106650584983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1949852156466737767056655 2924778234700106650584983)
            ·
              refine ⟨4387167352050159975877475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2924778234700106650584983 4387167352050159975877475)
              ·
                refine ⟨6580751028075239963816213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4387167352050159975877475 6580751028075239963816213)
                ·
                  refine ⟨308472704441026873303885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6580751028075239963816213 308472704441026873303885)
                  ·
                    refine ⟨115677264165385077488957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 308472704441026873303885 115677264165385077488957)
                    ·
                      rfl

theorem cell22_337921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_337921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337921 prefixEnd_337921 := by exact prefixLift 337921
  have htrace : WordTrace (prefixWord ++ tailWord_337921) baseStart_337921 baseEnd_337921 := by
    simpa [prefixWord, tailWord_337921, baseEnd_337921] using wordTrace_append hprefix tailTrace_337921
  have hstable : (prefixWord ++ tailWord_337921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337921).length < 2 ^ (prefixWord ++ tailWord_337921).sum := by decide
  have hdescent : baseEnd_337921 < baseStart_337921 := by decide
  rcases family_descends (prefixWord ++ tailWord_337921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337964 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_337964 : Nat := 118140960795 + 337964 * 2 ^ 59
def prefixEnd_337964 : Nat := 4983230072969 + 3 ^ 40 * 337964 * 2
def baseEnd_337964 : Nat := 115691983944147298663825

theorem tailTrace_337964 : CollatzResearch.WordTrace tailWord_337964 prefixEnd_337964 115691983944147298663825 := by
  unfold tailWord_337964
  simp only [CollatzResearch.WordTrace]
  refine ⟨6163279873810811250506473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8217706498414415000675297 6163279873810811250506473)
  ·
    refine ⟨4622459905358108437879855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6163279873810811250506473 4622459905358108437879855)
    ·
      refine ⟨6933689858037162656819783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4622459905358108437879855 6933689858037162656819783)
      ·
        refine ⟨10400534787055743985229675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6933689858037162656819783 10400534787055743985229675)
        ·
          refine ⟨15600802180583615977844513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10400534787055743985229675 15600802180583615977844513)
          ·
            refine ⟨11700601635437711983383385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15600802180583615977844513 11700601635437711983383385)
            ·
              refine ⟨8775451226578283987537539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11700601635437711983383385 8775451226578283987537539)
              ·
                refine ⟨13163176839867425981306309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8775451226578283987537539 13163176839867425981306309)
                ·
                  refine ⟨2468095657475142371494933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13163176839867425981306309 2468095657475142371494933)
                  ·
                    refine ⟨115691983944147298663825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2468095657475142371494933 115691983944147298663825)
                    ·
                      rfl

theorem cell22_337964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_337964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337964 prefixEnd_337964 := by exact prefixLift 337964
  have htrace : WordTrace (prefixWord ++ tailWord_337964) baseStart_337964 baseEnd_337964 := by
    simpa [prefixWord, tailWord_337964, baseEnd_337964] using wordTrace_append hprefix tailTrace_337964
  have hstable : (prefixWord ++ tailWord_337964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337964).length < 2 ^ (prefixWord ++ tailWord_337964).sum := by decide
  have hdescent : baseEnd_337964 < baseStart_337964 := by decide
  rcases family_descends (prefixWord ++ tailWord_337964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337996 : List Nat := [2, 2, 1, 3, 1, 1, 3, 4, 5]
def baseStart_337996 : Nat := 118140960795 + 337996 * 2 ^ 59
def prefixEnd_337996 : Nat := 4983230072969 + 3 ^ 40 * 337996 * 2
def baseEnd_337996 : Nat := 38567646066036627287909

theorem tailTrace_337996 : CollatzResearch.WordTrace tailWord_337996 prefixEnd_337996 38567646066036627287909 := by
  unfold tailWord_337996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6163863441752845983088921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8218484589003794644118561 6163863441752845983088921)
  ·
    refine ⟨4622897581314634487316691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6163863441752845983088921 4622897581314634487316691)
    ·
      refine ⟨6934346371971951730975037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4622897581314634487316691 6934346371971951730975037)
      ·
        refine ⟨2600379889489481899115639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6934346371971951730975037 2600379889489481899115639)
        ·
          refine ⟨3900569834234222848673459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600379889489481899115639 3900569834234222848673459)
          ·
            refine ⟨5850854751351334273010189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900569834234222848673459 5850854751351334273010189)
            ·
              refine ⟨2194070531756750352378821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5850854751351334273010189 2194070531756750352378821)
              ·
                refine ⟨411388224704390691071029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2194070531756750352378821 411388224704390691071029)
                ·
                  refine ⟨38567646066036627287909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 411388224704390691071029 38567646066036627287909)
                  ·
                    rfl

theorem cell22_337996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_337996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_337996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_337996 prefixEnd_337996 := by exact prefixLift 337996
  have htrace : WordTrace (prefixWord ++ tailWord_337996) baseStart_337996 baseEnd_337996 := by
    simpa [prefixWord, tailWord_337996, baseEnd_337996] using wordTrace_append hprefix tailTrace_337996
  have hstable : (prefixWord ++ tailWord_337996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337996).length < 2 ^ (prefixWord ++ tailWord_337996).sum := by decide
  have hdescent : baseEnd_337996 < baseStart_337996 := by decide
  rcases family_descends (prefixWord ++ tailWord_337996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338058 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 6]
def baseStart_338058 : Nat := 118140960795 + 338058 * 2 ^ 59
def prefixEnd_338058 : Nat := 4983230072969 + 3 ^ 40 * 338058 * 2
def baseEnd_338058 : Nat := 38574720688387462271179

theorem tailTrace_338058 : CollatzResearch.WordTrace tailWord_338058 prefixEnd_338058 38574720688387462271179 := by
  unfold tailWord_338058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082497052320269138733707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8219992139520717703289885 3082497052320269138733707)
  ·
    refine ⟨4623745578480403708100561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3082497052320269138733707 4623745578480403708100561)
    ·
      refine ⟨3467809183860302781075421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4623745578480403708100561 3467809183860302781075421)
      ·
        refine ⟨1300428443947613542903283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3467809183860302781075421 1300428443947613542903283)
        ·
          refine ⟨1950642665921420314354925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1300428443947613542903283 1950642665921420314354925)
          ·
            refine ⟨731490999720532617883097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1950642665921420314354925 731490999720532617883097)
            ·
              refine ⟨548618249790399463412323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 731490999720532617883097 548618249790399463412323)
              ·
                refine ⟨822927374685599195118485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548618249790399463412323 822927374685599195118485)
                ·
                  refine ⟨38574720688387462271179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 822927374685599195118485 38574720688387462271179)
                  ·
                    rfl

theorem cell22_338058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_338058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338058 prefixEnd_338058 := by exact prefixLift 338058
  have htrace : WordTrace (prefixWord ++ tailWord_338058) baseStart_338058 baseEnd_338058 := by
    simpa [prefixWord, tailWord_338058, baseEnd_338058] using wordTrace_append hprefix tailTrace_338058
  have hstable : (prefixWord ++ tailWord_338058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338058).length < 2 ^ (prefixWord ++ tailWord_338058).sum := by decide
  have hdescent : baseEnd_338058 < baseStart_338058 := by decide
  rcases family_descends (prefixWord ++ tailWord_338058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338073 : List Nat := [1, 2, 1, 2, 1, 2, 1, 7, 2, 3]
def baseStart_338073 : Nat := 118140960795 + 338073 * 2 ^ 59
def prefixEnd_338073 : Nat := 4983230072969 + 3 ^ 40 * 338073 * 2
def baseEnd_338073 : Nat := 115729296871707347688491

theorem tailTrace_338073 : CollatzResearch.WordTrace tailWord_338073 prefixEnd_338073 115729296871707347688491 := by
  unfold tailWord_338073
  simp only [CollatzResearch.WordTrace]
  refine ⟨12330535304226734116730873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8220356869484489411153915 12330535304226734116730873)
  ·
    refine ⟨9247901478170050587548155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12330535304226734116730873 9247901478170050587548155)
    ·
      refine ⟨13871852217255075881322233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9247901478170050587548155 13871852217255075881322233)
      ·
        refine ⟨10403889162941306910991675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13871852217255075881322233 10403889162941306910991675)
        ·
          refine ⟨15605833744411960366487513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10403889162941306910991675 15605833744411960366487513)
          ·
            refine ⟨11704375308308970274865635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15605833744411960366487513 11704375308308970274865635)
            ·
              refine ⟨17556562962463455412298453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11704375308308970274865635 17556562962463455412298453)
              ·
                refine ⟨411481944432737236225745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17556562962463455412298453 411481944432737236225745)
                ·
                  refine ⟨308611458324552927169309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411481944432737236225745 308611458324552927169309)
                  ·
                    refine ⟨115729296871707347688491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 308611458324552927169309 115729296871707347688491)
                    ·
                      rfl

theorem cell22_338073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 3].length) (baseStart_338073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338073 prefixEnd_338073 := by exact prefixLift 338073
  have htrace : WordTrace (prefixWord ++ tailWord_338073) baseStart_338073 baseEnd_338073 := by
    simpa [prefixWord, tailWord_338073, baseEnd_338073] using wordTrace_append hprefix tailTrace_338073
  have hstable : (prefixWord ++ tailWord_338073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338073).length < 2 ^ (prefixWord ++ tailWord_338073).sum := by decide
  have hdescent : baseEnd_338073 < baseStart_338073 := by decide
  rcases family_descends (prefixWord ++ tailWord_338073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338180 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_338180 : Nat := 118140960795 + 338180 * 2 ^ 59
def prefixEnd_338180 : Nat := 4983230072969 + 3 ^ 40 * 338180 * 2
def baseEnd_338180 : Nat := 115765925158394735263163

theorem tailTrace_338180 : CollatzResearch.WordTrace tailWord_338180 prefixEnd_338180 115765925158394735263163 := by
  unfold tailWord_338180
  simp only [CollatzResearch.WordTrace]
  refine ⟨6167218957419545695437997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8222958609892727593917329 6167218957419545695437997)
  ·
    refine ⟨2312707109032329635789249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6167218957419545695437997 2312707109032329635789249)
    ·
      refine ⟨1734530331774247226841937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2312707109032329635789249 1734530331774247226841937)
      ·
        refine ⟨1300897748830685420131453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1734530331774247226841937 1300897748830685420131453)
        ·
          refine ⟨487836655811507032549295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1300897748830685420131453 487836655811507032549295)
          ·
            refine ⟨731754983717260548823943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487836655811507032549295 731754983717260548823943)
            ·
              refine ⟨1097632475575890823235915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731754983717260548823943 1097632475575890823235915)
              ·
                refine ⟨1646448713363836234853873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097632475575890823235915 1646448713363836234853873)
                ·
                  refine ⟨1234836535022877176140405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1646448713363836234853873 1234836535022877176140405)
                  ·
                    refine ⟨115765925158394735263163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1234836535022877176140405 115765925158394735263163)
                    ·
                      rfl

theorem cell22_338180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_338180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338180 prefixEnd_338180 := by exact prefixLift 338180
  have htrace : WordTrace (prefixWord ++ tailWord_338180) baseStart_338180 baseEnd_338180 := by
    simpa [prefixWord, tailWord_338180, baseEnd_338180] using wordTrace_append hprefix tailTrace_338180
  have hstable : (prefixWord ++ tailWord_338180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338180).length < 2 ^ (prefixWord ++ tailWord_338180).sum := by decide
  have hdescent : baseEnd_338180 < baseStart_338180 := by decide
  rcases family_descends (prefixWord ++ tailWord_338180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338193 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 6]
def baseStart_338193 : Nat := 118140960795 + 338193 * 2 ^ 59
def prefixEnd_338193 : Nat := 4983230072969 + 3 ^ 40 * 338193 * 2
def baseEnd_338193 : Nat := 38590125108022344896041

theorem tailTrace_338193 : CollatzResearch.WordTrace tailWord_338193 prefixEnd_338193 38590125108022344896041 := by
  unfold tailWord_338193
  simp only [CollatzResearch.WordTrace]
  refine ⟨12334912063791994611099233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8223274709194663074066155 12334912063791994611099233)
  ·
    refine ⟨9251184047843995958324425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12334912063791994611099233 9251184047843995958324425)
    ·
      refine ⟨6938388035882996968743319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9251184047843995958324425 6938388035882996968743319)
      ·
        refine ⟨10407582053824495453114979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6938388035882996968743319 10407582053824495453114979)
        ·
          refine ⟨15611373080736743179672469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10407582053824495453114979 15611373080736743179672469)
          ·
            refine ⟨731783113159534836547147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15611373080736743179672469 731783113159534836547147)
            ·
              refine ⟨1097674669739302254820721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731783113159534836547147 1097674669739302254820721)
              ·
                refine ⟨823256002304476691115541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097674669739302254820721 823256002304476691115541)
                ·
                  refine ⟨38590125108022344896041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 823256002304476691115541 38590125108022344896041)
                  ·
                    rfl

theorem cell22_338193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_338193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338193 prefixEnd_338193 := by exact prefixLift 338193
  have htrace : WordTrace (prefixWord ++ tailWord_338193) baseStart_338193 baseEnd_338193 := by
    simpa [prefixWord, tailWord_338193, baseEnd_338193] using wordTrace_append hprefix tailTrace_338193
  have hstable : (prefixWord ++ tailWord_338193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338193).length < 2 ^ (prefixWord ++ tailWord_338193).sum := by decide
  have hdescent : baseEnd_338193 < baseStart_338193 := by decide
  rcases family_descends (prefixWord ++ tailWord_338193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338212 : List Nat := [2, 3, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_338212 : Nat := 118140960795 + 338212 * 2 ^ 59
def prefixEnd_338212 : Nat := 4983230072969 + 3 ^ 40 * 338212 * 2
def baseEnd_338212 : Nat := 115776879412357318463065

theorem tailTrace_338212 : CollatzResearch.WordTrace tailWord_338212 prefixEnd_338212 115776879412357318463065 := by
  unfold tailWord_338212
  simp only [CollatzResearch.WordTrace]
  refine ⟨6167802525361580428020445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8223736700482107237360593 6167802525361580428020445)
  ·
    refine ⟨2312925947010592660507667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6167802525361580428020445 2312925947010592660507667)
    ·
      refine ⟨3469388920515888990761501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2312925947010592660507667 3469388920515888990761501)
      ·
        refine ⟨1301020845193458371535563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3469388920515888990761501 1301020845193458371535563)
        ·
          refine ⟨1951531267790187557303345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1301020845193458371535563 1951531267790187557303345)
          ·
            refine ⟨1463648450842640667977509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1951531267790187557303345 1463648450842640667977509)
            ·
              refine ⟨274434084532995125245783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1463648450842640667977509 274434084532995125245783)
              ·
                refine ⟨411651126799492687868675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274434084532995125245783 411651126799492687868675)
                ·
                  refine ⟨617476690199239031803013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411651126799492687868675 617476690199239031803013)
                  ·
                    refine ⟨115776879412357318463065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 617476690199239031803013 115776879412357318463065)
                    ·
                      rfl

theorem cell22_338212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_338212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338212 prefixEnd_338212 := by exact prefixLift 338212
  have htrace : WordTrace (prefixWord ++ tailWord_338212) baseStart_338212 baseEnd_338212 := by
    simpa [prefixWord, tailWord_338212, baseEnd_338212] using wordTrace_append hprefix tailTrace_338212
  have hstable : (prefixWord ++ tailWord_338212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338212).length < 2 ^ (prefixWord ++ tailWord_338212).sum := by decide
  have hdescent : baseEnd_338212 < baseStart_338212 := by decide
  rcases family_descends (prefixWord ++ tailWord_338212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338223 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 2, 4]
def baseStart_338223 : Nat := 118140960795 + 338223 * 2 ^ 59
def prefixEnd_338223 : Nat := 4983230072969 + 3 ^ 40 * 338223 * 2
def baseEnd_338223 : Nat := 115780644937156956438031

theorem tailTrace_338223 : CollatzResearch.WordTrace tailWord_338223 prefixEnd_338223 115780644937156956438031 := by
  unfold tailWord_338223
  simp only [CollatzResearch.WordTrace]
  refine ⟨12336006253683309734691323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8224004169122206489794215 12336006253683309734691323)
  ·
    refine ⟨18504009380524964602036985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12336006253683309734691323 18504009380524964602036985)
    ·
      refine ⟨13878007035393723451527739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18504009380524964602036985 13878007035393723451527739)
      ·
        refine ⟨20817010553090585177291609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13878007035393723451527739 20817010553090585177291609)
        ·
          refine ⟨15612757914817938882968707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20817010553090585177291609 15612757914817938882968707)
          ·
            refine ⟨23419136872226908324453061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15612757914817938882968707 23419136872226908324453061)
            ·
              refine ⟨4391088163542545310834949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23419136872226908324453061 4391088163542545310834949)
              ·
                refine ⟨823329030664227245781553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4391088163542545310834949 823329030664227245781553)
                ·
                  refine ⟨617496772998170434336165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 823329030664227245781553 617496772998170434336165)
                  ·
                    refine ⟨115780644937156956438031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 617496772998170434336165 115780644937156956438031)
                    ·
                      rfl

theorem cell22_338223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_338223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338223 prefixEnd_338223 := by exact prefixLift 338223
  have htrace : WordTrace (prefixWord ++ tailWord_338223) baseStart_338223 baseEnd_338223 := by
    simpa [prefixWord, tailWord_338223, baseEnd_338223] using wordTrace_append hprefix tailTrace_338223
  have hstable : (prefixWord ++ tailWord_338223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338223).length < 2 ^ (prefixWord ++ tailWord_338223).sum := by decide
  have hdescent : baseEnd_338223 < baseStart_338223 := by decide
  rcases family_descends (prefixWord ++ tailWord_338223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338334 : List Nat := [4, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_338334 : Nat := 118140960795 + 338334 * 2 ^ 59
def prefixEnd_338334 : Nat := 4983230072969 + 3 ^ 40 * 338334 * 2
def baseEnd_338334 : Nat := 38606214168529888970897

theorem tailTrace_338334 : CollatzResearch.WordTrace tailWord_338334 prefixEnd_338334 38606214168529888970897 := by
  unfold tailWord_338334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1542506844535146961497757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8226703170854117127988037 1542506844535146961497757)
  ·
    refine ⟨578440066700680110561659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1542506844535146961497757 578440066700680110561659)
    ·
      refine ⟨867660100051020165842489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 578440066700680110561659 867660100051020165842489)
      ·
        refine ⟨650745075038265124381867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 867660100051020165842489 650745075038265124381867)
        ·
          refine ⟨976117612557397686572801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650745075038265124381867 976117612557397686572801)
          ·
            refine ⟨732088209418048264929601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 976117612557397686572801 732088209418048264929601)
            ·
              refine ⟨549066157063536198697201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 732088209418048264929601 549066157063536198697201)
              ·
                refine ⟨411799617797652149022901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549066157063536198697201 411799617797652149022901)
                ·
                  refine ⟨38606214168529888970897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 411799617797652149022901 38606214168529888970897)
                  ·
                    rfl

theorem cell22_338334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_338334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338334 prefixEnd_338334 := by exact prefixLift 338334
  have htrace : WordTrace (prefixWord ++ tailWord_338334) baseStart_338334 baseEnd_338334 := by
    simpa [prefixWord, tailWord_338334, baseEnd_338334] using wordTrace_append hprefix tailTrace_338334
  have hstable : (prefixWord ++ tailWord_338334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338334).length < 2 ^ (prefixWord ++ tailWord_338334).sum := by decide
  have hdescent : baseEnd_338334 < baseStart_338334 := by decide
  rcases family_descends (prefixWord ++ tailWord_338334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338360 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 6, 3]
def baseStart_338360 : Nat := 118140960795 + 338360 * 2 ^ 59
def prefixEnd_338360 : Nat := 4983230072969 + 3 ^ 40 * 338360 * 2
def baseEnd_338360 : Nat := 115827542836934265762611

theorem tailTrace_338360 : CollatzResearch.WordTrace tailWord_338360 prefixEnd_338360 115827542836934265762611 := by
  unfold tailWord_338360
  simp only [CollatzResearch.WordTrace]
  refine ⟨6170501527093491066214267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8227335369457988088285689 6170501527093491066214267)
  ·
    refine ⟨9255752290640236599321401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6170501527093491066214267 9255752290640236599321401)
    ·
      refine ⟨6941814217980177449491051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9255752290640236599321401 6941814217980177449491051)
      ·
        refine ⟨10412721326970266174236577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6941814217980177449491051 10412721326970266174236577)
        ·
          refine ⟨7809540995227699630677433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10412721326970266174236577 7809540995227699630677433)
          ·
            refine ⟨5857155746420774723008075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7809540995227699630677433 5857155746420774723008075)
            ·
              refine ⟨8785733619631162084512113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5857155746420774723008075 8785733619631162084512113)
              ·
                refine ⟨6589300214723371563384085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8785733619631162084512113 6589300214723371563384085)
                ·
                  refine ⟨308873447565158042033629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6589300214723371563384085 308873447565158042033629)
                  ·
                    refine ⟨115827542836934265762611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 308873447565158042033629 115827542836934265762611)
                    ·
                      rfl

theorem cell22_338360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_338360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338360 prefixEnd_338360 := by exact prefixLift 338360
  have htrace : WordTrace (prefixWord ++ tailWord_338360) baseStart_338360 baseEnd_338360 := by
    simpa [prefixWord, tailWord_338360, baseEnd_338360] using wordTrace_append hprefix tailTrace_338360
  have hstable : (prefixWord ++ tailWord_338360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338360).length < 2 ^ (prefixWord ++ tailWord_338360).sum := by decide
  have hdescent : baseEnd_338360 < baseStart_338360 := by decide
  rcases family_descends (prefixWord ++ tailWord_338360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338375 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 1, 6]
def baseStart_338375 : Nat := 118140960795 + 338375 * 2 ^ 59
def prefixEnd_338375 : Nat := 4983230072969 + 3 ^ 40 * 338375 * 2
def baseEnd_338375 : Nat := 115832677643479226637565

theorem tailTrace_338375 : CollatzResearch.WordTrace tailWord_338375 prefixEnd_338375 115832677643479226637565 := by
  unfold tailWord_338375
  simp only [CollatzResearch.WordTrace]
  refine ⟨12341550149132639694224579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8227700099421759796149719 12341550149132639694224579)
  ·
    refine ⟨18512325223698959541336869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12341550149132639694224579 18512325223698959541336869)
    ·
      refine ⟨3471060979443554914000663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18512325223698959541336869 3471060979443554914000663)
      ·
        refine ⟨5206591469165332371000995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3471060979443554914000663 5206591469165332371000995)
        ·
          refine ⟨7809887203747998556501493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5206591469165332371000995 7809887203747998556501493)
          ·
            refine ⟨732176925351374864672015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7809887203747998556501493 732176925351374864672015)
            ·
              refine ⟨1098265388027062297008023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732176925351374864672015 1098265388027062297008023)
              ·
                refine ⟨1647398082040593445512035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098265388027062297008023 1647398082040593445512035)
                ·
                  refine ⟨2471097123060890168268053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647398082040593445512035 2471097123060890168268053)
                  ·
                    refine ⟨115832677643479226637565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2471097123060890168268053 115832677643479226637565)
                    ·
                      rfl

theorem cell22_338375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_338375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338375 prefixEnd_338375 := by exact prefixLift 338375
  have htrace : WordTrace (prefixWord ++ tailWord_338375) baseStart_338375 baseEnd_338375 := by
    simpa [prefixWord, tailWord_338375, baseEnd_338375] using wordTrace_append hprefix tailTrace_338375
  have hstable : (prefixWord ++ tailWord_338375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338375).length < 2 ^ (prefixWord ++ tailWord_338375).sum := by decide
  have hdescent : baseEnd_338375 < baseStart_338375 := by decide
  rcases family_descends (prefixWord ++ tailWord_338375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338480 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 6]
def baseStart_338480 : Nat := 118140960795 + 338480 * 2 ^ 59
def prefixEnd_338480 : Nat := 4983230072969 + 3 ^ 40 * 338480 * 2
def baseEnd_338480 : Nat := 38622873763097984254081

theorem tailTrace_338480 : CollatzResearch.WordTrace tailWord_338480 prefixEnd_338480 38622873763097984254081 := by
  unfold tailWord_338480
  simp only [CollatzResearch.WordTrace]
  refine ⟨6172689906876121313398447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8230253209168161751197929 6172689906876121313398447)
  ·
    refine ⟨9259034860314181970097671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6172689906876121313398447 9259034860314181970097671)
    ·
      refine ⟨13888552290471272955146507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9259034860314181970097671 13888552290471272955146507)
      ·
        refine ⟨20832828435706909432719761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13888552290471272955146507 20832828435706909432719761)
        ·
          refine ⟨15624621326780182074539821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20832828435706909432719761 15624621326780182074539821)
          ·
            refine ⟨5859232997542568277952433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15624621326780182074539821 5859232997542568277952433)
            ·
              refine ⟨4394424748156926208464325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5859232997542568277952433 4394424748156926208464325)
              ·
                refine ⟨823954640279423664087061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4394424748156926208464325 823954640279423664087061)
                ·
                  refine ⟨38622873763097984254081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 823954640279423664087061 38622873763097984254081)
                  ·
                    rfl

theorem cell22_338480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_338480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338480 prefixEnd_338480 := by exact prefixLift 338480
  have htrace : WordTrace (prefixWord ++ tailWord_338480) baseStart_338480 baseEnd_338480 := by
    simpa [prefixWord, tailWord_338480, baseEnd_338480] using wordTrace_append hprefix tailTrace_338480
  have hstable : (prefixWord ++ tailWord_338480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338480).length < 2 ^ (prefixWord ++ tailWord_338480).sum := by decide
  have hdescent : baseEnd_338480 < baseStart_338480 := by decide
  rcases family_descends (prefixWord ++ tailWord_338480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338514 : List Nat := [3, 2, 2, 1, 2, 1, 3, 4, 4]
def baseStart_338514 : Nat := 118140960795 + 338514 * 2 ^ 59
def prefixEnd_338514 : Nat := 4983230072969 + 3 ^ 40 * 338514 * 2
def baseEnd_338514 : Nat := 38626753394709732470713

theorem tailTrace_338514 : CollatzResearch.WordTrace tailWord_338514 prefixEnd_338514 38626753394709732470713 := by
  unfold tailWord_338514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3086654973907266608383649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8231079930419377622356397 3086654973907266608383649)
  ·
    refine ⟨2314991230430449956287737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3086654973907266608383649 2314991230430449956287737)
    ·
      refine ⟨1736243422822837467215803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2314991230430449956287737 1736243422822837467215803)
      ·
        refine ⟨2604365134234256200823705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1736243422822837467215803 2604365134234256200823705)
        ·
          refine ⟨1953273850675692150617779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2604365134234256200823705 1953273850675692150617779)
          ·
            refine ⟨2929910776013538225926669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1953273850675692150617779 2929910776013538225926669)
            ·
              refine ⟨1098716541005076834722501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2929910776013538225926669 1098716541005076834722501)
              ·
                refine ⟨206009351438451906510469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1098716541005076834722501 206009351438451906510469)
                ·
                  refine ⟨38626753394709732470713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 206009351438451906510469 38626753394709732470713)
                  ·
                    rfl

theorem cell22_338514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_338514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338514 prefixEnd_338514 := by exact prefixLift 338514
  have htrace : WordTrace (prefixWord ++ tailWord_338514) baseStart_338514 baseEnd_338514 := by
    simpa [prefixWord, tailWord_338514, baseEnd_338514] using wordTrace_append hprefix tailTrace_338514
  have hstable : (prefixWord ++ tailWord_338514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338514).length < 2 ^ (prefixWord ++ tailWord_338514).sum := by decide
  have hdescent : baseEnd_338514 < baseStart_338514 := by decide
  rcases family_descends (prefixWord ++ tailWord_338514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338529 : List Nat := [1, 2, 3, 1, 1, 4, 2, 3, 2, 3]
def baseStart_338529 : Nat := 118140960795 + 338529 * 2 ^ 59
def prefixEnd_338529 : Nat := 4983230072969 + 3 ^ 40 * 338529 * 2
def baseEnd_338529 : Nat := 115885394990674158287093

theorem tailTrace_338529 : CollatzResearch.WordTrace tailWord_338529 prefixEnd_338529 115885394990674158287093 := by
  unfold tailWord_338529
  simp only [CollatzResearch.WordTrace]
  refine ⟨12347166990574723995330641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8231444660383149330220427 12347166990574723995330641)
  ·
    refine ⟨9260375242931042996497981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12347166990574723995330641 9260375242931042996497981)
    ·
      refine ⟨3472640716099141123686743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9260375242931042996497981 3472640716099141123686743)
      ·
        refine ⟨5208961074148711685530115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472640716099141123686743 5208961074148711685530115)
        ·
          refine ⟨7813441611223067528295173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5208961074148711685530115 7813441611223067528295173)
          ·
            refine ⟨1465020302104325161555345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7813441611223067528295173 1465020302104325161555345)
            ·
              refine ⟨1098765226578243871166509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1465020302104325161555345 1098765226578243871166509)
              ·
                refine ⟨412036959966841451687441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1098765226578243871166509 412036959966841451687441)
                ·
                  refine ⟨309027719975131088765581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412036959966841451687441 309027719975131088765581)
                  ·
                    refine ⟨115885394990674158287093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309027719975131088765581 115885394990674158287093)
                    ·
                      rfl

theorem cell22_338529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_338529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338529 prefixEnd_338529 := by exact prefixLift 338529
  have htrace : WordTrace (prefixWord ++ tailWord_338529) baseStart_338529 baseEnd_338529 := by
    simpa [prefixWord, tailWord_338529, baseEnd_338529] using wordTrace_append hprefix tailTrace_338529
  have hstable : (prefixWord ++ tailWord_338529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338529).length < 2 ^ (prefixWord ++ tailWord_338529).sum := by decide
  have hdescent : baseEnd_338529 < baseStart_338529 := by decide
  rcases family_descends (prefixWord ++ tailWord_338529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338550 : List Nat := [5, 1, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_338550 : Nat := 118140960795 + 338550 * 2 ^ 59
def prefixEnd_338550 : Nat := 4983230072969 + 3 ^ 40 * 338550 * 2
def baseEnd_338550 : Nat := 115892583719837103512029

theorem tailTrace_338550 : CollatzResearch.WordTrace tailWord_338550 prefixEnd_338550 115892583719837103512029 := by
  unfold tailWord_338550
  simp only [CollatzResearch.WordTrace]
  refine ⟨771745807718665286365319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8231955282332429721230069 771745807718665286365319)
  ·
    refine ⟨1157618711577997929547979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 771745807718665286365319 1157618711577997929547979)
    ·
      refine ⟨1736428067366996894321969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1157618711577997929547979 1736428067366996894321969)
      ·
        refine ⟨1302321050525247670741477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1736428067366996894321969 1302321050525247670741477)
        ·
          refine ⟨244185196973483938264027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1302321050525247670741477 244185196973483938264027)
          ·
            refine ⟨366277795460225907396041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244185196973483938264027 366277795460225907396041)
            ·
              refine ⟨274708346595169430547031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366277795460225907396041 274708346595169430547031)
              ·
                refine ⟨412062519892754145820547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274708346595169430547031 412062519892754145820547)
                ·
                  refine ⟨618093779839131218730821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412062519892754145820547 618093779839131218730821)
                  ·
                    refine ⟨115892583719837103512029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 618093779839131218730821 115892583719837103512029)
                    ·
                      rfl

theorem cell22_338550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_338550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338550 prefixEnd_338550 := by exact prefixLift 338550
  have htrace : WordTrace (prefixWord ++ tailWord_338550) baseStart_338550 baseEnd_338550 := by
    simpa [prefixWord, tailWord_338550, baseEnd_338550] using wordTrace_append hprefix tailTrace_338550
  have hstable : (prefixWord ++ tailWord_338550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338550).length < 2 ^ (prefixWord ++ tailWord_338550).sum := by decide
  have hdescent : baseEnd_338550 < baseStart_338550 := by decide
  rcases family_descends (prefixWord ++ tailWord_338550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338555 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 1, 8]
def baseStart_338555 : Nat := 118140960795 + 338555 * 2 ^ 59
def prefixEnd_338555 : Nat := 4983230072969 + 3 ^ 40 * 338555 * 2
def baseEnd_338555 : Nat := 115894295322018757137013

theorem tailTrace_338555 : CollatzResearch.WordTrace tailWord_338555 prefixEnd_338555 115894295322018757137013 := by
  unfold tailWord_338555
  simp only [CollatzResearch.WordTrace]
  refine ⟨12348115288480530435777119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8232076858987020290518079 12348115288480530435777119)
  ·
    refine ⟨18522172932720795653665679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12348115288480530435777119 18522172932720795653665679)
    ·
      refine ⟨27783259399081193480498519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18522172932720795653665679 27783259399081193480498519)
      ·
        refine ⟨41674889098621790220747779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27783259399081193480498519 41674889098621790220747779)
        ·
          refine ⟨62512333647932685331121669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41674889098621790220747779 62512333647932685331121669)
          ·
            refine ⟨11721062558987378499585313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62512333647932685331121669 11721062558987378499585313)
            ·
              refine ⟨8790796919240533874688985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11721062558987378499585313 8790796919240533874688985)
              ·
                refine ⟨6593097689430400406016739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8790796919240533874688985 6593097689430400406016739)
                ·
                  refine ⟨9889646534145600609025109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6593097689430400406016739 9889646534145600609025109)
                  ·
                    refine ⟨115894295322018757137013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9889646534145600609025109 115894295322018757137013)
                    ·
                      rfl

theorem cell22_338555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_338555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338555 prefixEnd_338555 := by exact prefixLift 338555
  have htrace : WordTrace (prefixWord ++ tailWord_338555) baseStart_338555 baseEnd_338555 := by
    simpa [prefixWord, tailWord_338555, baseEnd_338555] using wordTrace_append hprefix tailTrace_338555
  have hstable : (prefixWord ++ tailWord_338555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338555).length < 2 ^ (prefixWord ++ tailWord_338555).sum := by decide
  have hdescent : baseEnd_338555 < baseStart_338555 := by decide
  rcases family_descends (prefixWord ++ tailWord_338555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338617 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 5, 4]
def baseStart_338617 : Nat := 118140960795 + 338617 * 2 ^ 59
def prefixEnd_338617 : Nat := 4983230072969 + 3 ^ 40 * 338617 * 2
def baseEnd_338617 : Nat := 115915519189071262086823

theorem tailTrace_338617 : CollatzResearch.WordTrace tailWord_338617 prefixEnd_338617 115915519189071262086823 := by
  unfold tailWord_338617
  simp only [CollatzResearch.WordTrace]
  refine ⟨12350376614255915024534105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8233584409503943349689403 12350376614255915024534105)
  ·
    refine ⟨9262782460691936268400579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12350376614255915024534105 9262782460691936268400579)
    ·
      refine ⟨13894173691037904402600869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9262782460691936268400579 13894173691037904402600869)
      ·
        refine ⟨2605157567069607075487663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13894173691037904402600869 2605157567069607075487663)
        ·
          refine ⟨3907736350604410613231495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2605157567069607075487663 3907736350604410613231495)
          ·
            refine ⟨5861604525906615919847243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3907736350604410613231495 5861604525906615919847243)
            ·
              refine ⟨8792406788859923879770865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5861604525906615919847243 8792406788859923879770865)
              ·
                refine ⟨6594305091644942909828149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8792406788859923879770865 6594305091644942909828149)
                ·
                  refine ⟨618216102341713397796389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6594305091644942909828149 618216102341713397796389)
                  ·
                    refine ⟨115915519189071262086823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 618216102341713397796389 115915519189071262086823)
                    ·
                      rfl

theorem cell22_338617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_338617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338617 prefixEnd_338617 := by exact prefixLift 338617
  have htrace : WordTrace (prefixWord ++ tailWord_338617) baseStart_338617 baseEnd_338617 := by
    simpa [prefixWord, tailWord_338617, baseEnd_338617] using wordTrace_append hprefix tailTrace_338617
  have hstable : (prefixWord ++ tailWord_338617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338617).length < 2 ^ (prefixWord ++ tailWord_338617).sum := by decide
  have hdescent : baseEnd_338617 < baseStart_338617 := by decide
  rcases family_descends (prefixWord ++ tailWord_338617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338625 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 3, 3]
def baseStart_338625 : Nat := 118140960795 + 338625 * 2 ^ 59
def prefixEnd_338625 : Nat := 4983230072969 + 3 ^ 40 * 338625 * 2
def baseEnd_338625 : Nat := 115918257752561907886799

theorem tailTrace_338625 : CollatzResearch.WordTrace tailWord_338625 prefixEnd_338625 115918257752561907886799 := by
  unfold tailWord_338625
  simp only [CollatzResearch.WordTrace]
  refine ⟨12350668398226932390825329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8233778932151288260550219 12350668398226932390825329)
  ·
    refine ⟨9263001298670199293118997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12350668398226932390825329 9263001298670199293118997)
    ·
      refine ⟨434203185875165591864953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9263001298670199293118997 434203185875165591864953)
      ·
        refine ⟨325652389406374193898715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434203185875165591864953 325652389406374193898715)
        ·
          refine ⟨488478584109561290848073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325652389406374193898715 488478584109561290848073)
          ·
            refine ⟨366358938082170968136055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488478584109561290848073 366358938082170968136055)
            ·
              refine ⟨549538407123256452204083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366358938082170968136055 549538407123256452204083)
              ·
                refine ⟨824307610684884678306125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549538407123256452204083 824307610684884678306125)
                ·
                  refine ⟨309115354006831754364797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824307610684884678306125 309115354006831754364797)
                  ·
                    refine ⟨115918257752561907886799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309115354006831754364797 115918257752561907886799)
                    ·
                      rfl

theorem cell22_338625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_338625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338625 prefixEnd_338625 := by exact prefixLift 338625
  have htrace : WordTrace (prefixWord ++ tailWord_338625) baseStart_338625 baseEnd_338625 := by
    simpa [prefixWord, tailWord_338625, baseEnd_338625] using wordTrace_append hprefix tailTrace_338625
  have hstable : (prefixWord ++ tailWord_338625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338625).length < 2 ^ (prefixWord ++ tailWord_338625).sum := by decide
  have hdescent : baseEnd_338625 < baseStart_338625 := by decide
  rcases family_descends (prefixWord ++ tailWord_338625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338676 : List Nat := [2, 6, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_338676 : Nat := 118140960795 + 338676 * 2 ^ 59
def prefixEnd_338676 : Nat := 4983230072969 + 3 ^ 40 * 338676 * 2
def baseEnd_338676 : Nat := 115935716094814774861643

theorem tailTrace_338676 : CollatzResearch.WordTrace tailWord_338676 prefixEnd_338676 115935716094814774861643 := by
  unfold tailWord_338676
  simp only [CollatzResearch.WordTrace]
  refine ⟨6176264260521084050465941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8235019014028112067287921 6176264260521084050465941)
  ·
    refine ⟨289512387211925814865591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6176264260521084050465941 289512387211925814865591)
    ·
      refine ⟨434268580817888722298387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289512387211925814865591 434268580817888722298387)
      ·
        refine ⟨651402871226833083447581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434268580817888722298387 651402871226833083447581)
        ·
          refine ⟨244276076710062406292843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 651402871226833083447581 244276076710062406292843)
          ·
            refine ⟨366414115065093609439265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244276076710062406292843 366414115065093609439265)
            ·
              refine ⟨274810586298820207079449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366414115065093609439265 274810586298820207079449)
              ·
                refine ⟨206107939724115155309587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274810586298820207079449 206107939724115155309587)
                ·
                  refine ⟨309161909586172732964381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206107939724115155309587 309161909586172732964381)
                  ·
                    refine ⟨115935716094814774861643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309161909586172732964381 115935716094814774861643)
                    ·
                      rfl

theorem cell22_338676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_338676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338676 prefixEnd_338676 := by exact prefixLift 338676
  have htrace : WordTrace (prefixWord ++ tailWord_338676) baseStart_338676 baseEnd_338676 := by
    simpa [prefixWord, tailWord_338676, baseEnd_338676] using wordTrace_append hprefix tailTrace_338676
  have hstable : (prefixWord ++ tailWord_338676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338676).length < 2 ^ (prefixWord ++ tailWord_338676).sum := by decide
  have hdescent : baseEnd_338676 < baseStart_338676 := by decide
  rcases family_descends (prefixWord ++ tailWord_338676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338707 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 2, 6]
def baseStart_338707 : Nat := 118140960795 + 338707 * 2 ^ 59
def prefixEnd_338707 : Nat := 4983230072969 + 3 ^ 40 * 338707 * 2
def baseEnd_338707 : Nat := 115946328028341027336547

theorem tailTrace_338707 : CollatzResearch.WordTrace tailWord_338707 prefixEnd_338707 115946328028341027336547 := by
  unfold tailWord_338707
  simp only [CollatzResearch.WordTrace]
  refine ⟨12353659183929860395310375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8235772789286573596873583 12353659183929860395310375)
  ·
    refine ⟨18530488775894790592965563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12353659183929860395310375 18530488775894790592965563)
    ·
      refine ⟨27795733163842185889448345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18530488775894790592965563 27795733163842185889448345)
      ·
        refine ⟨20846799872881639417086259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27795733163842185889448345 20846799872881639417086259)
        ·
          refine ⟨31270199809322459125629389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20846799872881639417086259 31270199809322459125629389)
          ·
            refine ⟨11726324928495922172111021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31270199809322459125629389 11726324928495922172111021)
            ·
              refine ⟨4397371848185970814541633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11726324928495922172111021 4397371848185970814541633)
              ·
                refine ⟨3298028886139478110906225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4397371848185970814541633 3298028886139478110906225)
                ·
                  refine ⟨2473521664604608583179669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3298028886139478110906225 2473521664604608583179669)
                  ·
                    refine ⟨115946328028341027336547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2473521664604608583179669 115946328028341027336547)
                    ·
                      rfl

theorem cell22_338707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_338707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338707 prefixEnd_338707 := by exact prefixLift 338707
  have htrace : WordTrace (prefixWord ++ tailWord_338707) baseStart_338707 baseEnd_338707 := by
    simpa [prefixWord, tailWord_338707, baseEnd_338707] using wordTrace_append hprefix tailTrace_338707
  have hstable : (prefixWord ++ tailWord_338707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338707).length < 2 ^ (prefixWord ++ tailWord_338707).sum := by decide
  have hdescent : baseEnd_338707 < baseStart_338707 := by decide
  rcases family_descends (prefixWord ++ tailWord_338707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338711 : List Nat := [1, 1, 3, 4, 3, 1, 3, 6]
def baseStart_338711 : Nat := 118140960795 + 338711 * 2 ^ 59
def prefixEnd_338711 : Nat := 4983230072969 + 3 ^ 40 * 338711 * 2
def baseEnd_338711 : Nat := 12883077478898483359615

theorem tailTrace_338711 : CollatzResearch.WordTrace tailWord_338711 prefixEnd_338711 12883077478898483359615 := by
  unfold tailWord_338711
  simp only [CollatzResearch.WordTrace]
  refine ⟨12353805075915369078455987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8235870050610246052303991 12353805075915369078455987)
  ·
    refine ⟨18530707613873053617683981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12353805075915369078455987 18530707613873053617683981)
    ·
      refine ⟨6949015355202395106631493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18530707613873053617683981 6949015355202395106631493)
      ·
        refine ⟨1302940379100449082493405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6949015355202395106631493 1302940379100449082493405)
        ·
          refine ⟨488602642162668405935027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1302940379100449082493405 488602642162668405935027)
          ·
            refine ⟨732903963244002608902541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488602642162668405935027 732903963244002608902541)
            ·
              refine ⟨274838986216500978338453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 732903963244002608902541 274838986216500978338453)
              ·
                refine ⟨12883077478898483359615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 274838986216500978338453 12883077478898483359615)
                ·
                  rfl

theorem cell22_338711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 6].length) (baseStart_338711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338711 prefixEnd_338711 := by exact prefixLift 338711
  have htrace : WordTrace (prefixWord ++ tailWord_338711) baseStart_338711 baseEnd_338711 := by
    simpa [prefixWord, tailWord_338711, baseEnd_338711] using wordTrace_append hprefix tailTrace_338711
  have hstable : (prefixWord ++ tailWord_338711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338711).length < 2 ^ (prefixWord ++ tailWord_338711).sum := by decide
  have hdescent : baseEnd_338711 < baseStart_338711 := by decide
  rcases family_descends (prefixWord ++ tailWord_338711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338739 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 7]
def baseStart_338739 : Nat := 118140960795 + 338739 * 2 ^ 59
def prefixEnd_338739 : Nat := 4983230072969 + 3 ^ 40 * 338739 * 2
def baseEnd_338739 : Nat := 38652427427434536845483

theorem tailTrace_338739 : CollatzResearch.WordTrace tailWord_338739 prefixEnd_338739 38652427427434536845483 := by
  unfold tailWord_338739
  simp only [CollatzResearch.WordTrace]
  refine ⟨12354826319813929860475271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8236550879875953240316847 12354826319813929860475271)
  ·
    refine ⟨18532239479720894790712907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12354826319813929860475271 18532239479720894790712907)
    ·
      refine ⟨27798359219581342186069361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18532239479720894790712907 27798359219581342186069361)
      ·
        refine ⟨20848769414686006639552021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27798359219581342186069361 20848769414686006639552021)
        ·
          refine ⟨977286066313406561229001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20848769414686006639552021 977286066313406561229001)
          ·
            refine ⟨732964549735054920921751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977286066313406561229001 732964549735054920921751)
            ·
              refine ⟨1099446824602582381382627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732964549735054920921751 1099446824602582381382627)
              ·
                refine ⟨1649170236903873572073941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099446824602582381382627 1649170236903873572073941)
                ·
                  refine ⟨38652427427434536845483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1649170236903873572073941 38652427427434536845483)
                  ·
                    rfl

theorem cell22_338739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 7].length) (baseStart_338739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338739 prefixEnd_338739 := by exact prefixLift 338739
  have htrace : WordTrace (prefixWord ++ tailWord_338739) baseStart_338739 baseEnd_338739 := by
    simpa [prefixWord, tailWord_338739, baseEnd_338739] using wordTrace_append hprefix tailTrace_338739
  have hstable : (prefixWord ++ tailWord_338739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338739).length < 2 ^ (prefixWord ++ tailWord_338739).sum := by decide
  have hdescent : baseEnd_338739 < baseStart_338739 := by decide
  rcases family_descends (prefixWord ++ tailWord_338739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338801 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 6]
def baseStart_338801 : Nat := 118140960795 + 338801 * 2 ^ 59
def prefixEnd_338801 : Nat := 4983230072969 + 3 ^ 40 * 338801 * 2
def baseEnd_338801 : Nat := 38659502049785371828753

theorem tailTrace_338801 : CollatzResearch.WordTrace tailWord_338801 prefixEnd_338801 38659502049785371828753 := by
  unfold tailWord_338801
  simp only [CollatzResearch.WordTrace]
  refine ⟨12357087645589314449232257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8238058430392876299488171 12357087645589314449232257)
  ·
    refine ⟨9267815734191985836924193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12357087645589314449232257 9267815734191985836924193)
    ·
      refine ⟨6950861800643989377693145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9267815734191985836924193 6950861800643989377693145)
      ·
        refine ⟨5213146350482992033269859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6950861800643989377693145 5213146350482992033269859)
        ·
          refine ⟨7819719525724488049904789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213146350482992033269859 7819719525724488049904789)
          ·
            refine ⟨366549352768335377339287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7819719525724488049904789 366549352768335377339287)
            ·
              refine ⟨549824029152503066008931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366549352768335377339287 549824029152503066008931)
              ·
                refine ⟨824736043728754599013397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549824029152503066008931 824736043728754599013397)
                ·
                  refine ⟨38659502049785371828753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 824736043728754599013397 38659502049785371828753)
                  ·
                    rfl

theorem cell22_338801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 6].length) (baseStart_338801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338801 prefixEnd_338801 := by exact prefixLift 338801
  have htrace : WordTrace (prefixWord ++ tailWord_338801) baseStart_338801 baseEnd_338801 := by
    simpa [prefixWord, tailWord_338801, baseEnd_338801] using wordTrace_append hprefix tailTrace_338801
  have hstable : (prefixWord ++ tailWord_338801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338801).length < 2 ^ (prefixWord ++ tailWord_338801).sum := by decide
  have hdescent : baseEnd_338801 < baseStart_338801 := by decide
  rcases family_descends (prefixWord ++ tailWord_338801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338850 : List Nat := [3, 3, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_338850 : Nat := 118140960795 + 338850 * 2 ^ 59
def prefixEnd_338850 : Nat := 4983230072969 + 3 ^ 40 * 338850 * 2
def baseEnd_338850 : Nat := 115995279850736321011109

theorem tailTrace_338850 : CollatzResearch.WordTrace tailWord_338850 prefixEnd_338850 115995279850736321011109 := by
  unfold tailWord_338850
  simp only [CollatzResearch.WordTrace]
  refine ⟨3089718705602948954441501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8239249881607863878510669 3089718705602948954441501)
  ·
    refine ⟨1158644514601105857915563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3089718705602948954441501 1158644514601105857915563)
    ·
      refine ⟨1737966771901658786873345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1158644514601105857915563 1737966771901658786873345)
      ·
        refine ⟨1303475078926244090155009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1737966771901658786873345 1303475078926244090155009)
        ·
          refine ⟨977606309194683067616257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1303475078926244090155009 977606309194683067616257)
          ·
            refine ⟨733204731896012300712193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977606309194683067616257 733204731896012300712193)
            ·
              refine ⟨549903548922009225534145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733204731896012300712193 549903548922009225534145)
              ·
                refine ⟨412427661691506919150609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549903548922009225534145 412427661691506919150609)
                ·
                  refine ⟨309320746268630189362957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412427661691506919150609 309320746268630189362957)
                  ·
                    refine ⟨115995279850736321011109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309320746268630189362957 115995279850736321011109)
                    ·
                      rfl

theorem cell22_338850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_338850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338850 prefixEnd_338850 := by exact prefixLift 338850
  have htrace : WordTrace (prefixWord ++ tailWord_338850) baseStart_338850 baseEnd_338850 := by
    simpa [prefixWord, tailWord_338850, baseEnd_338850] using wordTrace_append hprefix tailTrace_338850
  have hstable : (prefixWord ++ tailWord_338850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338850).length < 2 ^ (prefixWord ++ tailWord_338850).sum := by decide
  have hdescent : baseEnd_338850 < baseStart_338850 := by decide
  rcases family_descends (prefixWord ++ tailWord_338850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338878 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_338878 : Nat := 118140960795 + 338878 * 2 ^ 59
def prefixEnd_338878 : Nat := 4983230072969 + 3 ^ 40 * 338878 * 2
def baseEnd_338878 : Nat := 116004864822953581311023

theorem tailTrace_338878 : CollatzResearch.WordTrace tailWord_338878 prefixEnd_338878 116004864822953581311023 := by
  unfold tailWord_338878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544987008288794574973161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8239930710873571066523525 1544987008288794574973161)
  ·
    refine ⟨1158740256216595931229871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1544987008288794574973161 1158740256216595931229871)
    ·
      refine ⟨1738110384324893896844807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1158740256216595931229871 1738110384324893896844807)
      ·
        refine ⟨2607165576487340845267211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738110384324893896844807 2607165576487340845267211)
        ·
          refine ⟨3910748364731011267900817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607165576487340845267211 3910748364731011267900817)
          ·
            refine ⟨2933061273548258450925613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3910748364731011267900817 2933061273548258450925613)
            ·
              refine ⟨1099897977580596919097105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2933061273548258450925613 1099897977580596919097105)
              ·
                refine ⟨824923483185447689322829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099897977580596919097105 824923483185447689322829)
                ·
                  refine ⟨309346306194542883496061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824923483185447689322829 309346306194542883496061)
                  ·
                    refine ⟨116004864822953581311023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309346306194542883496061 116004864822953581311023)
                    ·
                      rfl

theorem cell22_338878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_338878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338878 prefixEnd_338878 := by exact prefixLift 338878
  have htrace : WordTrace (prefixWord ++ tailWord_338878) baseStart_338878 baseEnd_338878 := by
    simpa [prefixWord, tailWord_338878, baseEnd_338878] using wordTrace_append hprefix tailTrace_338878
  have hstable : (prefixWord ++ tailWord_338878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338878).length < 2 ^ (prefixWord ++ tailWord_338878).sum := by decide
  have hdescent : baseEnd_338878 < baseStart_338878 := by decide
  rcases family_descends (prefixWord ++ tailWord_338878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338886 : List Nat := [6, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_338886 : Nat := 118140960795 + 338886 * 2 ^ 59
def prefixEnd_338886 : Nat := 4983230072969 + 3 ^ 40 * 338886 * 2
def baseEnd_338886 : Nat := 38669201128814742370333

theorem tailTrace_338886 : CollatzResearch.WordTrace tailWord_338886 prefixEnd_338886 38669201128814742370333 := by
  unfold tailWord_338886
  simp only [CollatzResearch.WordTrace]
  refine ⟨386255870321292936439891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8240125233520915977384341 386255870321292936439891)
  ·
    refine ⟨579383805481939404659837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 386255870321292936439891 579383805481939404659837)
    ·
      refine ⟨217268927055727276747439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 579383805481939404659837 217268927055727276747439)
      ·
        refine ⟨325903390583590915121159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217268927055727276747439 325903390583590915121159)
        ·
          refine ⟨488855085875386372681739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325903390583590915121159 488855085875386372681739)
          ·
            refine ⟨733282628813079559022609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488855085875386372681739 733282628813079559022609)
            ·
              refine ⟨549961971609809669266957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733282628813079559022609 549961971609809669266957)
              ·
                refine ⟨206235739353678625975109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 549961971609809669266957 206235739353678625975109)
                ·
                  refine ⟨38669201128814742370333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 206235739353678625975109 38669201128814742370333)
                  ·
                    rfl

theorem cell22_338886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_338886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338886 prefixEnd_338886 := by exact prefixLift 338886
  have htrace : WordTrace (prefixWord ++ tailWord_338886) baseStart_338886 baseEnd_338886 := by
    simpa [prefixWord, tailWord_338886, baseEnd_338886] using wordTrace_append hprefix tailTrace_338886
  have hstable : (prefixWord ++ tailWord_338886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338886).length < 2 ^ (prefixWord ++ tailWord_338886).sum := by decide
  have hdescent : baseEnd_338886 < baseStart_338886 := by decide
  rcases family_descends (prefixWord ++ tailWord_338886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338889 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 6, 5]
def baseStart_338889 : Nat := 118140960795 + 338889 * 2 ^ 59
def prefixEnd_338889 : Nat := 4983230072969 + 3 ^ 40 * 338889 * 2
def baseEnd_338889 : Nat := 116008630347753219285989

theorem tailTrace_338889 : CollatzResearch.WordTrace tailWord_338889 prefixEnd_338889 116008630347753219285989 := by
  unfold tailWord_338889
  simp only [CollatzResearch.WordTrace]
  refine ⟨12360297269270505478435721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8240198179513670318957147 12360297269270505478435721)
  ·
    refine ⟨9270222951952879108826791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12360297269270505478435721 9270222951952879108826791)
    ·
      refine ⟨13905334427929318663240187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9270222951952879108826791 13905334427929318663240187)
      ·
        refine ⟨20858001641893977994860281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13905334427929318663240187 20858001641893977994860281)
        ·
          refine ⟨15643501231420483496145211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20858001641893977994860281 15643501231420483496145211)
          ·
            refine ⟨23465251847130725244217817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15643501231420483496145211 23465251847130725244217817)
            ·
              refine ⟨17598938885348043933163363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23465251847130725244217817 17598938885348043933163363)
              ·
                refine ⟨26398408328022065899745045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17598938885348043933163363 26398408328022065899745045)
                ·
                  refine ⟨1237425390376034339050549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26398408328022065899745045 1237425390376034339050549)
                  ·
                    refine ⟨116008630347753219285989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1237425390376034339050549 116008630347753219285989)
                    ·
                      rfl

theorem cell22_338889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_338889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338889 prefixEnd_338889 := by exact prefixLift 338889
  have htrace : WordTrace (prefixWord ++ tailWord_338889) baseStart_338889 baseEnd_338889 := by
    simpa [prefixWord, tailWord_338889, baseEnd_338889] using wordTrace_append hprefix tailTrace_338889
  have hstable : (prefixWord ++ tailWord_338889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338889).length < 2 ^ (prefixWord ++ tailWord_338889).sum := by decide
  have hdescent : baseEnd_338889 < baseStart_338889 := by decide
  rcases family_descends (prefixWord ++ tailWord_338889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338895 : List Nat := [1, 1, 2, 1, 1, 7, 2, 3, 1, 3]
def baseStart_338895 : Nat := 118140960795 + 338895 * 2 ^ 59
def prefixEnd_338895 : Nat := 4983230072969 + 3 ^ 40 * 338895 * 2
def baseEnd_338895 : Nat := 116010684270371203635971

theorem tailTrace_338895 : CollatzResearch.WordTrace tailWord_338895 prefixEnd_338895 116010684270371203635971 := by
  unfold tailWord_338895
  simp only [CollatzResearch.WordTrace]
  refine ⟨12360516107248768503154139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8240344071499179002102759 12360516107248768503154139)
  ·
    refine ⟨18540774160873152754731209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12360516107248768503154139 18540774160873152754731209)
    ·
      refine ⟨13905580620654864566048407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18540774160873152754731209 13905580620654864566048407)
      ·
        refine ⟨20858370930982296849072611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13905580620654864566048407 20858370930982296849072611)
        ·
          refine ⟨31287556396473445273608917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20858370930982296849072611 31287556396473445273608917)
          ·
            refine ⟨733302103042346373600209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 31287556396473445273608917 733302103042346373600209)
            ·
              refine ⟨549976577281759780200157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733302103042346373600209 549976577281759780200157)
              ·
                refine ⟨206241216480659917575059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 549976577281759780200157 206241216480659917575059)
                ·
                  refine ⟨309361824720989876362589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206241216480659917575059 309361824720989876362589)
                  ·
                    refine ⟨116010684270371203635971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309361824720989876362589 116010684270371203635971)
                    ·
                      rfl

theorem cell22_338895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 1, 3].length) (baseStart_338895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338895 prefixEnd_338895 := by exact prefixLift 338895
  have htrace : WordTrace (prefixWord ++ tailWord_338895) baseStart_338895 baseEnd_338895 := by
    simpa [prefixWord, tailWord_338895, baseEnd_338895] using wordTrace_append hprefix tailTrace_338895
  have hstable : (prefixWord ++ tailWord_338895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338895).length < 2 ^ (prefixWord ++ tailWord_338895).sum := by decide
  have hdescent : baseEnd_338895 < baseStart_338895 := by decide
  rcases family_descends (prefixWord ++ tailWord_338895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338906 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_338906 : Nat := 118140960795 + 338906 * 2 ^ 59
def prefixEnd_338906 : Nat := 4983230072969 + 3 ^ 40 * 338906 * 2
def baseEnd_338906 : Nat := 116014449795170841610937

theorem tailTrace_338906 : CollatzResearch.WordTrace tailWord_338906 prefixEnd_338906 116014449795170841610937 := by
  unfold tailWord_338906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3090229327552229345451143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8240611540139278254536381 3090229327552229345451143)
  ·
    refine ⟨4635343991328344018176715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3090229327552229345451143 4635343991328344018176715)
    ·
      refine ⟨6953015986992516027265073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4635343991328344018176715 6953015986992516027265073)
      ·
        refine ⟨5214761990244387020448805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6953015986992516027265073 5214761990244387020448805)
        ·
          refine ⟨977767873170822566334151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5214761990244387020448805 977767873170822566334151)
          ·
            refine ⟨1466651809756233849501227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977767873170822566334151 1466651809756233849501227)
            ·
              refine ⟨2199977714634350774251841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466651809756233849501227 2199977714634350774251841)
              ·
                refine ⟨1649983285975763080688881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2199977714634350774251841 1649983285975763080688881)
                ·
                  refine ⟨1237487464481822310516661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1649983285975763080688881 1237487464481822310516661)
                  ·
                    refine ⟨116014449795170841610937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1237487464481822310516661 116014449795170841610937)
                    ·
                      rfl

theorem cell22_338906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_338906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338906 prefixEnd_338906 := by exact prefixLift 338906
  have htrace : WordTrace (prefixWord ++ tailWord_338906) baseStart_338906 baseEnd_338906 := by
    simpa [prefixWord, tailWord_338906, baseEnd_338906] using wordTrace_append hprefix tailTrace_338906
  have hstable : (prefixWord ++ tailWord_338906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338906).length < 2 ^ (prefixWord ++ tailWord_338906).sum := by decide
  have hdescent : baseEnd_338906 < baseStart_338906 := by decide
  rcases family_descends (prefixWord ++ tailWord_338906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338946 : List Nat := [3, 4, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_338946 : Nat := 118140960795 + 338946 * 2 ^ 59
def prefixEnd_338946 : Nat := 4983230072969 + 3 ^ 40 * 338946 * 2
def baseEnd_338946 : Nat := 116028142612624070610815

theorem tailTrace_338946 : CollatzResearch.WordTrace tailWord_338946 prefixEnd_338946 116028142612624070610815 := by
  unfold tailWord_338946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3090594057516001053315173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8241584153376002808840461 3090594057516001053315173)
  ·
    refine ⟨579486385784250197496595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3090594057516001053315173 579486385784250197496595)
    ·
      refine ⟨869229578676375296244893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 579486385784250197496595 869229578676375296244893)
      ·
        refine ⟨325961092003640736091835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 869229578676375296244893 325961092003640736091835)
        ·
          refine ⟨488941638005461104137753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325961092003640736091835 488941638005461104137753)
          ·
            refine ⟨366706228504095828103315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488941638005461104137753 366706228504095828103315)
            ·
              refine ⟨550059342756143742154973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366706228504095828103315 550059342756143742154973)
              ·
                refine ⟨206272253533553903308115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 550059342756143742154973 206272253533553903308115)
                ·
                  refine ⟨309408380300330854962173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206272253533553903308115 309408380300330854962173)
                  ·
                    refine ⟨116028142612624070610815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309408380300330854962173 116028142612624070610815)
                    ·
                      rfl

theorem cell22_338946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_338946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338946 prefixEnd_338946 := by exact prefixLift 338946
  have htrace : WordTrace (prefixWord ++ tailWord_338946) baseStart_338946 baseEnd_338946 := by
    simpa [prefixWord, tailWord_338946, baseEnd_338946] using wordTrace_append hprefix tailTrace_338946
  have hstable : (prefixWord ++ tailWord_338946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338946).length < 2 ^ (prefixWord ++ tailWord_338946).sum := by decide
  have hdescent : baseEnd_338946 < baseStart_338946 := by decide
  rcases family_descends (prefixWord ++ tailWord_338946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338951 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 3, 5]
def baseStart_338951 : Nat := 118140960795 + 338951 * 2 ^ 59
def prefixEnd_338951 : Nat := 4983230072969 + 3 ^ 40 * 338951 * 2
def baseEnd_338951 : Nat := 116029854214805724235799

theorem tailTrace_338951 : CollatzResearch.WordTrace tailWord_338951 prefixEnd_338951 116029854214805724235799 := by
  unfold tailWord_338951
  simp only [CollatzResearch.WordTrace]
  refine ⟨12362558595045890067192707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8241705730030593378128471 12362558595045890067192707)
  ·
    refine ⟨18543837892568835100789061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12362558595045890067192707 18543837892568835100789061)
    ·
      refine ⟨3476969604856656581397949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18543837892568835100789061 3476969604856656581397949)
      ·
        refine ⟨1303863601821246218024231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3476969604856656581397949 1303863601821246218024231)
        ·
          refine ⟨1955795402731869327036347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1303863601821246218024231 1955795402731869327036347)
          ·
            refine ⟨2933693104097803990554521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955795402731869327036347 2933693104097803990554521)
            ·
              refine ⟨2200269828073352992915891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2933693104097803990554521 2200269828073352992915891)
              ·
                refine ⟨3300404742110029489373837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2200269828073352992915891 3300404742110029489373837)
                ·
                  refine ⟨1237651778291261058515189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3300404742110029489373837 1237651778291261058515189)
                  ·
                    refine ⟨116029854214805724235799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1237651778291261058515189 116029854214805724235799)
                    ·
                      rfl

theorem cell22_338951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_338951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338951 prefixEnd_338951 := by exact prefixLift 338951
  have htrace : WordTrace (prefixWord ++ tailWord_338951) baseStart_338951 baseEnd_338951 := by
    simpa [prefixWord, tailWord_338951, baseEnd_338951] using wordTrace_append hprefix tailTrace_338951
  have hstable : (prefixWord ++ tailWord_338951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338951).length < 2 ^ (prefixWord ++ tailWord_338951).sum := by decide
  have hdescent : baseEnd_338951 < baseStart_338951 := by decide
  rcases family_descends (prefixWord ++ tailWord_338951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338968 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 4, 3]
def baseStart_338968 : Nat := 118140960795 + 338968 * 2 ^ 59
def prefixEnd_338968 : Nat := 4983230072969 + 3 ^ 40 * 338968 * 2
def baseEnd_338968 : Nat := 116035673662223346560747

theorem tailTrace_338968 : CollatzResearch.WordTrace tailWord_338968 prefixEnd_338968 116035673662223346560747 := by
  unfold tailWord_338968
  simp only [CollatzResearch.WordTrace]
  refine ⟨6181589317992150985280779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8242119090656201313707705 6181589317992150985280779)
  ·
    refine ⟨9272383976988226477921169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6181589317992150985280779 9272383976988226477921169)
    ·
      refine ⟨6954287982741169858440877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9272383976988226477921169 6954287982741169858440877)
      ·
        refine ⟨2607857993527938696915329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6954287982741169858440877 2607857993527938696915329)
        ·
          refine ⟨1955893495145954022686497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2607857993527938696915329 1955893495145954022686497)
          ·
            refine ⟨1466920121359465517014873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1955893495145954022686497 1466920121359465517014873)
            ·
              refine ⟨1100190091019599137761155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466920121359465517014873 1100190091019599137761155)
              ·
                refine ⟨1650285136529398706641733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100190091019599137761155 1650285136529398706641733)
                ·
                  refine ⟨309428463099262257495325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1650285136529398706641733 309428463099262257495325)
                  ·
                    refine ⟨116035673662223346560747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309428463099262257495325 116035673662223346560747)
                    ·
                      rfl

theorem cell22_338968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_338968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338968 prefixEnd_338968 := by exact prefixLift 338968
  have htrace : WordTrace (prefixWord ++ tailWord_338968) baseStart_338968 baseEnd_338968 := by
    simpa [prefixWord, tailWord_338968, baseEnd_338968] using wordTrace_append hprefix tailTrace_338968
  have hstable : (prefixWord ++ tailWord_338968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338968).length < 2 ^ (prefixWord ++ tailWord_338968).sum := by decide
  have hdescent : baseEnd_338968 < baseStart_338968 := by decide
  rcases family_descends (prefixWord ++ tailWord_338968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338970 : List Nat := [3, 1, 1, 3, 1, 2, 5, 2, 4]
def baseStart_338970 : Nat := 118140960795 + 338970 * 2 ^ 59
def prefixEnd_338970 : Nat := 4983230072969 + 3 ^ 40 * 338970 * 2
def baseEnd_338970 : Nat := 38678786101032002670247

theorem tailTrace_338970 : CollatzResearch.WordTrace tailWord_338970 prefixEnd_338970 38678786101032002670247 := by
  unfold tailWord_338970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3090812895494264078033591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8242167721318037541422909 3090812895494264078033591)
  ·
    refine ⟨4636219343241396117050387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3090812895494264078033591 4636219343241396117050387)
    ·
      refine ⟨6954329014862094175575581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4636219343241396117050387 6954329014862094175575581)
      ·
        refine ⟨2607873380573285315840843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6954329014862094175575581 2607873380573285315840843)
        ·
          refine ⟨3911810070859927973761265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607873380573285315840843 3911810070859927973761265)
          ·
            refine ⟨2933857553144945980320949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3911810070859927973761265 2933857553144945980320949)
            ·
              refine ⟨275049145607338685655089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2933857553144945980320949 275049145607338685655089)
              ·
                refine ⟨206286859205504014241317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275049145607338685655089 206286859205504014241317)
                ·
                  refine ⟨38678786101032002670247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 206286859205504014241317 38678786101032002670247)
                  ·
                    rfl

theorem cell22_338970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_338970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338970 prefixEnd_338970 := by exact prefixLift 338970
  have htrace : WordTrace (prefixWord ++ tailWord_338970) baseStart_338970 baseEnd_338970 := by
    simpa [prefixWord, tailWord_338970, baseEnd_338970] using wordTrace_append hprefix tailTrace_338970
  have hstable : (prefixWord ++ tailWord_338970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338970).length < 2 ^ (prefixWord ++ tailWord_338970).sum := by decide
  have hdescent : baseEnd_338970 < baseStart_338970 := by decide
  rcases family_descends (prefixWord ++ tailWord_338970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338981 : List Nat := [1, 3, 1, 2, 2, 2, 4, 7]
def baseStart_338981 : Nat := 118140960795 + 338981 * 2 ^ 59
def prefixEnd_338981 : Nat := 4983230072969 + 3 ^ 40 * 338981 * 2
def baseEnd_338981 : Nat := 12893347091988405109523

theorem tailTrace_338981 : CollatzResearch.WordTrace tailWord_338981 prefixEnd_338981 12893347091988405109523 := by
  unfold tailWord_338981
  simp only [CollatzResearch.WordTrace]
  refine ⟨12363652784937205190784797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8242435189958136793856531 12363652784937205190784797)
  ·
    refine ⟨4636369794351451946544299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12363652784937205190784797 4636369794351451946544299)
    ·
      refine ⟨6954554691527177919816449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4636369794351451946544299 6954554691527177919816449)
      ·
        refine ⟨5215916018645383439862337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6954554691527177919816449 5215916018645383439862337)
        ·
          refine ⟨3911937013984037579896753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5215916018645383439862337 3911937013984037579896753)
          ·
            refine ⟨2933952760488028184922565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3911937013984037579896753 2933952760488028184922565)
            ·
              refine ⟨550116142591505284672981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2933952760488028184922565 550116142591505284672981)
              ·
                refine ⟨12893347091988405109523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 550116142591505284672981 12893347091988405109523)
                ·
                  rfl

theorem cell22_338981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 7].length) (baseStart_338981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338981 prefixEnd_338981 := by exact prefixLift 338981
  have htrace : WordTrace (prefixWord ++ tailWord_338981) baseStart_338981 baseEnd_338981 := by
    simpa [prefixWord, tailWord_338981, baseEnd_338981] using wordTrace_append hprefix tailTrace_338981
  have hstable : (prefixWord ++ tailWord_338981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338981).length < 2 ^ (prefixWord ++ tailWord_338981).sum := by decide
  have hdescent : baseEnd_338981 < baseStart_338981 := by decide
  rcases family_descends (prefixWord ++ tailWord_338981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338998 : List Nat := [5, 1, 2, 1, 1, 2, 2, 8]
def baseStart_338998 : Nat := 118140960795 + 338998 * 2 ^ 59
def prefixEnd_338998 : Nat := 4983230072969 + 3 ^ 40 * 338998 * 2
def baseEnd_338998 : Nat := 12893993697257029812295

theorem tailTrace_338998 : CollatzResearch.WordTrace tailWord_338998 prefixEnd_338998 12893993697257029812295 := by
  unfold tailWord_338998
  simp only [CollatzResearch.WordTrace]
  refine ⟨772767051617226068384603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8242848550583744729435765 772767051617226068384603)
  ·
    refine ⟨1159150577425839102576905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 772767051617226068384603 1159150577425839102576905)
    ·
      refine ⟨869362933069379326932679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1159150577425839102576905 869362933069379326932679)
      ·
        refine ⟨1304044399604068990399019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869362933069379326932679 1304044399604068990399019)
        ·
          refine ⟨1956066599406103485598529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304044399604068990399019 1956066599406103485598529)
          ·
            refine ⟨1467049949554577614198897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1956066599406103485598529 1467049949554577614198897)
            ·
              refine ⟨1100287462165933210649173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1467049949554577614198897 1100287462165933210649173)
              ·
                refine ⟨12893993697257029812295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1100287462165933210649173 12893993697257029812295)
                ·
                  rfl

theorem cell22_338998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_338998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_338998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_338998 prefixEnd_338998 := by exact prefixLift 338998
  have htrace : WordTrace (prefixWord ++ tailWord_338998) baseStart_338998 baseEnd_338998 := by
    simpa [prefixWord, tailWord_338998, baseEnd_338998] using wordTrace_append hprefix tailTrace_338998
  have hstable : (prefixWord ++ tailWord_338998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338998).length < 2 ^ (prefixWord ++ tailWord_338998).sum := by decide
  have hdescent : baseEnd_338998 < baseStart_338998 := by decide
  rcases family_descends (prefixWord ++ tailWord_338998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339041 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 1, 7]
def baseStart_339041 : Nat := 118140960795 + 339041 * 2 ^ 59
def prefixEnd_339041 : Nat := 4983230072969 + 3 ^ 40 * 339041 * 2
def baseEnd_339041 : Nat := 116060663054075489485523

theorem tailTrace_339041 : CollatzResearch.WordTrace tailWord_339041 prefixEnd_339041 116060663054075489485523 := by
  unfold tailWord_339041
  simp only [CollatzResearch.WordTrace]
  refine ⟨12365841164719835437968977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8243894109813223625312651 12365841164719835437968977)
  ·
    refine ⟨9274380873539876578476733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12365841164719835437968977 9274380873539876578476733)
    ·
      refine ⟨3477892827577453716928775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9274380873539876578476733 3477892827577453716928775)
      ·
        refine ⟨5216839241366180575393163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3477892827577453716928775 5216839241366180575393163)
        ·
          refine ⟨7825258862049270863089745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5216839241366180575393163 7825258862049270863089745)
          ·
            refine ⟨5868944146536953147317309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7825258862049270863089745 5868944146536953147317309)
            ·
              refine ⟨2200854054951357430243991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5868944146536953147317309 2200854054951357430243991)
              ·
                refine ⟨3301281082427036145365987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2200854054951357430243991 3301281082427036145365987)
                ·
                  refine ⟨4951921623640554218048981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301281082427036145365987 4951921623640554218048981)
                  ·
                    refine ⟨116060663054075489485523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4951921623640554218048981 116060663054075489485523)
                    ·
                      rfl

theorem cell22_339041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_339041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339041 prefixEnd_339041 := by exact prefixLift 339041
  have htrace : WordTrace (prefixWord ++ tailWord_339041) baseStart_339041 baseEnd_339041 := by
    simpa [prefixWord, tailWord_339041, baseEnd_339041] using wordTrace_append hprefix tailTrace_339041
  have hstable : (prefixWord ++ tailWord_339041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339041).length < 2 ^ (prefixWord ++ tailWord_339041).sum := by decide
  have hdescent : baseEnd_339041 < baseStart_339041 := by decide
  rcases family_descends (prefixWord ++ tailWord_339041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339077 : List Nat := [1, 3, 1, 1, 7, 1, 1, 2, 5]
def baseStart_339077 : Nat := 118140960795 + 339077 * 2 ^ 59
def prefixEnd_339077 : Nat := 4983230072969 + 3 ^ 40 * 339077 * 2
def baseEnd_339077 : Nat := 38690995529927798528471

theorem tailTrace_339077 : CollatzResearch.WordTrace tailWord_339077 prefixEnd_339077 38690995529927798528471 := by
  unfold tailWord_339077
  simp only [CollatzResearch.WordTrace]
  refine ⟨12367154192589413586279485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8244769461726275724186323 12367154192589413586279485)
  ·
    refine ⟨4637682822221030094854807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12367154192589413586279485 4637682822221030094854807)
    ·
      refine ⟨6956524233331545142282211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4637682822221030094854807 6956524233331545142282211)
      ·
        refine ⟨10434786349997317713423317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6956524233331545142282211 10434786349997317713423317)
        ·
          refine ⟨244565305078062133908359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10434786349997317713423317 244565305078062133908359)
          ·
            refine ⟨366847957617093200862539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244565305078062133908359 366847957617093200862539)
            ·
              refine ⟨550271936425639801293809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366847957617093200862539 550271936425639801293809)
              ·
                refine ⟨412703952319229850970357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550271936425639801293809 412703952319229850970357)
                ·
                  refine ⟨38690995529927798528471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 412703952319229850970357 38690995529927798528471)
                  ·
                    rfl

theorem cell22_339077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_339077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339077 prefixEnd_339077 := by exact prefixLift 339077
  have htrace : WordTrace (prefixWord ++ tailWord_339077) baseStart_339077 baseEnd_339077 := by
    simpa [prefixWord, tailWord_339077, baseEnd_339077] using wordTrace_append hprefix tailTrace_339077
  have hstable : (prefixWord ++ tailWord_339077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339077).length < 2 ^ (prefixWord ++ tailWord_339077).sum := by decide
  have hdescent : baseEnd_339077 < baseStart_339077 := by decide
  rcases family_descends (prefixWord ++ tailWord_339077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339122 : List Nat := [3, 2, 1, 1, 1, 6, 1, 3, 4]
def baseStart_339122 : Nat := 118140960795 + 339122 * 2 ^ 59
def prefixEnd_339122 : Nat := 4983230072969 + 3 ^ 40 * 339122 * 2
def baseEnd_339122 : Nat := 38696130336472759403425

theorem tailTrace_339122 : CollatzResearch.WordTrace tailWord_339122 prefixEnd_339122 38696130336472759403425 := by
  unfold tailWord_339122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3092198869356596567916905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8245863651617590847778413 3092198869356596567916905)
  ·
    refine ⟨2319149152017447425937679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3092198869356596567916905 2319149152017447425937679)
    ·
      refine ⟨3478723728026171138906519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2319149152017447425937679 3478723728026171138906519)
      ·
        refine ⟨5218085592039256708359779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3478723728026171138906519 5218085592039256708359779)
        ·
          refine ⟨7827128388058885062539669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5218085592039256708359779 7827128388058885062539669)
          ·
            refine ⟨366896643190260237306547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7827128388058885062539669 366896643190260237306547)
            ·
              refine ⟨550344964785390355959821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366896643190260237306547 550344964785390355959821)
              ·
                refine ⟨206379361794521383484933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 550344964785390355959821 206379361794521383484933)
                ·
                  refine ⟨38696130336472759403425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 206379361794521383484933 38696130336472759403425)
                  ·
                    rfl

theorem cell22_339122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_339122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339122 prefixEnd_339122 := by exact prefixLift 339122
  have htrace : WordTrace (prefixWord ++ tailWord_339122) baseStart_339122 baseEnd_339122 := by
    simpa [prefixWord, tailWord_339122, baseEnd_339122] using wordTrace_append hprefix tailTrace_339122
  have hstable : (prefixWord ++ tailWord_339122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339122).length < 2 ^ (prefixWord ++ tailWord_339122).sum := by decide
  have hdescent : baseEnd_339122 < baseStart_339122 := by decide
  rcases family_descends (prefixWord ++ tailWord_339122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339137 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 4, 3]
def baseStart_339137 : Nat := 118140960795 + 339137 * 2 ^ 59
def prefixEnd_339137 : Nat := 4983230072969 + 3 ^ 40 * 339137 * 2
def baseEnd_339137 : Nat := 116093525815963239085229

theorem tailTrace_339137 : CollatzResearch.WordTrace tailWord_339137 prefixEnd_339137 116093525815963239085229 := by
  unfold tailWord_339137
  simp only [CollatzResearch.WordTrace]
  refine ⟨12369342572372043833463665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8246228381581362555642443 12369342572372043833463665)
  ·
    refine ⟨9277006929279032875097749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12369342572372043833463665 9277006929279032875097749)
    ·
      refine ⟨434859699809954666020207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9277006929279032875097749 434859699809954666020207)
      ·
        refine ⟨652289549714931999030311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434859699809954666020207 652289549714931999030311)
        ·
          refine ⟨978434324572397998545467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652289549714931999030311 978434324572397998545467)
          ·
            refine ⟨1467651486858596997818201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978434324572397998545467 1467651486858596997818201)
            ·
              refine ⟨1100738615143947748363651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1467651486858596997818201 1100738615143947748363651)
              ·
                refine ⟨1651107922715921622545477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100738615143947748363651 1651107922715921622545477)
                ·
                  refine ⟨309582735509235304227277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651107922715921622545477 309582735509235304227277)
                  ·
                    refine ⟨116093525815963239085229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309582735509235304227277 116093525815963239085229)
                    ·
                      rfl

theorem cell22_339137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_339137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339137 prefixEnd_339137 := by exact prefixLift 339137
  have htrace : WordTrace (prefixWord ++ tailWord_339137) baseStart_339137 baseEnd_339137 := by
    simpa [prefixWord, tailWord_339137, baseEnd_339137] using wordTrace_append hprefix tailTrace_339137
  have hstable : (prefixWord ++ tailWord_339137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339137).length < 2 ^ (prefixWord ++ tailWord_339137).sum := by decide
  have hdescent : baseEnd_339137 < baseStart_339137 := by decide
  rcases family_descends (prefixWord ++ tailWord_339137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339150 : List Nat := [4, 1, 1, 1, 5, 1, 2, 7]
def baseStart_339150 : Nat := 118140960795 + 339150 * 2 ^ 59
def prefixEnd_339150 : Nat := 4983230072969 + 3 ^ 40 * 339150 * 2
def baseEnd_339150 : Nat := 12899775109070615390021

theorem tailTrace_339150 : CollatzResearch.WordTrace tailWord_339150 prefixEnd_339150 12899775109070615390021 := by
  unfold tailWord_339150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1546227090165618381710863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8246544480883298035791269 1546227090165618381710863)
  ·
    refine ⟨2319340635248427572566295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1546227090165618381710863 2319340635248427572566295)
    ·
      refine ⟨3479010952872641358849443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2319340635248427572566295 3479010952872641358849443)
      ·
        refine ⟨5218516429308962038274165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479010952872641358849443 5218516429308962038274165)
        ·
          refine ⟨489235915247715191088203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5218516429308962038274165 489235915247715191088203)
          ·
            refine ⟨733853872871572786632305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489235915247715191088203 733853872871572786632305)
            ·
              refine ⟨550390404653679589974229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733853872871572786632305 550390404653679589974229)
              ·
                refine ⟨12899775109070615390021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 550390404653679589974229 12899775109070615390021)
                ·
                  rfl

theorem cell22_339150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_339150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339150 prefixEnd_339150 := by exact prefixLift 339150
  have htrace : WordTrace (prefixWord ++ tailWord_339150) baseStart_339150 baseEnd_339150 := by
    simpa [prefixWord, tailWord_339150, baseEnd_339150] using wordTrace_append hprefix tailTrace_339150
  have hstable : (prefixWord ++ tailWord_339150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339150).length < 2 ^ (prefixWord ++ tailWord_339150).sum := by decide
  have hdescent : baseEnd_339150 < baseStart_339150 := by decide
  rcases family_descends (prefixWord ++ tailWord_339150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339188 : List Nat := [2, 6, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_339188 : Nat := 118140960795 + 339188 * 2 ^ 59
def prefixEnd_339188 : Nat := 4983230072969 + 3 ^ 40 * 339188 * 2
def baseEnd_339188 : Nat := 116110984158216106060073

theorem tailTrace_339188 : CollatzResearch.WordTrace tailWord_339188 prefixEnd_339188 116110984158216106060073 := by
  unfold tailWord_339188
  simp only [CollatzResearch.WordTrace]
  refine ⟨6185601347593639771785109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8247468463458186362380145 6185601347593639771785109)
  ·
    refine ⟨289950063168451864302427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6185601347593639771785109 289950063168451864302427)
    ·
      refine ⟨434925094752677796453641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289950063168451864302427 434925094752677796453641)
      ·
        refine ⟨326193821064508347340231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434925094752677796453641 326193821064508347340231)
        ·
          refine ⟨489290731596762521010347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326193821064508347340231 489290731596762521010347)
          ·
            refine ⟨733936097395143781515521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489290731596762521010347 733936097395143781515521)
            ·
              refine ⟨550452073046357836136641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733936097395143781515521 550452073046357836136641)
              ·
                refine ⟨412839054784768377102481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550452073046357836136641 412839054784768377102481)
                ·
                  refine ⟨309629291088576282826861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412839054784768377102481 309629291088576282826861)
                  ·
                    refine ⟨116110984158216106060073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309629291088576282826861 116110984158216106060073)
                    ·
                      rfl

theorem cell22_339188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_339188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339188 prefixEnd_339188 := by exact prefixLift 339188
  have htrace : WordTrace (prefixWord ++ tailWord_339188) baseStart_339188 baseEnd_339188 := by
    simpa [prefixWord, tailWord_339188, baseEnd_339188] using wordTrace_append hprefix tailTrace_339188
  have hstable : (prefixWord ++ tailWord_339188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339188).length < 2 ^ (prefixWord ++ tailWord_339188).sum := by decide
  have hdescent : baseEnd_339188 < baseStart_339188 := by decide
  rcases family_descends (prefixWord ++ tailWord_339188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339193 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 2, 5]
def baseStart_339193 : Nat := 118140960795 + 339193 * 2 ^ 59
def prefixEnd_339193 : Nat := 4983230072969 + 3 ^ 40 * 339193 * 2
def baseEnd_339193 : Nat := 116112695760397759685057

theorem tailTrace_339193 : CollatzResearch.WordTrace tailWord_339193 prefixEnd_339193 116112695760397759685057 := by
  unfold tailWord_339193
  simp only [CollatzResearch.WordTrace]
  refine ⟨12371385060169165397502233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8247590040112776931668155 12371385060169165397502233)
  ·
    refine ⟨9278538795126874048126675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12371385060169165397502233 9278538795126874048126675)
    ·
      refine ⟨13917808192690311072190013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9278538795126874048126675 13917808192690311072190013)
      ·
        refine ⟨5219178072258866652071255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13917808192690311072190013 5219178072258866652071255)
        ·
          refine ⟨7828767108388299978106883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5219178072258866652071255 7828767108388299978106883)
          ·
            refine ⟨11743150662582449967160325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7828767108388299978106883 11743150662582449967160325)
            ·
              refine ⟨2201840749234209368842561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11743150662582449967160325 2201840749234209368842561)
              ·
                refine ⟨1651380561925657026631921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2201840749234209368842561 1651380561925657026631921)
                ·
                  refine ⟨1238535421444242769973941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1651380561925657026631921 1238535421444242769973941)
                  ·
                    refine ⟨116112695760397759685057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1238535421444242769973941 116112695760397759685057)
                    ·
                      rfl

theorem cell22_339193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_339193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339193 prefixEnd_339193 := by exact prefixLift 339193
  have htrace : WordTrace (prefixWord ++ tailWord_339193) baseStart_339193 baseEnd_339193 := by
    simpa [prefixWord, tailWord_339193, baseEnd_339193] using wordTrace_append hprefix tailTrace_339193
  have hstable : (prefixWord ++ tailWord_339193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339193).length < 2 ^ (prefixWord ++ tailWord_339193).sum := by decide
  have hdescent : baseEnd_339193 < baseStart_339193 := by decide
  rcases family_descends (prefixWord ++ tailWord_339193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339199 : List Nat := [1, 1, 2, 2, 1, 5, 4, 2, 1, 3]
def baseStart_339199 : Nat := 118140960795 + 339199 * 2 ^ 59
def prefixEnd_339199 : Nat := 4983230072969 + 3 ^ 40 * 339199 * 2
def baseEnd_339199 : Nat := 116114749683015744035039

theorem tailTrace_339199 : CollatzResearch.WordTrace tailWord_339199 prefixEnd_339199 116114749683015744035039 := by
  unfold tailWord_339199
  simp only [CollatzResearch.WordTrace]
  refine ⟨12371603898147428422220651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8247735932098285614813767 12371603898147428422220651)
  ·
    refine ⟨18557405847221142633330977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12371603898147428422220651 18557405847221142633330977)
    ·
      refine ⟨13918054385415856974998233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18557405847221142633330977 13918054385415856974998233)
      ·
        refine ⟨10438540789061892731248675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13918054385415856974998233 10438540789061892731248675)
        ·
          refine ⟨15657811183592839096873013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10438540789061892731248675 15657811183592839096873013)
          ·
            refine ⟨1467919798461828665331845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15657811183592839096873013 1467919798461828665331845)
            ·
              refine ⟨275234962211592874749721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1467919798461828665331845 275234962211592874749721)
              ·
                refine ⟨206426221658694656062291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275234962211592874749721 206426221658694656062291)
                ·
                  refine ⟨309639332488041984093437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206426221658694656062291 309639332488041984093437)
                  ·
                    refine ⟨116114749683015744035039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309639332488041984093437 116114749683015744035039)
                    ·
                      rfl

theorem cell22_339199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 1, 3].length) (baseStart_339199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339199 prefixEnd_339199 := by exact prefixLift 339199
  have htrace : WordTrace (prefixWord ++ tailWord_339199) baseStart_339199 baseEnd_339199 := by
    simpa [prefixWord, tailWord_339199, baseEnd_339199] using wordTrace_append hprefix tailTrace_339199
  have hstable : (prefixWord ++ tailWord_339199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339199).length < 2 ^ (prefixWord ++ tailWord_339199).sum := by decide
  have hdescent : baseEnd_339199 < baseStart_339199 := by decide
  rcases family_descends (prefixWord ++ tailWord_339199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339257 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 6]
def baseStart_339257 : Nat := 118140960795 + 339257 * 2 ^ 59
def prefixEnd_339257 : Nat := 4983230072969 + 3 ^ 40 * 339257 * 2
def baseEnd_339257 : Nat := 38711534756107642028287

theorem tailTrace_339257 : CollatzResearch.WordTrace tailWord_339257 prefixEnd_339257 38711534756107642028287 := by
  unfold tailWord_339257
  simp only [CollatzResearch.WordTrace]
  refine ⟨12373719331937304327832025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8249146221291536218554683 12373719331937304327832025)
  ·
    refine ⟨9280289498952978245874019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12373719331937304327832025 9280289498952978245874019)
    ·
      refine ⟨13920434248429467368811029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9280289498952978245874019 13920434248429467368811029)
      ·
        refine ⟨652520355395131282913017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13920434248429467368811029 652520355395131282913017)
        ·
          refine ⟨489390266546348462184763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652520355395131282913017 489390266546348462184763)
          ·
            refine ⟨734085399819522693277145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489390266546348462184763 734085399819522693277145)
            ·
              refine ⟨550564049864642019957859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734085399819522693277145 550564049864642019957859)
              ·
                refine ⟨825846074796963029936789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550564049864642019957859 825846074796963029936789)
                ·
                  refine ⟨38711534756107642028287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 825846074796963029936789 38711534756107642028287)
                  ·
                    rfl

theorem cell22_339257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 6].length) (baseStart_339257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339257 prefixEnd_339257 := by exact prefixLift 339257
  have htrace : WordTrace (prefixWord ++ tailWord_339257) baseStart_339257 baseEnd_339257 := by
    simpa [prefixWord, tailWord_339257, baseEnd_339257] using wordTrace_append hprefix tailTrace_339257
  have hstable : (prefixWord ++ tailWord_339257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339257).length < 2 ^ (prefixWord ++ tailWord_339257).sum := by decide
  have hdescent : baseEnd_339257 < baseStart_339257 := by decide
  rcases family_descends (prefixWord ++ tailWord_339257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339283 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 2, 7]
def baseStart_339283 : Nat := 118140960795 + 339283 * 2 ^ 59
def prefixEnd_339283 : Nat := 4983230072969 + 3 ^ 40 * 339283 * 2
def baseEnd_339283 : Nat := 116143504599667524934781

theorem tailTrace_339283 : CollatzResearch.WordTrace tailWord_339283 prefixEnd_339283 116143504599667524934781 := by
  unfold tailWord_339283
  simp only [CollatzResearch.WordTrace]
  refine ⟨12374667629843110768278503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8249778419895407178852335 12374667629843110768278503)
  ·
    refine ⟨18562001444764666152417755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12374667629843110768278503 18562001444764666152417755)
    ·
      refine ⟨27843002167146999228626633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18562001444764666152417755 27843002167146999228626633)
      ·
        refine ⟨20882251625360249421469975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27843002167146999228626633 20882251625360249421469975)
        ·
          refine ⟨31323377438040374132204963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20882251625360249421469975 31323377438040374132204963)
          ·
            refine ⟨46985066157060561198307445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31323377438040374132204963 46985066157060561198307445)
            ·
              refine ⟨4404849952224427612341323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46985066157060561198307445 4404849952224427612341323)
              ·
                refine ⟨6607274928336641418511985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404849952224427612341323 6607274928336641418511985)
                ·
                  refine ⟨4955456196252481063883989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6607274928336641418511985 4955456196252481063883989)
                  ·
                    refine ⟨116143504599667524934781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4955456196252481063883989 116143504599667524934781)
                    ·
                      rfl

theorem cell22_339283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_339283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339283 prefixEnd_339283 := by exact prefixLift 339283
  have htrace : WordTrace (prefixWord ++ tailWord_339283) baseStart_339283 baseEnd_339283 := by
    simpa [prefixWord, tailWord_339283, baseEnd_339283] using wordTrace_append hprefix tailTrace_339283
  have hstable : (prefixWord ++ tailWord_339283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339283).length < 2 ^ (prefixWord ++ tailWord_339283).sum := by decide
  have hdescent : baseEnd_339283 < baseStart_339283 := by decide
  rcases family_descends (prefixWord ++ tailWord_339283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339285 : List Nat := [1, 3, 2, 2, 3, 2, 1, 8]
def baseStart_339285 : Nat := 118140960795 + 339285 * 2 ^ 59
def prefixEnd_339285 : Nat := 4983230072969 + 3 ^ 40 * 339285 * 2
def baseEnd_339285 : Nat := 12904909915615576264975

theorem tailTrace_339285 : CollatzResearch.WordTrace tailWord_339285 prefixEnd_339285 12904909915615576264975 := by
  unfold tailWord_339285
  simp only [CollatzResearch.WordTrace]
  refine ⟨12374740575835865109851309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8249827050557243406567539 12374740575835865109851309)
  ·
    refine ⟨4640527715938449416194241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12374740575835865109851309 4640527715938449416194241)
    ·
      refine ⟨3480395786953837062145681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4640527715938449416194241 3480395786953837062145681)
      ·
        refine ⟨2610296840215377796609261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3480395786953837062145681 2610296840215377796609261)
        ·
          refine ⟨978861315080766673728473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2610296840215377796609261 978861315080766673728473)
          ·
            refine ⟨734145986310575005296355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 978861315080766673728473 734145986310575005296355)
            ·
              refine ⟨1101218979465862507944533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734145986310575005296355 1101218979465862507944533)
              ·
                refine ⟨12904909915615576264975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1101218979465862507944533 12904909915615576264975)
                ·
                  rfl

theorem cell22_339285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 8].length) (baseStart_339285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339285 prefixEnd_339285 := by exact prefixLift 339285
  have htrace : WordTrace (prefixWord ++ tailWord_339285) baseStart_339285 baseEnd_339285 := by
    simpa [prefixWord, tailWord_339285, baseEnd_339285] using wordTrace_append hprefix tailTrace_339285
  have hstable : (prefixWord ++ tailWord_339285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339285).length < 2 ^ (prefixWord ++ tailWord_339285).sum := by decide
  have hdescent : baseEnd_339285 < baseStart_339285 := by decide
  rcases family_descends (prefixWord ++ tailWord_339285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339368 : List Nat := [2, 1, 6, 1, 2, 1, 1, 4, 1, 3]
def baseStart_339368 : Nat := 118140960795 + 339368 * 2 ^ 59
def prefixEnd_339368 : Nat := 4983230072969 + 3 ^ 40 * 339368 * 2
def baseEnd_339368 : Nat := 116172601836755636559521

theorem tailTrace_339368 : CollatzResearch.WordTrace tailWord_339368 prefixEnd_339368 116172601836755636559521 := by
  unfold tailWord_339368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6188883917267585142561379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8251845223023446856748505 6188883917267585142561379)
  ·
    refine ⟨9283325875901377713842069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6188883917267585142561379 9283325875901377713842069)
    ·
      refine ⟨435155900432877080336347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9283325875901377713842069 435155900432877080336347)
      ·
        refine ⟨652733850649315620504521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435155900432877080336347 652733850649315620504521)
        ·
          refine ⟨489550387986986715378391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652733850649315620504521 489550387986986715378391)
          ·
            refine ⟨734325581980480073067587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489550387986986715378391 734325581980480073067587)
            ·
              refine ⟨1101488372970720109601381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734325581980480073067587 1101488372970720109601381)
              ·
                refine ⟨206529069932010020550259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1101488372970720109601381 206529069932010020550259)
                ·
                  refine ⟨309793604898015030825389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206529069932010020550259 309793604898015030825389)
                  ·
                    refine ⟨116172601836755636559521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309793604898015030825389 116172601836755636559521)
                    ·
                      rfl

theorem cell22_339368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_339368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339368 prefixEnd_339368 := by exact prefixLift 339368
  have htrace : WordTrace (prefixWord ++ tailWord_339368) baseStart_339368 baseEnd_339368 := by
    simpa [prefixWord, tailWord_339368, baseEnd_339368] using wordTrace_append hprefix tailTrace_339368
  have hstable : (prefixWord ++ tailWord_339368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339368).length < 2 ^ (prefixWord ++ tailWord_339368).sum := by decide
  have hdescent : baseEnd_339368 < baseStart_339368 := by decide
  rcases family_descends (prefixWord ++ tailWord_339368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339441 : List Nat := [1, 2, 2, 2, 3, 3, 3, 1, 2, 3]
def baseStart_339441 : Nat := 118140960795 + 339441 * 2 ^ 59
def prefixEnd_339441 : Nat := 4983230072969 + 3 ^ 40 * 339441 * 2
def baseEnd_339441 : Nat := 116197591228607779484297

theorem tailTrace_339441 : CollatzResearch.WordTrace tailWord_339441 prefixEnd_339441 116197591228607779484297 := by
  unfold tailWord_339441
  simp only [CollatzResearch.WordTrace]
  refine ⟨12380430363270703752530177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8253620242180469168353451 12380430363270703752530177)
  ·
    refine ⟨9285322772453027814397633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12380430363270703752530177 9285322772453027814397633)
    ·
      refine ⟨6963992079339770860798225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9285322772453027814397633 6963992079339770860798225)
      ·
        refine ⟨5222994059504828145598669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6963992079339770860798225 5222994059504828145598669)
        ·
          refine ⟨1958622772314310554599501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5222994059504828145598669 1958622772314310554599501)
          ·
            refine ⟨734483539617866457974813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1958622772314310554599501 734483539617866457974813)
            ·
              refine ⟨275431327356699921740555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 734483539617866457974813 275431327356699921740555)
              ·
                refine ⟨413146991035049882610833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275431327356699921740555 413146991035049882610833)
                ·
                  refine ⟨309860243276287411958125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413146991035049882610833 309860243276287411958125)
                  ·
                    refine ⟨116197591228607779484297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309860243276287411958125 116197591228607779484297)
                    ·
                      rfl

theorem cell22_339441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_339441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339441 prefixEnd_339441 := by exact prefixLift 339441
  have htrace : WordTrace (prefixWord ++ tailWord_339441) baseStart_339441 baseEnd_339441 := by
    simpa [prefixWord, tailWord_339441, baseEnd_339441] using wordTrace_append hprefix tailTrace_339441
  have hstable : (prefixWord ++ tailWord_339441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339441).length < 2 ^ (prefixWord ++ tailWord_339441).sum := by decide
  have hdescent : baseEnd_339441 < baseStart_339441 := by decide
  rcases family_descends (prefixWord ++ tailWord_339441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339465 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 9]
def baseStart_339465 : Nat := 118140960795 + 339465 * 2 ^ 59
def prefixEnd_339465 : Nat := 4983230072969 + 3 ^ 40 * 339465 * 2
def baseEnd_339465 : Nat := 38735268973026572294741

theorem tailTrace_339465 : CollatzResearch.WordTrace tailWord_339465 prefixEnd_339465 38735268973026572294741 := by
  unfold tailWord_339465
  simp only [CollatzResearch.WordTrace]
  refine ⟨12381305715183755851403849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8254203810122503900935899 12381305715183755851403849)
  ·
    refine ⟨9285979286387816888552887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12381305715183755851403849 9285979286387816888552887)
    ·
      refine ⟨13928968929581725332829331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9285979286387816888552887 13928968929581725332829331)
      ·
        refine ⟨20893453394372587999243997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13928968929581725332829331 20893453394372587999243997)
        ·
          refine ⟨7835045022889720499716499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20893453394372587999243997 7835045022889720499716499)
          ·
            refine ⟨11752567534334580749574749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7835045022889720499716499 11752567534334580749574749)
            ·
              refine ⟨4407212825375467781090531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11752567534334580749574749 4407212825375467781090531)
              ·
                refine ⟨6610819238063201671635797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4407212825375467781090531 6610819238063201671635797)
                ·
                  refine ⟨38735268973026572294741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6610819238063201671635797 38735268973026572294741)
                  ·
                    rfl

theorem cell22_339465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_339465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339465 prefixEnd_339465 := by exact prefixLift 339465
  have htrace : WordTrace (prefixWord ++ tailWord_339465) baseStart_339465 baseEnd_339465 := by
    simpa [prefixWord, tailWord_339465, baseEnd_339465] using wordTrace_append hprefix tailTrace_339465
  have hstable : (prefixWord ++ tailWord_339465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339465).length < 2 ^ (prefixWord ++ tailWord_339465).sum := by decide
  have hdescent : baseEnd_339465 < baseStart_339465 := by decide
  rcases family_descends (prefixWord ++ tailWord_339465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339482 : List Nat := [3, 1, 1, 3, 1, 1, 1, 6, 5]
def baseStart_339482 : Nat := 118140960795 + 339482 * 2 ^ 59
def prefixEnd_339482 : Nat := 4983230072969 + 3 ^ 40 * 339482 * 2
def baseEnd_339482 : Nat := 38737208788832446403057

theorem tailTrace_339482 : CollatzResearch.WordTrace tailWord_339482 prefixEnd_339482 38737208788832446403057 := by
  unfold tailWord_339482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3095481439030541938693175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8254617170748111836515133 3095481439030541938693175)
  ·
    refine ⟨4643222158545812908039763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3095481439030541938693175 4643222158545812908039763)
    ·
      refine ⟨6964833237818719362059645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4643222158545812908039763 6964833237818719362059645)
      ·
        refine ⟨2611812464182019760772367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6964833237818719362059645 2611812464182019760772367)
        ·
          refine ⟨3917718696273029641158551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2611812464182019760772367 3917718696273029641158551)
          ·
            refine ⟨5876578044409544461737827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3917718696273029641158551 5876578044409544461737827)
            ·
              refine ⟨8814867066614316692606741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5876578044409544461737827 8814867066614316692606741)
              ·
                refine ⟨413196893747546094965941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8814867066614316692606741 413196893747546094965941)
                ·
                  refine ⟨38737208788832446403057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 413196893747546094965941 38737208788832446403057)
                  ·
                    rfl

theorem cell22_339482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_339482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339482 prefixEnd_339482 := by exact prefixLift 339482
  have htrace : WordTrace (prefixWord ++ tailWord_339482) baseStart_339482 baseEnd_339482 := by
    simpa [prefixWord, tailWord_339482, baseEnd_339482] using wordTrace_append hprefix tailTrace_339482
  have hstable : (prefixWord ++ tailWord_339482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339482).length < 2 ^ (prefixWord ++ tailWord_339482).sum := by decide
  have hdescent : baseEnd_339482 < baseStart_339482 := by decide
  rcases family_descends (prefixWord ++ tailWord_339482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339632 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 1, 7]
def baseStart_339632 : Nat := 118140960795 + 339632 * 2 ^ 59
def prefixEnd_339632 : Nat := 4983230072969 + 3 ^ 40 * 339632 * 2
def baseEnd_339632 : Nat := 116262974431946947958711

theorem tailTrace_339632 : CollatzResearch.WordTrace tailWord_339632 prefixEnd_339632 116262974431946947958711 := by
  unfold tailWord_339632
  simp only [CollatzResearch.WordTrace]
  refine ⟨6193698352789371686366575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8258264470385828915155433 6193698352789371686366575)
  ·
    refine ⟨9290547529184057529549863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6193698352789371686366575 9290547529184057529549863)
    ·
      refine ⟨13935821293776086294324795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9290547529184057529549863 13935821293776086294324795)
      ·
        refine ⟨20903731940664129441487193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13935821293776086294324795 20903731940664129441487193)
        ·
          refine ⟨15677798955498097081115395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20903731940664129441487193 15677798955498097081115395)
          ·
            refine ⟨23516698433247145621673093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15677798955498097081115395 23516698433247145621673093)
            ·
              refine ⟨4409380956233839804063705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23516698433247145621673093 4409380956233839804063705)
              ·
                refine ⟨3307035717175379853047779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4409380956233839804063705 3307035717175379853047779)
                ·
                  refine ⟨4960553575763069779571669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3307035717175379853047779 4960553575763069779571669)
                  ·
                    refine ⟨116262974431946947958711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4960553575763069779571669 116262974431946947958711)
                    ·
                      rfl

theorem cell22_339632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_339632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339632 prefixEnd_339632 := by exact prefixLift 339632
  have htrace : WordTrace (prefixWord ++ tailWord_339632) baseStart_339632 baseEnd_339632 := by
    simpa [prefixWord, tailWord_339632, baseEnd_339632] using wordTrace_append hprefix tailTrace_339632
  have hstable : (prefixWord ++ tailWord_339632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339632).length < 2 ^ (prefixWord ++ tailWord_339632).sum := by decide
  have hdescent : baseEnd_339632 < baseStart_339632 := by decide
  rcases family_descends (prefixWord ++ tailWord_339632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339668 : List Nat := [2, 4, 1, 3, 1, 1, 4, 1, 5]
def baseStart_339668 : Nat := 118140960795 + 339668 * 2 ^ 59
def prefixEnd_339668 : Nat := 4983230072969 + 3 ^ 40 * 339668 * 2
def baseEnd_339668 : Nat := 38758432655884951352867

theorem tailTrace_339668 : CollatzResearch.WordTrace tailWord_339668 prefixEnd_339668 38758432655884951352867 := by
  unfold tailWord_339668
  simp only [CollatzResearch.WordTrace]
  refine ⟨6194354866724160760521829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8259139822298881014029105 6194354866724160760521829)
  ·
    refine ⟨1161441537510780142597843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6194354866724160760521829 1161441537510780142597843)
    ·
      refine ⟨1742162306266170213896765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1161441537510780142597843 1742162306266170213896765)
      ·
        refine ⟨653310864849813830211287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1742162306266170213896765 653310864849813830211287)
        ·
          refine ⟨979966297274720745316931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653310864849813830211287 979966297274720745316931)
          ·
            refine ⟨1469949445912081117975397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979966297274720745316931 1469949445912081117975397)
            ·
              refine ⟨275615521108515209620387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1469949445912081117975397 275615521108515209620387)
              ·
                refine ⟨413423281662772814430581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275615521108515209620387 413423281662772814430581)
                ·
                  refine ⟨38758432655884951352867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 413423281662772814430581 38758432655884951352867)
                  ·
                    rfl

theorem cell22_339668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_339668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339668 prefixEnd_339668 := by exact prefixLift 339668
  have htrace : WordTrace (prefixWord ++ tailWord_339668) baseStart_339668 baseEnd_339668 := by
    simpa [prefixWord, tailWord_339668, baseEnd_339668] using wordTrace_append hprefix tailTrace_339668
  have hstable : (prefixWord ++ tailWord_339668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339668).length < 2 ^ (prefixWord ++ tailWord_339668).sum := by decide
  have hdescent : baseEnd_339668 < baseStart_339668 := by decide
  rcases family_descends (prefixWord ++ tailWord_339668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339681 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 3, 4]
def baseStart_339681 : Nat := 118140960795 + 339681 * 2 ^ 59
def prefixEnd_339681 : Nat := 4983230072969 + 3 ^ 40 * 339681 * 2
def baseEnd_339681 : Nat := 116279748133327153483561

theorem tailTrace_339681 : CollatzResearch.WordTrace tailWord_339681 prefixEnd_339681 116279748133327153483561 := by
  unfold tailWord_339681
  simp only [CollatzResearch.WordTrace]
  refine ⟨12389183882401224741266897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8259455921600816494177931 12389183882401224741266897)
  ·
    refine ⟨9291887911800918555950173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12389183882401224741266897 9291887911800918555950173)
    ·
      refine ⟨3484457966925344458481315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9291887911800918555950173 3484457966925344458481315)
      ·
        refine ⟨5226686950388016687721973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3484457966925344458481315 5226686950388016687721973)
        ·
          refine ⟨490001901598876564473935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5226686950388016687721973 490001901598876564473935)
          ·
            refine ⟨735002852398314846710903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490001901598876564473935 735002852398314846710903)
            ·
              refine ⟨1102504278597472270066355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735002852398314846710903 1102504278597472270066355)
              ·
                refine ⟨1653756417896208405099533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102504278597472270066355 1653756417896208405099533)
                ·
                  refine ⟨620158656711078151912325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1653756417896208405099533 620158656711078151912325)
                  ·
                    refine ⟨116279748133327153483561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 620158656711078151912325 116279748133327153483561)
                    ·
                      rfl

theorem cell22_339681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_339681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339681 prefixEnd_339681 := by exact prefixLift 339681
  have htrace : WordTrace (prefixWord ++ tailWord_339681) baseStart_339681 baseEnd_339681 := by
    simpa [prefixWord, tailWord_339681, baseEnd_339681] using wordTrace_append hprefix tailTrace_339681
  have hstable : (prefixWord ++ tailWord_339681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339681).length < 2 ^ (prefixWord ++ tailWord_339681).sum := by decide
  have hdescent : baseEnd_339681 < baseStart_339681 := by decide
  rcases family_descends (prefixWord ++ tailWord_339681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339698 : List Nat := [3, 2, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_339698 : Nat := 118140960795 + 339698 * 2 ^ 59
def prefixEnd_339698 : Nat := 4983230072969 + 3 ^ 40 * 339698 * 2
def baseEnd_339698 : Nat := 116285567580744775808509

theorem tailTrace_339698 : CollatzResearch.WordTrace tailWord_339698 prefixEnd_339698 116285567580744775808509 := by
  unfold tailWord_339698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3097450980834909161158937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8259869282226424429757165 3097450980834909161158937)
  ·
    refine ⟨2323088235626181870869203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3097450980834909161158937 2323088235626181870869203)
    ·
      refine ⟨3484632353439272806303805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2323088235626181870869203 3484632353439272806303805)
      ·
        refine ⟨1306737132539727302363927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3484632353439272806303805 1306737132539727302363927)
        ·
          refine ⟨1960105698809590953545891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306737132539727302363927 1960105698809590953545891)
          ·
            refine ⟨2940158548214386430318837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1960105698809590953545891 2940158548214386430318837)
            ·
              refine ⟨275639863895098727842391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2940158548214386430318837 275639863895098727842391)
              ·
                refine ⟨413459795842648091763587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275639863895098727842391 413459795842648091763587)
                ·
                  refine ⟨620189693763972137645381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 413459795842648091763587 620189693763972137645381)
                  ·
                    refine ⟨116285567580744775808509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 620189693763972137645381 116285567580744775808509)
                    ·
                      rfl

theorem cell22_339698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_339698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339698 prefixEnd_339698 := by exact prefixLift 339698
  have htrace : WordTrace (prefixWord ++ tailWord_339698) baseStart_339698 baseEnd_339698 := by
    simpa [prefixWord, tailWord_339698, baseEnd_339698] using wordTrace_append hprefix tailTrace_339698
  have hstable : (prefixWord ++ tailWord_339698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339698).length < 2 ^ (prefixWord ++ tailWord_339698).sum := by decide
  have hdescent : baseEnd_339698 < baseStart_339698 := by decide
  rcases family_descends (prefixWord ++ tailWord_339698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
