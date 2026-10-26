import V185TrunkScan22Chunk090

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_816845 : List Nat := [1, 6, 2, 1, 1, 2, 2, 2, 5]
def baseStart_816845 : Nat := 118140960795 + 816845 * 2 ^ 59
def prefixEnd_816845 : Nat := 4983230072969 + 3 ^ 40 * 816845 * 2
def baseEnd_816845 : Nat := 93207578938213738640201

theorem tailTrace_816845 : CollatzResearch.WordTrace tailWord_816845 prefixEnd_816845 93207578938213738640201 := by
  unfold tailWord_816845
  simp only [CollatzResearch.WordTrace]
  refine ⟨29792784725717545864467989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19861856483811697242978659 29792784725717545864467989)
  ·
    refine ⟨1396536784018009962396937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29792784725717545864467989 1396536784018009962396937)
    ·
      refine ⟨1047402588013507471797703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1396536784018009962396937 1047402588013507471797703)
      ·
        refine ⟨1571103882020261207696555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047402588013507471797703 1571103882020261207696555)
        ·
          refine ⟨2356655823030391811544833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1571103882020261207696555 2356655823030391811544833)
          ·
            refine ⟨1767491867272793858658625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2356655823030391811544833 1767491867272793858658625)
            ·
              refine ⟨1325618900454595393993969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767491867272793858658625 1325618900454595393993969)
              ·
                refine ⟨994214175340946545495477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325618900454595393993969 994214175340946545495477)
                ·
                  refine ⟨93207578938213738640201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 994214175340946545495477 93207578938213738640201)
                  ·
                    rfl

theorem cell22_816845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_816845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816845 prefixEnd_816845 := by exact prefixLift 816845
  have htrace : WordTrace (prefixWord ++ tailWord_816845) baseStart_816845 baseEnd_816845 := by
    simpa [prefixWord, tailWord_816845, baseEnd_816845] using wordTrace_append hprefix tailTrace_816845
  have hstable : (prefixWord ++ tailWord_816845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816845).length < 2 ^ (prefixWord ++ tailWord_816845).sum := by decide
  have hdescent : baseEnd_816845 < baseStart_816845 := by decide
  rcases family_descends (prefixWord ++ tailWord_816845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816933 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 3, 3]
def baseStart_816933 : Nat := 118140960795 + 816933 * 2 ^ 59
def prefixEnd_816933 : Nat := 4983230072969 + 3 ^ 40 * 816933 * 2
def baseEnd_816933 : Nat := 279652861013038319720333

theorem tailTrace_816933 : CollatzResearch.WordTrace tailWord_816933 prefixEnd_816933 279652861013038319720333 := by
  unfold tailWord_816933
  simp only [CollatzResearch.WordTrace]
  refine ⟨29795994349398736893671453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19863996232932491262447635 29795994349398736893671453)
  ·
    refine ⟨11173497881024526335126795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29795994349398736893671453 11173497881024526335126795)
    ·
      refine ⟨16760246821536789502690193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11173497881024526335126795 16760246821536789502690193)
      ·
        refine ⟨12570185116152592127017645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16760246821536789502690193 12570185116152592127017645)
        ·
          refine ⟨4713819418557222047631617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12570185116152592127017645 4713819418557222047631617)
          ·
            refine ⟨3535364563917916535723713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4713819418557222047631617 3535364563917916535723713)
            ·
              refine ⟨2651523422938437401792785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3535364563917916535723713 2651523422938437401792785)
              ·
                refine ⟨1988642567203828051344589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2651523422938437401792785 1988642567203828051344589)
                ·
                  refine ⟨745740962701435519254221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1988642567203828051344589 745740962701435519254221)
                  ·
                    refine ⟨279652861013038319720333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 745740962701435519254221 279652861013038319720333)
                    ·
                      rfl

theorem cell22_816933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_816933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816933 prefixEnd_816933 := by exact prefixLift 816933
  have htrace : WordTrace (prefixWord ++ tailWord_816933) baseStart_816933 baseEnd_816933 := by
    simpa [prefixWord, tailWord_816933, baseEnd_816933] using wordTrace_append hprefix tailTrace_816933
  have hstable : (prefixWord ++ tailWord_816933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816933).length < 2 ^ (prefixWord ++ tailWord_816933).sum := by decide
  have hdescent : baseEnd_816933 < baseStart_816933 := by decide
  rcases family_descends (prefixWord ++ tailWord_816933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816946 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 7]
def baseStart_816946 : Nat := 118140960795 + 816946 * 2 ^ 59
def prefixEnd_816946 : Nat := 4983230072969 + 3 ^ 40 * 816946 * 2
def baseEnd_816946 : Nat := 93219103726236873048431

theorem tailTrace_816946 : CollatzResearch.WordTrace tailWord_816946 prefixEnd_816946 93219103726236873048431 := by
  unfold tailWord_816946
  simp only [CollatzResearch.WordTrace]
  refine ⟨7449117124587910028473673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19864312332234426742596461 7449117124587910028473673)
  ·
    refine ⟨5586837843440932521355255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7449117124587910028473673 5586837843440932521355255)
    ·
      refine ⟨8380256765161398782032883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5586837843440932521355255 8380256765161398782032883)
      ·
        refine ⟨12570385147742098173049325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8380256765161398782032883 12570385147742098173049325)
        ·
          refine ⟨4713894430403286814893497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12570385147742098173049325 4713894430403286814893497)
          ·
            refine ⟨3535420822802465111170123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4713894430403286814893497 3535420822802465111170123)
            ·
              refine ⟨5303131234203697666755185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3535420822802465111170123 5303131234203697666755185)
              ·
                refine ⟨3977348425652773250066389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5303131234203697666755185 3977348425652773250066389)
                ·
                  refine ⟨93219103726236873048431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3977348425652773250066389 93219103726236873048431)
                  ·
                    rfl

theorem cell22_816946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_816946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816946 prefixEnd_816946 := by exact prefixLift 816946
  have htrace : WordTrace (prefixWord ++ tailWord_816946) baseStart_816946 baseEnd_816946 := by
    simpa [prefixWord, tailWord_816946, baseEnd_816946] using wordTrace_append hprefix tailTrace_816946
  have hstable : (prefixWord ++ tailWord_816946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816946).length < 2 ^ (prefixWord ++ tailWord_816946).sum := by decide
  have hdescent : baseEnd_816946 < baseStart_816946 := by decide
  rcases family_descends (prefixWord ++ tailWord_816946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816976 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 3, 4]
def baseStart_816976 : Nat := 118140960795 + 816976 * 2 ^ 59
def prefixEnd_816976 : Nat := 4983230072969 + 3 ^ 40 * 816976 * 2
def baseEnd_816976 : Nat := 279667580791800540895201

theorem tailTrace_816976 : CollatzResearch.WordTrace tailWord_816976 prefixEnd_816976 279667580791800540895201 := by
  unfold tailWord_816976
  simp only [CollatzResearch.WordTrace]
  refine ⟨14898781344121477618743391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19865041792161970158324521 14898781344121477618743391)
  ·
    refine ⟨22348172016182216428115087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14898781344121477618743391 22348172016182216428115087)
    ·
      refine ⟨33522258024273324642172631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22348172016182216428115087 33522258024273324642172631)
      ·
        refine ⟨50283387036409986963258947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33522258024273324642172631 50283387036409986963258947)
        ·
          refine ⟨75425080554614980444888421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50283387036409986963258947 75425080554614980444888421)
          ·
            refine ⟨14142202603990308833416579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75425080554614980444888421 14142202603990308833416579)
            ·
              refine ⟨21213303905985463250124869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14142202603990308833416579 21213303905985463250124869)
              ·
                refine ⟨3977494482372274359398413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21213303905985463250124869 3977494482372274359398413)
                ·
                  refine ⟨1491560430889602884774405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3977494482372274359398413 1491560430889602884774405)
                  ·
                    refine ⟨279667580791800540895201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1491560430889602884774405 279667580791800540895201)
                    ·
                      rfl

theorem cell22_816976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_816976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816976 prefixEnd_816976 := by exact prefixLift 816976
  have htrace : WordTrace (prefixWord ++ tailWord_816976) baseStart_816976 baseEnd_816976 := by
    simpa [prefixWord, tailWord_816976, baseEnd_816976] using wordTrace_append hprefix tailTrace_816976
  have hstable : (prefixWord ++ tailWord_816976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816976).length < 2 ^ (prefixWord ++ tailWord_816976).sum := by decide
  have hdescent : baseEnd_816976 < baseStart_816976 := by decide
  rcases family_descends (prefixWord ++ tailWord_816976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816980 : List Nat := [2, 4, 1, 1, 3, 1, 4, 1, 5]
def baseStart_816980 : Nat := 118140960795 + 816980 * 2 ^ 59
def prefixEnd_816980 : Nat := 4983230072969 + 3 ^ 40 * 816980 * 2
def baseEnd_816980 : Nat := 93222983357848621265063

theorem tailTrace_816980 : CollatzResearch.WordTrace tailWord_816980 prefixEnd_816980 93222983357848621265063 := by
  unfold tailWord_816980
  simp only [CollatzResearch.WordTrace]
  refine ⟨14898854290114231960316197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19865139053485642613754929 14898854290114231960316197)
  ·
    refine ⟨2793535179396418492559287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14898854290114231960316197 2793535179396418492559287)
    ·
      refine ⟨4190302769094627738838931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2793535179396418492559287 4190302769094627738838931)
      ·
        refine ⟨6285454153641941608258397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4190302769094627738838931 6285454153641941608258397)
        ·
          refine ⟨2357045307615728103096899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6285454153641941608258397 2357045307615728103096899)
          ·
            refine ⟨3535567961423592154645349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357045307615728103096899 3535567961423592154645349)
            ·
              refine ⟨662918992766923528996003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3535567961423592154645349 662918992766923528996003)
              ·
                refine ⟨994378489150385293494005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662918992766923528996003 994378489150385293494005)
                ·
                  refine ⟨93222983357848621265063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 994378489150385293494005 93222983357848621265063)
                  ·
                    rfl

theorem cell22_816980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_816980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816980 prefixEnd_816980 := by exact prefixLift 816980
  have htrace : WordTrace (prefixWord ++ tailWord_816980) baseStart_816980 baseEnd_816980 := by
    simpa [prefixWord, tailWord_816980, baseEnd_816980] using wordTrace_append hprefix tailTrace_816980
  have hstable : (prefixWord ++ tailWord_816980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816980).length < 2 ^ (prefixWord ++ tailWord_816980).sum := by decide
  have hdescent : baseEnd_816980 < baseStart_816980 := by decide
  rcases family_descends (prefixWord ++ tailWord_816980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817008 : List Nat := [2, 1, 1, 1, 4, 1, 1, 7, 4]
def baseStart_817008 : Nat := 118140960795 + 817008 * 2 ^ 59
def prefixEnd_817008 : Nat := 4983230072969 + 3 ^ 40 * 817008 * 2
def baseEnd_817008 : Nat := 93226178348587708031701

theorem tailTrace_817008 : CollatzResearch.WordTrace tailWord_817008 prefixEnd_817008 93226178348587708031701 := by
  unfold tailWord_817008
  simp only [CollatzResearch.WordTrace]
  refine ⟨14899364912063512351325839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19865819882751349801767785 14899364912063512351325839)
  ·
    refine ⟨22349047368095268526988759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14899364912063512351325839 22349047368095268526988759)
    ·
      refine ⟨33523571052142902790483139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22349047368095268526988759 33523571052142902790483139)
      ·
        refine ⟨50285356578214354185724709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33523571052142902790483139 50285356578214354185724709)
        ·
          refine ⟨9428504358415191409823383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50285356578214354185724709 9428504358415191409823383)
          ·
            refine ⟨14142756537622787114735075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9428504358415191409823383 14142756537622787114735075)
            ·
              refine ⟨21214134806434180672102613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14142756537622787114735075 21214134806434180672102613)
              ·
                refine ⟨497206284525801109502405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21214134806434180672102613 497206284525801109502405)
                ·
                  refine ⟨93226178348587708031701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 497206284525801109502405 93226178348587708031701)
                  ·
                    rfl

theorem cell22_817008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 4].length) (baseStart_817008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817008 prefixEnd_817008 := by exact prefixLift 817008
  have htrace : WordTrace (prefixWord ++ tailWord_817008) baseStart_817008 baseEnd_817008 := by
    simpa [prefixWord, tailWord_817008, baseEnd_817008] using wordTrace_append hprefix tailTrace_817008
  have hstable : (prefixWord ++ tailWord_817008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817008).length < 2 ^ (prefixWord ++ tailWord_817008).sum := by decide
  have hdescent : baseEnd_817008 < baseStart_817008 := by decide
  rcases family_descends (prefixWord ++ tailWord_817008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817021 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_817021 : Nat := 118140960795 + 817021 * 2 ^ 59
def prefixEnd_817021 : Nat := 4983230072969 + 3 ^ 40 * 817021 * 2
def baseEnd_817021 : Nat := 279682985211435423520063

theorem tailTrace_817021 : CollatzResearch.WordTrace tailWord_817021 prefixEnd_817021 279682985211435423520063 := by
  unfold tailWord_817021
  simp only [CollatzResearch.WordTrace]
  refine ⟨29799203973079927922874917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19866135982053285281916611 29799203973079927922874917)
  ·
    refine ⟨5587350744952486485539047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29799203973079927922874917 5587350744952486485539047)
    ·
      refine ⟨8381026117428729728308571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5587350744952486485539047 8381026117428729728308571)
      ·
        refine ⟨12571539176143094592462857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8381026117428729728308571 12571539176143094592462857)
        ·
          refine ⟨9428654382107320944347143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12571539176143094592462857 9428654382107320944347143)
          ·
            refine ⟨14142981573160981416520715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9428654382107320944347143 14142981573160981416520715)
            ·
              refine ⟨21214472359741472124781073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14142981573160981416520715 21214472359741472124781073)
              ·
                refine ⟨15910854269806104093585805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21214472359741472124781073 15910854269806104093585805)
                ·
                  refine ⟨5966570351177289035094677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15910854269806104093585805 5966570351177289035094677)
                  ·
                    refine ⟨279682985211435423520063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5966570351177289035094677 279682985211435423520063)
                    ·
                      rfl

theorem cell22_817021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_817021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817021 prefixEnd_817021 := by exact prefixLift 817021
  have htrace : WordTrace (prefixWord ++ tailWord_817021) baseStart_817021 baseEnd_817021 := by
    simpa [prefixWord, tailWord_817021, baseEnd_817021] using wordTrace_append hprefix tailTrace_817021
  have hstable : (prefixWord ++ tailWord_817021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817021).length < 2 ^ (prefixWord ++ tailWord_817021).sum := by decide
  have hdescent : baseEnd_817021 < baseStart_817021 := by decide
  rcases family_descends (prefixWord ++ tailWord_817021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817085 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_817085 : Nat := 118140960795 + 817085 * 2 ^ 59
def prefixEnd_817085 : Nat := 4983230072969 + 3 ^ 40 * 817085 * 2
def baseEnd_817085 : Nat := 279704893719360589919867

theorem tailTrace_817085 : CollatzResearch.WordTrace tailWord_817085 prefixEnd_817085 279704893719360589919867 := by
  unfold tailWord_817085
  simp only [CollatzResearch.WordTrace]
  refine ⟨29801538244848066853204709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19867692163232044568803139 29801538244848066853204709)
  ·
    refine ⟨5587788420909012534975883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29801538244848066853204709 5587788420909012534975883)
    ·
      refine ⟨8381682631363518802463825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5587788420909012534975883 8381682631363518802463825)
      ·
        refine ⟨6286261973522639101847869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8381682631363518802463825 6286261973522639101847869)
        ·
          refine ⟨2357348240070989663192951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6286261973522639101847869 2357348240070989663192951)
          ·
            refine ⟨3536022360106484494789427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357348240070989663192951 3536022360106484494789427)
            ·
              refine ⟨5304033540159726742184141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3536022360106484494789427 5304033540159726742184141)
              ·
                refine ⟨1989012577559897528319053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5304033540159726742184141 1989012577559897528319053)
                ·
                  refine ⟨745879716584961573119645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1989012577559897528319053 745879716584961573119645)
                  ·
                    refine ⟨279704893719360589919867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 745879716584961573119645 279704893719360589919867)
                    ·
                      rfl

theorem cell22_817085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_817085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817085 prefixEnd_817085 := by exact prefixLift 817085
  have htrace : WordTrace (prefixWord ++ tailWord_817085) baseStart_817085 baseEnd_817085 := by
    simpa [prefixWord, tailWord_817085, baseEnd_817085] using wordTrace_append hprefix tailTrace_817085
  have hstable : (prefixWord ++ tailWord_817085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817085).length < 2 ^ (prefixWord ++ tailWord_817085).sum := by decide
  have hdescent : baseEnd_817085 < baseStart_817085 := by decide
  rcases family_descends (prefixWord ++ tailWord_817085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817098 : List Nat := [3, 1, 2, 1, 2, 1, 2, 5, 5]
def baseStart_817098 : Nat := 118140960795 + 817098 * 2 ^ 59
def prefixEnd_817098 : Nat := 4983230072969 + 3 ^ 40 * 817098 * 2
def baseEnd_817098 : Nat := 93236447961677629781609

theorem tailTrace_817098 : CollatzResearch.WordTrace tailWord_817098 prefixEnd_817098 93236447961677629781609 := by
  unfold tailWord_817098
  simp only [CollatzResearch.WordTrace]
  refine ⟨7450503098450242518356987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19868008262533980048951965 7450503098450242518356987)
  ·
    refine ⟨11175754647675363777535481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7450503098450242518356987 11175754647675363777535481)
    ·
      refine ⟨8381815985756522833151611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11175754647675363777535481 8381815985756522833151611)
      ·
        refine ⟨12572723978634784249727417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8381815985756522833151611 12572723978634784249727417)
        ·
          refine ⟨9429542983976088187295563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12572723978634784249727417 9429542983976088187295563)
          ·
            refine ⟨14144314475964132280943345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9429542983976088187295563 14144314475964132280943345)
            ·
              refine ⟨10608235856973099210707509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14144314475964132280943345 10608235856973099210707509)
              ·
                refine ⟨994522111591228051003829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10608235856973099210707509 994522111591228051003829)
                ·
                  refine ⟨93236447961677629781609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 994522111591228051003829 93236447961677629781609)
                  ·
                    rfl

theorem cell22_817098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_817098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817098 prefixEnd_817098 := by exact prefixLift 817098
  have htrace : WordTrace (prefixWord ++ tailWord_817098) baseStart_817098 baseEnd_817098 := by
    simpa [prefixWord, tailWord_817098, baseEnd_817098] using wordTrace_append hprefix tailTrace_817098
  have hstable : (prefixWord ++ tailWord_817098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817098).length < 2 ^ (prefixWord ++ tailWord_817098).sum := by decide
  have hdescent : baseEnd_817098 < baseStart_817098 := by decide
  rcases family_descends (prefixWord ++ tailWord_817098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817119 : List Nat := [1, 1, 2, 3, 4, 3, 1, 3, 1, 3]
def baseStart_817119 : Nat := 118140960795 + 817119 * 2 ^ 59
def prefixEnd_817119 : Nat := 4983230072969 + 3 ^ 40 * 817119 * 2
def baseEnd_817119 : Nat := 279716532614195834569763

theorem tailTrace_817119 : CollatzResearch.WordTrace tailWord_817119 prefixEnd_817119 279716532614195834569763 := by
  unfold tailWord_817119
  simp only [CollatzResearch.WordTrace]
  refine ⟨29802778326724890659942411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19868518884483260439961607 29802778326724890659942411)
  ·
    refine ⟨44704167490087335989913617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29802778326724890659942411 44704167490087335989913617)
    ·
      refine ⟨33528125617565501992435213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44704167490087335989913617 33528125617565501992435213)
      ·
        refine ⟨12573047106587063247163205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33528125617565501992435213 12573047106587063247163205)
        ·
          refine ⟨2357446332485074358843101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12573047106587063247163205 2357446332485074358843101)
          ·
            refine ⟨884042374681902884566163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2357446332485074358843101 884042374681902884566163)
            ·
              refine ⟨1326063562022854326849245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884042374681902884566163 1326063562022854326849245)
              ·
                refine ⟨497273835758570372568467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1326063562022854326849245 497273835758570372568467)
                ·
                  refine ⟨745910753637855558852701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497273835758570372568467 745910753637855558852701)
                  ·
                    refine ⟨279716532614195834569763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 745910753637855558852701 279716532614195834569763)
                    ·
                      rfl

theorem cell22_817119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 1, 3].length) (baseStart_817119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817119 prefixEnd_817119 := by exact prefixLift 817119
  have htrace : WordTrace (prefixWord ++ tailWord_817119) baseStart_817119 baseEnd_817119 := by
    simpa [prefixWord, tailWord_817119, baseEnd_817119] using wordTrace_append hprefix tailTrace_817119
  have hstable : (prefixWord ++ tailWord_817119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817119).length < 2 ^ (prefixWord ++ tailWord_817119).sum := by decide
  have hdescent : baseEnd_817119 < baseStart_817119 := by decide
  rcases family_descends (prefixWord ++ tailWord_817119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817128 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 5, 4]
def baseStart_817128 : Nat := 118140960795 + 817128 * 2 ^ 59
def prefixEnd_817128 : Nat := 4983230072969 + 3 ^ 40 * 817128 * 2
def baseEnd_817128 : Nat := 279719613498122811094735

theorem tailTrace_817128 : CollatzResearch.WordTrace tailWord_817128 prefixEnd_817128 279719613498122811094735 := by
  unfold tailWord_817128
  simp only [CollatzResearch.WordTrace]
  refine ⟨14901553291846142598510019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19868737722461523464680025 14901553291846142598510019)
  ·
    refine ⟨22352329937769213897765029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14901553291846142598510019 22352329937769213897765029)
    ·
      refine ⟨4191061863331727605830943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22352329937769213897765029 4191061863331727605830943)
      ·
        refine ⟨6286592794997591408746415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191061863331727605830943 6286592794997591408746415)
        ·
          refine ⟨9429889192496387113119623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6286592794997591408746415 9429889192496387113119623)
          ·
            refine ⟨14144833788744580669679435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9429889192496387113119623 14144833788744580669679435)
            ·
              refine ⟨21217250683116871004519153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14144833788744580669679435 21217250683116871004519153)
              ·
                refine ⟨15912938012337653253389365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21217250683116871004519153 15912938012337653253389365)
                ·
                  refine ⟨1491837938656654992505253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15912938012337653253389365 1491837938656654992505253)
                  ·
                    refine ⟨279719613498122811094735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1491837938656654992505253 279719613498122811094735)
                    ·
                      rfl

theorem cell22_817128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_817128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817128 prefixEnd_817128 := by exact prefixLift 817128
  have htrace : WordTrace (prefixWord ++ tailWord_817128) baseStart_817128 baseEnd_817128 := by
    simpa [prefixWord, tailWord_817128, baseEnd_817128] using wordTrace_append hprefix tailTrace_817128
  have hstable : (prefixWord ++ tailWord_817128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817128).length < 2 ^ (prefixWord ++ tailWord_817128).sum := by decide
  have hdescent : baseEnd_817128 < baseStart_817128 := by decide
  rcases family_descends (prefixWord ++ tailWord_817128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817188 : List Nat := [2, 3, 1, 4, 12]
def baseStart_817188 : Nat := 118140960795 + 817188 * 2 ^ 59
def prefixEnd_817188 : Nat := 4983230072969 + 3 ^ 40 * 817188 * 2
def baseEnd_817188 : Nat := 1151194044132932734957

theorem tailTrace_817188 : CollatzResearch.WordTrace tailWord_817188 prefixEnd_817188 1151194044132932734957 := by
  unfold tailWord_817188
  simp only [CollatzResearch.WordTrace]
  refine ⟨14902647481737457722102109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19870196642316610296136145 14902647481737457722102109)
  ·
    refine ⟨5588492805651546645788291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14902647481737457722102109 5588492805651546645788291)
    ·
      refine ⟨8382739208477319968682437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5588492805651546645788291 8382739208477319968682437)
      ·
        refine ⟨1571763601589497494127957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8382739208477319968682437 1571763601589497494127957)
        ·
          refine ⟨1151194044132932734957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1571763601589497494127957 1151194044132932734957)
          ·
            rfl

theorem cell22_817188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 12].length) (baseStart_817188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817188 prefixEnd_817188 := by exact prefixLift 817188
  have htrace : WordTrace (prefixWord ++ tailWord_817188) baseStart_817188 baseEnd_817188 := by
    simpa [prefixWord, tailWord_817188, baseEnd_817188] using wordTrace_append hprefix tailTrace_817188
  have hstable : (prefixWord ++ tailWord_817188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817188).length < 2 ^ (prefixWord ++ tailWord_817188).sum := by decide
  have hdescent : baseEnd_817188 < baseStart_817188 := by decide
  rcases family_descends (prefixWord ++ tailWord_817188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817194 : List Nat := [3, 1, 4, 1, 2, 1, 4, 2, 4]
def baseStart_817194 : Nat := 118140960795 + 817194 * 2 ^ 59
def prefixEnd_817194 : Nat := 4983230072969 + 3 ^ 40 * 817194 * 2
def baseEnd_817194 : Nat := 93247402215640212981511

theorem tailTrace_817194 : CollatzResearch.WordTrace tailWord_817194 prefixEnd_817194 93247402215640212981511 := by
  unfold tailWord_817194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7451378450363294617230659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19870342534302118979281757 7451378450363294617230659)
  ·
    refine ⟨11177067675544941925845989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7451378450363294617230659 11177067675544941925845989)
    ·
      refine ⟨2095700189164676611096123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11177067675544941925845989 2095700189164676611096123)
      ·
        refine ⟨3143550283747014916644185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2095700189164676611096123 3143550283747014916644185)
        ·
          refine ⟨2357662712810261187483139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3143550283747014916644185 2357662712810261187483139)
          ·
            refine ⟨3536494069215391781224709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357662712810261187483139 3536494069215391781224709)
            ·
              refine ⟨663092637977885958979633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3536494069215391781224709 663092637977885958979633)
              ·
                refine ⟨497319478483414469234725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663092637977885958979633 497319478483414469234725)
                ·
                  refine ⟨93247402215640212981511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 497319478483414469234725 93247402215640212981511)
                  ·
                    rfl

theorem cell22_817194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_817194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817194 prefixEnd_817194 := by exact prefixLift 817194
  have htrace : WordTrace (prefixWord ++ tailWord_817194) baseStart_817194 baseEnd_817194 := by
    simpa [prefixWord, tailWord_817194, baseEnd_817194] using wordTrace_append hprefix tailTrace_817194
  have hstable : (prefixWord ++ tailWord_817194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817194).length < 2 ^ (prefixWord ++ tailWord_817194).sum := by decide
  have hdescent : baseEnd_817194 < baseStart_817194 := by decide
  rcases family_descends (prefixWord ++ tailWord_817194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817233 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 7]
def baseStart_817233 : Nat := 118140960795 + 817233 * 2 ^ 59
def prefixEnd_817233 : Nat := 4983230072969 + 3 ^ 40 * 817233 * 2
def baseEnd_817233 : Nat := 93251852381312512406471

theorem tailTrace_817233 : CollatzResearch.WordTrace tailWord_817233 prefixEnd_817233 93251852381312512406471 := by
  unfold tailWord_817233
  simp only [CollatzResearch.WordTrace]
  refine ⟨29806936248311888129592353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19871290832207925419728235 29806936248311888129592353)
  ·
    refine ⟨22355202186233916097194265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29806936248311888129592353 22355202186233916097194265)
    ·
      refine ⟨16766401639675437072895699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22355202186233916097194265 16766401639675437072895699)
      ·
        refine ⟨25149602459513155609343549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16766401639675437072895699 25149602459513155609343549)
        ·
          refine ⟨9431100922317433353503831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25149602459513155609343549 9431100922317433353503831)
          ·
            refine ⟨14146651383476150030255747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9431100922317433353503831 14146651383476150030255747)
            ·
              refine ⟨21219977075214225045383621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14146651383476150030255747 21219977075214225045383621)
              ·
                refine ⟨3978745701602667196009429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21219977075214225045383621 3978745701602667196009429)
                ·
                  refine ⟨93251852381312512406471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3978745701602667196009429 93251852381312512406471)
                  ·
                    rfl

theorem cell22_817233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_817233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817233 prefixEnd_817233 := by exact prefixLift 817233
  have htrace : WordTrace (prefixWord ++ tailWord_817233) baseStart_817233 baseEnd_817233 := by
    simpa [prefixWord, tailWord_817233, baseEnd_817233] using wordTrace_append hprefix tailTrace_817233
  have hstable : (prefixWord ++ tailWord_817233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817233).length < 2 ^ (prefixWord ++ tailWord_817233).sum := by decide
  have hdescent : baseEnd_817233 < baseStart_817233 := by decide
  rcases family_descends (prefixWord ++ tailWord_817233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817312 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 6]
def baseStart_817312 : Nat := 118140960795 + 817312 * 2 ^ 59
def prefixEnd_817312 : Nat := 4983230072969 + 3 ^ 40 * 817312 * 2
def baseEnd_817312 : Nat := 93260866819469221498057

theorem tailTrace_817312 : CollatzResearch.WordTrace tailWord_817312 prefixEnd_817312 93260866819469221498057 := by
  unfold tailWord_817312
  simp only [CollatzResearch.WordTrace]
  refine ⟨14904908807512842310859095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19873211743350456414478793 14904908807512842310859095)
  ·
    refine ⟨22357363211269263466288643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14904908807512842310859095 22357363211269263466288643)
    ·
      refine ⟨33536044816903895199432965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22357363211269263466288643 33536044816903895199432965)
      ·
        refine ⟨6288008403169480349893681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33536044816903895199432965 6288008403169480349893681)
        ·
          refine ⟨4716006302377110262420261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6288008403169480349893681 4716006302377110262420261)
          ·
            refine ⟨884251181695708174203799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4716006302377110262420261 884251181695708174203799)
            ·
              refine ⟨1326376772543562261305699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884251181695708174203799 1326376772543562261305699)
              ·
                refine ⟨1989565158815343391958549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1326376772543562261305699 1989565158815343391958549)
                ·
                  refine ⟨93260866819469221498057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1989565158815343391958549 93260866819469221498057)
                  ·
                    rfl

theorem cell22_817312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 6].length) (baseStart_817312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817312 prefixEnd_817312 := by exact prefixLift 817312
  have htrace : WordTrace (prefixWord ++ tailWord_817312) baseStart_817312 baseEnd_817312 := by
    simpa [prefixWord, tailWord_817312, baseEnd_817312] using wordTrace_append hprefix tailTrace_817312
  have hstable : (prefixWord ++ tailWord_817312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817312).length < 2 ^ (prefixWord ++ tailWord_817312).sum := by decide
  have hdescent : baseEnd_817312 < baseStart_817312 := by decide
  rcases family_descends (prefixWord ++ tailWord_817312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817370 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_817370 : Nat := 118140960795 + 817370 * 2 ^ 59
def prefixEnd_817370 : Nat := 4983230072969 + 3 ^ 40 * 817370 * 2
def baseEnd_817370 : Nat := 279802455043714846543993

theorem tailTrace_817370 : CollatzResearch.WordTrace tailWord_817370 prefixEnd_817370 279802455043714846543993 := by
  unfold tailWord_817370
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452983262203890131832391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19874622032543707018219709 7452983262203890131832391)
  ·
    refine ⟨11179474893305835197748587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7452983262203890131832391 11179474893305835197748587)
    ·
      refine ⟨16769212339958752796622881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11179474893305835197748587 16769212339958752796622881)
      ·
        refine ⟨12576909254969064597467161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16769212339958752796622881 12576909254969064597467161)
        ·
          refine ⟨9432681941226798448100371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12576909254969064597467161 9432681941226798448100371)
          ·
            refine ⟨14149022911840197672150557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9432681941226798448100371 14149022911840197672150557)
            ·
              refine ⟨5305883591940074127056459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14149022911840197672150557 5305883591940074127056459)
              ·
                refine ⟨7958825387910111190584689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305883591940074127056459 7958825387910111190584689)
                ·
                  refine ⟨5969119040932583392938517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7958825387910111190584689 5969119040932583392938517)
                  ·
                    refine ⟨279802455043714846543993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5969119040932583392938517 279802455043714846543993)
                    ·
                      rfl

theorem cell22_817370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_817370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817370 prefixEnd_817370 := by exact prefixLift 817370
  have htrace : WordTrace (prefixWord ++ tailWord_817370) baseStart_817370 baseEnd_817370 := by
    simpa [prefixWord, tailWord_817370, baseEnd_817370] using wordTrace_append hprefix tailTrace_817370
  have hstable : (prefixWord ++ tailWord_817370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817370).length < 2 ^ (prefixWord ++ tailWord_817370).sum := by decide
  have hdescent : baseEnd_817370 < baseStart_817370 := by decide
  rcases family_descends (prefixWord ++ tailWord_817370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817378 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_817378 : Nat := 118140960795 + 817378 * 2 ^ 59
def prefixEnd_817378 : Nat := 4983230072969 + 3 ^ 40 * 817378 * 2
def baseEnd_817378 : Nat := 279805193607205492343969

theorem tailTrace_817378 : CollatzResearch.WordTrace tailWord_817378 prefixEnd_817378 279805193607205492343969 := by
  unfold tailWord_817378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7453056208196644473405197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19874816555191051929080525 7453056208196644473405197)
  ·
    refine ⟨2794896078073741677526949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7453056208196644473405197 2794896078073741677526949)
    ·
      refine ⟨524043014638826564536303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2794896078073741677526949 524043014638826564536303)
      ·
        refine ⟨786064521958239846804455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524043014638826564536303 786064521958239846804455)
        ·
          refine ⟨1179096782937359770206683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786064521958239846804455 1179096782937359770206683)
          ·
            refine ⟨1768645174406039655310025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179096782937359770206683 1768645174406039655310025)
            ·
              refine ⟨1326483880804529741482519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1768645174406039655310025 1326483880804529741482519)
              ·
                refine ⟨1989725821206794612223779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1326483880804529741482519 1989725821206794612223779)
                ·
                  refine ⟨2984588731810191918335669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1989725821206794612223779 2984588731810191918335669)
                  ·
                    refine ⟨279805193607205492343969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2984588731810191918335669 279805193607205492343969)
                    ·
                      rfl

theorem cell22_817378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_817378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817378 prefixEnd_817378 := by exact prefixLift 817378
  have htrace : WordTrace (prefixWord ++ tailWord_817378) baseStart_817378 baseEnd_817378 := by
    simpa [prefixWord, tailWord_817378, baseEnd_817378] using wordTrace_append hprefix tailTrace_817378
  have hstable : (prefixWord ++ tailWord_817378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817378).length < 2 ^ (prefixWord ++ tailWord_817378).sum := by decide
  have hdescent : baseEnd_817378 < baseStart_817378 := by decide
  rcases family_descends (prefixWord ++ tailWord_817378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817464 : List Nat := [2, 1, 2, 1, 3, 1, 5, 3, 4]
def baseStart_817464 : Nat := 118140960795 + 817464 * 2 ^ 59
def prefixEnd_817464 : Nat := 4983230072969 + 3 ^ 40 * 817464 * 2
def baseEnd_817464 : Nat := 93278211054909978231235

theorem tailTrace_817464 : CollatzResearch.WordTrace tailWord_817464 prefixEnd_817464 93278211054909978231235 := by
  unfold tailWord_817464
  simp only [CollatzResearch.WordTrace]
  refine ⟨14907680755237507290625723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19876907673650009720834297 14907680755237507290625723)
  ·
    refine ⟨22361521132856260935938585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14907680755237507290625723 22361521132856260935938585)
    ·
      refine ⟨16771140849642195701953939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22361521132856260935938585 16771140849642195701953939)
      ·
        refine ⟨25156711274463293552930909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16771140849642195701953939 25156711274463293552930909)
        ·
          refine ⟨9433766727923735082349091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25156711274463293552930909 9433766727923735082349091)
          ·
            refine ⟨14150650091885602623523637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9433766727923735082349091 14150650091885602623523637)
            ·
              refine ⟨1326623446114275245955341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14150650091885602623523637 1326623446114275245955341)
              ·
                refine ⟨497483792292853217233253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1326623446114275245955341 497483792292853217233253)
                ·
                  refine ⟨93278211054909978231235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 497483792292853217233253 93278211054909978231235)
                  ·
                    rfl

theorem cell22_817464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 4].length) (baseStart_817464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817464 prefixEnd_817464 := by exact prefixLift 817464
  have htrace : WordTrace (prefixWord ++ tailWord_817464) baseStart_817464 baseEnd_817464 := by
    simpa [prefixWord, tailWord_817464, baseEnd_817464] using wordTrace_append hprefix tailTrace_817464
  have hstable : (prefixWord ++ tailWord_817464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817464).length < 2 ^ (prefixWord ++ tailWord_817464).sum := by decide
  have hdescent : baseEnd_817464 < baseStart_817464 := by decide
  rcases family_descends (prefixWord ++ tailWord_817464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817475 : List Nat := [1, 1, 1, 3, 1, 3, 12]
def baseStart_817475 : Nat := 118140960795 + 817475 * 2 ^ 59
def prefixEnd_817475 : Nat := 4983230072969 + 3 ^ 40 * 817475 * 2
def baseEnd_817475 : Nat := 10364385136649243432173

theorem tailTrace_817475 : CollatzResearch.WordTrace tailWord_817475 prefixEnd_817475 10364385136649243432173 := by
  unfold tailWord_817475
  simp only [CollatzResearch.WordTrace]
  refine ⟨29815762713435163459901879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19877175142290108973267919 29815762713435163459901879)
  ·
    refine ⟨44723644070152745189852819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29815762713435163459901879 44723644070152745189852819)
    ·
      refine ⟨67085466105229117784779229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44723644070152745189852819 67085466105229117784779229)
      ·
        refine ⟨25157049789460919169292211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67085466105229117784779229 25157049789460919169292211)
        ·
          refine ⟨37735574684191378753938317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25157049789460919169292211 37735574684191378753938317)
          ·
            refine ⟨14150840506571767032726869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37735574684191378753938317 14150840506571767032726869)
            ·
              refine ⟨10364385136649243432173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 14150840506571767032726869 10364385136649243432173)
              ·
                rfl

theorem cell22_817475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 12].length) (baseStart_817475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817475 prefixEnd_817475 := by exact prefixLift 817475
  have htrace : WordTrace (prefixWord ++ tailWord_817475) baseStart_817475 baseEnd_817475 := by
    simpa [prefixWord, tailWord_817475, baseEnd_817475] using wordTrace_append hprefix tailTrace_817475
  have hstable : (prefixWord ++ tailWord_817475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817475).length < 2 ^ (prefixWord ++ tailWord_817475).sum := by decide
  have hdescent : baseEnd_817475 < baseStart_817475 := by decide
  rcases family_descends (prefixWord ++ tailWord_817475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817479 : List Nat := [1, 1, 4, 1, 2, 2, 2, 4, 2, 3]
def baseStart_817479 : Nat := 118140960795 + 817479 * 2 ^ 59
def prefixEnd_817479 : Nat := 4983230072969 + 3 ^ 40 * 817479 * 2
def baseEnd_817479 : Nat := 279839767971274895568659

theorem tailTrace_817479 : CollatzResearch.WordTrace tailWord_817479 prefixEnd_817479 279839767971274895568659 := by
  unfold tailWord_817479
  simp only [CollatzResearch.WordTrace]
  refine ⟨29815908605420672143047491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19877272403613781428698327 29815908605420672143047491)
  ·
    refine ⟨44723862908131008214571237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29815908605420672143047491 44723862908131008214571237)
    ·
      refine ⟨8385724295274564040232107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44723862908131008214571237 8385724295274564040232107)
      ·
        refine ⟨12578586442911846060348161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8385724295274564040232107 12578586442911846060348161)
        ·
          refine ⟨9433939832183884545261121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12578586442911846060348161 9433939832183884545261121)
          ·
            refine ⟨7075454874137913408945841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9433939832183884545261121 7075454874137913408945841)
            ·
              refine ⟨5306591155603435056709381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7075454874137913408945841 5306591155603435056709381)
              ·
                refine ⟨994985841675644073133009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5306591155603435056709381 994985841675644073133009)
                ·
                  refine ⟨746239381256733054849757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 994985841675644073133009 746239381256733054849757)
                  ·
                    refine ⟨279839767971274895568659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 746239381256733054849757 279839767971274895568659)
                    ·
                      rfl

theorem cell22_817479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_817479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817479 prefixEnd_817479 := by exact prefixLift 817479
  have htrace : WordTrace (prefixWord ++ tailWord_817479) baseStart_817479 baseEnd_817479 := by
    simpa [prefixWord, tailWord_817479, baseEnd_817479] using wordTrace_append hprefix tailTrace_817479
  have hstable : (prefixWord ++ tailWord_817479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817479).length < 2 ^ (prefixWord ++ tailWord_817479).sum := by decide
  have hdescent : baseEnd_817479 < baseStart_817479 := by decide
  rcases family_descends (prefixWord ++ tailWord_817479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817492 : List Nat := [2, 4, 1, 1, 2, 2, 1, 9]
def baseStart_817492 : Nat := 118140960795 + 817492 * 2 ^ 59
def prefixEnd_817492 : Nat := 4983230072969 + 3 ^ 40 * 817492 * 2
def baseEnd_817492 : Nat := 31093802015216354999291

theorem tailTrace_817492 : CollatzResearch.WordTrace tailWord_817492 prefixEnd_817492 31093802015216354999291 := by
  unfold tailWord_817492
  simp only [CollatzResearch.WordTrace]
  refine ⟨14908191377186787681635365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19877588502915716908847153 14908191377186787681635365)
  ·
    refine ⟨2795285883222522690306631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14908191377186787681635365 2795285883222522690306631)
    ·
      refine ⟨4192928824833784035459947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2795285883222522690306631 4192928824833784035459947)
      ·
        refine ⟨6289393237250676053189921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4192928824833784035459947 6289393237250676053189921)
        ·
          refine ⟨4717044927938007039892441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6289393237250676053189921 4717044927938007039892441)
          ·
            refine ⟨3537783695953505279919331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4717044927938007039892441 3537783695953505279919331)
            ·
              refine ⟨5306675543930257919878997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3537783695953505279919331 5306675543930257919878997)
              ·
                refine ⟨31093802015216354999291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5306675543930257919878997 31093802015216354999291)
                ·
                  rfl

theorem cell22_817492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 9].length) (baseStart_817492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817492 prefixEnd_817492 := by exact prefixLift 817492
  have htrace : WordTrace (prefixWord ++ tailWord_817492) baseStart_817492 baseEnd_817492 := by
    simpa [prefixWord, tailWord_817492, baseEnd_817492] using wordTrace_append hprefix tailTrace_817492
  have hstable : (prefixWord ++ tailWord_817492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817492).length < 2 ^ (prefixWord ++ tailWord_817492).sum := by decide
  have hdescent : baseEnd_817492 < baseStart_817492 := by decide
  rcases family_descends (prefixWord ++ tailWord_817492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817500 : List Nat := [2, 2, 4, 3, 2, 1, 1, 2, 1, 4]
def baseStart_817500 : Nat := 118140960795 + 817500 * 2 ^ 59
def prefixEnd_817500 : Nat := 4983230072969 + 3 ^ 40 * 817500 * 2
def baseEnd_817500 : Nat := 279846956700437840793595

theorem tailTrace_817500 : CollatzResearch.WordTrace tailWord_817500 prefixEnd_817500 279846956700437840793595 := by
  unfold tailWord_817500
  simp only [CollatzResearch.WordTrace]
  refine ⟨14908337269172296364780977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19877783025563061819707969 14908337269172296364780977)
  ·
    refine ⟨11181252951879222273585733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14908337269172296364780977 11181252951879222273585733)
    ·
      refine ⟨2096484928477354176297325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11181252951879222273585733 2096484928477354176297325)
      ·
        refine ⟨786181848179007816111497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2096484928477354176297325 786181848179007816111497)
        ·
          refine ⟨589636386134255862083623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786181848179007816111497 589636386134255862083623)
          ·
            refine ⟨884454579201383793125435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589636386134255862083623 884454579201383793125435)
            ·
              refine ⟨1326681868802075689688153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884454579201383793125435 1326681868802075689688153)
              ·
                refine ⟨995011401601556767266115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326681868802075689688153 995011401601556767266115)
                ·
                  refine ⟨1492517102402335150899173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995011401601556767266115 1492517102402335150899173)
                  ·
                    refine ⟨279846956700437840793595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1492517102402335150899173 279846956700437840793595)
                    ·
                      rfl

theorem cell22_817500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_817500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817500 prefixEnd_817500 := by exact prefixLift 817500
  have htrace : WordTrace (prefixWord ++ tailWord_817500) baseStart_817500 baseEnd_817500 := by
    simpa [prefixWord, tailWord_817500, baseEnd_817500] using wordTrace_append hprefix tailTrace_817500
  have hstable : (prefixWord ++ tailWord_817500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817500).length < 2 ^ (prefixWord ++ tailWord_817500).sum := by decide
  have hdescent : baseEnd_817500 < baseStart_817500 := by decide
  rcases family_descends (prefixWord ++ tailWord_817500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817526 : List Nat := [5, 1, 1, 4, 2, 9]
def baseStart_817526 : Nat := 118140960795 + 817526 * 2 ^ 59
def prefixEnd_817526 : Nat := 4983230072969 + 3 ^ 40 * 817526 * 2
def baseEnd_817526 : Nat := 3455010580639289378315

theorem tailTrace_817526 : CollatzResearch.WordTrace tailWord_817526 prefixEnd_817526 3455010580639289378315 := by
  unfold tailWord_817526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863601427265649948125527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19878415224166932780005621 1863601427265649948125527)
  ·
    refine ⟨2795402140898474922188291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1863601427265649948125527 2795402140898474922188291)
    ·
      refine ⟨4193103211347712383282437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2795402140898474922188291 4193103211347712383282437)
      ·
        refine ⟨786206852127696071865457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4193103211347712383282437 786206852127696071865457)
        ·
          refine ⟨589655139095772053899093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786206852127696071865457 589655139095772053899093)
          ·
            refine ⟨3455010580639289378315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 589655139095772053899093 3455010580639289378315)
            ·
              rfl

theorem cell22_817526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 9].length) (baseStart_817526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817526 prefixEnd_817526 := by exact prefixLift 817526
  have htrace : WordTrace (prefixWord ++ tailWord_817526) baseStart_817526 baseEnd_817526 := by
    simpa [prefixWord, tailWord_817526, baseEnd_817526] using wordTrace_append hprefix tailTrace_817526
  have hstable : (prefixWord ++ tailWord_817526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817526).length < 2 ^ (prefixWord ++ tailWord_817526).sum := by decide
  have hdescent : baseEnd_817526 < baseStart_817526 := by decide
  rcases family_descends (prefixWord ++ tailWord_817526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817588 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 7]
def baseStart_817588 : Nat := 118140960795 + 817588 * 2 ^ 59
def prefixEnd_817588 : Nat := 4983230072969 + 3 ^ 40 * 817588 * 2
def baseEnd_817588 : Nat := 93292360299611648197775

theorem tailTrace_817588 : CollatzResearch.WordTrace tailWord_817588 prefixEnd_817588 93292360299611648197775 := by
  unfold tailWord_817588
  simp only [CollatzResearch.WordTrace]
  refine ⟨14909942081012891879382709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19879922774683855839176945 14909942081012891879382709)
  ·
    refine ⟨1397807070094958613692129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14909942081012891879382709 1397807070094958613692129)
    ·
      refine ⟨1048355302571218960269097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1397807070094958613692129 1048355302571218960269097)
      ·
        refine ⟨786266476928414220201823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1048355302571218960269097 786266476928414220201823)
        ·
          refine ⟨1179399715392621330302735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786266476928414220201823 1179399715392621330302735)
          ·
            refine ⟨1769099573088931995454103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179399715392621330302735 1769099573088931995454103)
            ·
              refine ⟨2653649359633397993181155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1769099573088931995454103 2653649359633397993181155)
              ·
                refine ⟨3980474039450096989771733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653649359633397993181155 3980474039450096989771733)
                ·
                  refine ⟨93292360299611648197775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3980474039450096989771733 93292360299611648197775)
                  ·
                    rfl

theorem cell22_817588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_817588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817588 prefixEnd_817588 := by exact prefixLift 817588
  have htrace : WordTrace (prefixWord ++ tailWord_817588) baseStart_817588 baseEnd_817588 := by
    simpa [prefixWord, tailWord_817588, baseEnd_817588] using wordTrace_append hprefix tailTrace_817588
  have hstable : (prefixWord ++ tailWord_817588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817588).length < 2 ^ (prefixWord ++ tailWord_817588).sum := by decide
  have hdescent : baseEnd_817588 < baseStart_817588 := by decide
  rcases family_descends (prefixWord ++ tailWord_817588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817629 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_817629 : Nat := 118140960795 + 817629 * 2 ^ 59
def prefixEnd_817629 : Nat := 4983230072969 + 3 ^ 40 * 817629 * 2
def baseEnd_817629 : Nat := 279891116036724504318199

theorem tailTrace_817629 : CollatzResearch.WordTrace tailWord_817629 prefixEnd_817629 279891116036724504318199 := by
  unfold tailWord_817629
  simp only [CollatzResearch.WordTrace]
  refine ⟨29821379554877247761007941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19880919703251498507338627 29821379554877247761007941)
  ·
    refine ⟨5591508666539483955188989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29821379554877247761007941 5591508666539483955188989)
    ·
      refine ⟨2096815749952306483195871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5591508666539483955188989 2096815749952306483195871)
      ·
        refine ⟨3145223624928459724793807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096815749952306483195871 3145223624928459724793807)
        ·
          refine ⟨4717835437392689587190711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145223624928459724793807 4717835437392689587190711)
          ·
            refine ⟨7076753156089034380786067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4717835437392689587190711 7076753156089034380786067)
            ·
              refine ⟨10615129734133551571179101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7076753156089034380786067 10615129734133551571179101)
              ·
                refine ⟨3980673650300081839192163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10615129734133551571179101 3980673650300081839192163)
                ·
                  refine ⟨5971010475450122758788245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3980673650300081839192163 5971010475450122758788245)
                  ·
                    refine ⟨279891116036724504318199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5971010475450122758788245 279891116036724504318199)
                    ·
                      rfl

theorem cell22_817629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_817629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817629 prefixEnd_817629 := by exact prefixLift 817629
  have htrace : WordTrace (prefixWord ++ tailWord_817629) baseStart_817629 baseEnd_817629 := by
    simpa [prefixWord, tailWord_817629, baseEnd_817629] using wordTrace_append hprefix tailTrace_817629
  have hstable : (prefixWord ++ tailWord_817629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817629).length < 2 ^ (prefixWord ++ tailWord_817629).sum := by decide
  have hdescent : baseEnd_817629 < baseStart_817629 := by decide
  rcases family_descends (prefixWord ++ tailWord_817629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817646 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_817646 : Nat := 118140960795 + 817646 * 2 ^ 59
def prefixEnd_817646 : Nat := 4983230072969 + 3 ^ 40 * 817646 * 2
def baseEnd_817646 : Nat := 279896935484142126643147

theorem tailTrace_817646 : CollatzResearch.WordTrace tailWord_817646 prefixEnd_817646 279896935484142126643147 := by
  unfold tailWord_817646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3727749949476957458047099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19881333063877106442917861 3727749949476957458047099)
  ·
    refine ⟨5591624924215436187070649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3727749949476957458047099 5591624924215436187070649)
    ·
      refine ⟨4193718693161577140302987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5591624924215436187070649 4193718693161577140302987)
      ·
        refine ⟨6290578039742365710454481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4193718693161577140302987 6290578039742365710454481)
        ·
          refine ⟨4717933529806774282840861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6290578039742365710454481 4717933529806774282840861)
          ·
            refine ⟨1769225073677540356065323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4717933529806774282840861 1769225073677540356065323)
            ·
              refine ⟨2653837610516310534097985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1769225073677540356065323 2653837610516310534097985)
              ·
                refine ⟨1990378207887232900573489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2653837610516310534097985 1990378207887232900573489)
                ·
                  refine ⟨1492783655915424675430117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1990378207887232900573489 1492783655915424675430117)
                  ·
                    refine ⟨279896935484142126643147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1492783655915424675430117 279896935484142126643147)
                    ·
                      rfl

theorem cell22_817646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_817646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817646 prefixEnd_817646 := by exact prefixLift 817646
  have htrace : WordTrace (prefixWord ++ tailWord_817646) baseStart_817646 baseEnd_817646 := by
    simpa [prefixWord, tailWord_817646, baseEnd_817646] using wordTrace_append hprefix tailTrace_817646
  have hstable : (prefixWord ++ tailWord_817646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817646).length < 2 ^ (prefixWord ++ tailWord_817646).sum := by decide
  have hdescent : baseEnd_817646 < baseStart_817646 := by decide
  rcases family_descends (prefixWord ++ tailWord_817646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817650 : List Nat := [3, 2, 1, 4, 2, 1, 3, 2, 4]
def baseStart_817650 : Nat := 118140960795 + 817650 * 2 ^ 59
def prefixEnd_817650 : Nat := 4983230072969 + 3 ^ 40 * 817650 * 2
def baseEnd_817650 : Nat := 93299434921962483181045

theorem tailTrace_817650 : CollatzResearch.WordTrace tailWord_817650 prefixEnd_817650 93299434921962483181045 := by
  unfold tailWord_817650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7455536371950292086880601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19881430325200778898348269 7455536371950292086880601)
  ·
    refine ⟨5591652278962719065160451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7455536371950292086880601 5591652278962719065160451)
    ·
      refine ⟨8387478418444078597740677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5591652278962719065160451 8387478418444078597740677)
      ·
        refine ⟨1572652203458264737076377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8387478418444078597740677 1572652203458264737076377)
        ·
          refine ⟨1179489152593698552807283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1572652203458264737076377 1179489152593698552807283)
          ·
            refine ⟨1769233728890547829210925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179489152593698552807283 1769233728890547829210925)
            ·
              refine ⟨663462648333955435954097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1769233728890547829210925 663462648333955435954097)
              ·
                refine ⟨497596986250466576965573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663462648333955435954097 497596986250466576965573)
                ·
                  refine ⟨93299434921962483181045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 497596986250466576965573 93299434921962483181045)
                  ·
                    rfl

theorem cell22_817650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_817650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817650 prefixEnd_817650 := by exact prefixLift 817650
  have htrace : WordTrace (prefixWord ++ tailWord_817650) baseStart_817650 baseEnd_817650 := by
    simpa [prefixWord, tailWord_817650, baseEnd_817650] using wordTrace_append hprefix tailTrace_817650
  have hstable : (prefixWord ++ tailWord_817650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817650).length < 2 ^ (prefixWord ++ tailWord_817650).sum := by decide
  have hdescent : baseEnd_817650 < baseStart_817650 := by decide
  rcases family_descends (prefixWord ++ tailWord_817650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817665 : List Nat := [1, 2, 4, 1, 3, 3, 2, 1, 2, 3]
def baseStart_817665 : Nat := 118140960795 + 817665 * 2 ^ 59
def prefixEnd_817665 : Nat := 4983230072969 + 3 ^ 40 * 817665 * 2
def baseEnd_817665 : Nat := 279903439572432410418089

theorem tailTrace_817665 : CollatzResearch.WordTrace tailWord_817665 prefixEnd_817665 279903439572432410418089 := by
  unfold tailWord_817665
  simp only [CollatzResearch.WordTrace]
  refine ⟨29822692582746825909318449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19881795055164550606212299 29822692582746825909318449)
  ·
    refine ⟨22367019437060119431988837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29822692582746825909318449 22367019437060119431988837)
    ·
      refine ⟨4193816144448772393497907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22367019437060119431988837 4193816144448772393497907)
      ·
        refine ⟨6290724216673158590246861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4193816144448772393497907 6290724216673158590246861)
        ·
          refine ⟨2359021581252434471342573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6290724216673158590246861 2359021581252434471342573)
          ·
            refine ⟨884633092969662926753465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2359021581252434471342573 884633092969662926753465)
            ·
              refine ⟨663474819727247195065099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884633092969662926753465 663474819727247195065099)
              ·
                refine ⟨995212229590870792597649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663474819727247195065099 995212229590870792597649)
                ·
                  refine ⟨746409172193153094448237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 995212229590870792597649 746409172193153094448237)
                  ·
                    refine ⟨279903439572432410418089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 746409172193153094448237 279903439572432410418089)
                    ·
                      rfl

theorem cell22_817665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_817665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817665 prefixEnd_817665 := by exact prefixLift 817665
  have htrace : WordTrace (prefixWord ++ tailWord_817665) baseStart_817665 baseEnd_817665 := by
    simpa [prefixWord, tailWord_817665, baseEnd_817665] using wordTrace_append hprefix tailTrace_817665
  have hstable : (prefixWord ++ tailWord_817665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817665).length < 2 ^ (prefixWord ++ tailWord_817665).sum := by decide
  have hdescent : baseEnd_817665 < baseStart_817665 := by decide
  rcases family_descends (prefixWord ++ tailWord_817665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817706 : List Nat := [3, 1, 4, 1, 1, 2, 1, 4, 5]
def baseStart_817706 : Nat := 118140960795 + 817706 * 2 ^ 59
def prefixEnd_817706 : Nat := 4983230072969 + 3 ^ 40 * 817706 * 2
def baseEnd_817706 : Nat := 93305824903440656714321

theorem tailTrace_817706 : CollatzResearch.WordTrace tailWord_817706 prefixEnd_817706 93305824903440656714321 := by
  unfold tailWord_817706
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456046993899572477890243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19882791983732193274373981 7456046993899572477890243)
  ·
    refine ⟨11184070490849358716835365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7456046993899572477890243 11184070490849358716835365)
    ·
      refine ⟨2097013217034254759406631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11184070490849358716835365 2097013217034254759406631)
      ·
        refine ⟨3145519825551382139109947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2097013217034254759406631 3145519825551382139109947)
        ·
          refine ⟨4718279738327073208664921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145519825551382139109947 4718279738327073208664921)
          ·
            refine ⟨3538709803745304906498691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4718279738327073208664921 3538709803745304906498691)
            ·
              refine ⟨5308064705617957359748037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3538709803745304906498691 5308064705617957359748037)
              ·
                refine ⟨995262132303367004952757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5308064705617957359748037 995262132303367004952757)
                ·
                  refine ⟨93305824903440656714321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 995262132303367004952757 93305824903440656714321)
                  ·
                    rfl

theorem cell22_817706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_817706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817706 prefixEnd_817706 := by exact prefixLift 817706
  have htrace : WordTrace (prefixWord ++ tailWord_817706) baseStart_817706 baseEnd_817706 := by
    simpa [prefixWord, tailWord_817706, baseEnd_817706] using wordTrace_append hprefix tailTrace_817706
  have hstable : (prefixWord ++ tailWord_817706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817706).length < 2 ^ (prefixWord ++ tailWord_817706).sum := by decide
  have hdescent : baseEnd_817706 < baseStart_817706 := by decide
  rcases family_descends (prefixWord ++ tailWord_817706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817719 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 5, 4]
def baseStart_817719 : Nat := 118140960795 + 817719 * 2 ^ 59
def prefixEnd_817719 : Nat := 4983230072969 + 3 ^ 40 * 817719 * 2
def baseEnd_817719 : Nat := 279921924875994269567923

theorem tailTrace_817719 : CollatzResearch.WordTrace tailWord_817719 prefixEnd_817719 279921924875994269567923 := by
  unfold tailWord_817719
  simp only [CollatzResearch.WordTrace]
  refine ⟨29824662124551193131784211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19883108083034128754522807 29824662124551193131784211)
  ·
    refine ⟨44736993186826789697676317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29824662124551193131784211 44736993186826789697676317)
    ·
      refine ⟨16776372445060046136628619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44736993186826789697676317 16776372445060046136628619)
      ·
        refine ⟨25164558667590069204942929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16776372445060046136628619 25164558667590069204942929)
        ·
          refine ⟨18873419000692551903707197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25164558667590069204942929 18873419000692551903707197)
          ·
            refine ⟨7077532125259706963890199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18873419000692551903707197 7077532125259706963890199)
            ·
              refine ⟨10616298187889560445835299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7077532125259706963890199 10616298187889560445835299)
              ·
                refine ⟨15924447281834340668752949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10616298187889560445835299 15924447281834340668752949)
                ·
                  refine ⟨1492916932671969437695589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15924447281834340668752949 1492916932671969437695589)
                  ·
                    refine ⟨279921924875994269567923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1492916932671969437695589 279921924875994269567923)
                    ·
                      rfl

theorem cell22_817719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_817719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817719 prefixEnd_817719 := by exact prefixLift 817719
  have htrace : WordTrace (prefixWord ++ tailWord_817719) baseStart_817719 baseEnd_817719 := by
    simpa [prefixWord, tailWord_817719, baseEnd_817719] using wordTrace_append hprefix tailTrace_817719
  have hstable : (prefixWord ++ tailWord_817719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817719).length < 2 ^ (prefixWord ++ tailWord_817719).sum := by decide
  have hdescent : baseEnd_817719 < baseStart_817719 := by decide
  rcases family_descends (prefixWord ++ tailWord_817719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817768 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 6]
def baseStart_817768 : Nat := 118140960795 + 817768 * 2 ^ 59
def prefixEnd_817768 : Nat := 4983230072969 + 3 ^ 40 * 817768 * 2
def baseEnd_817768 : Nat := 93312899525791491697591

theorem tailTrace_817768 : CollatzResearch.WordTrace tailWord_817768 prefixEnd_817768 93312899525791491697591 := by
  unfold tailWord_817768
  simp only [CollatzResearch.WordTrace]
  refine ⟨14913224650686837250158979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19884299534249116333545305 14913224650686837250158979)
  ·
    refine ⟨22369836976030255875238469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14913224650686837250158979 22369836976030255875238469)
    ·
      refine ⟨4194344433005672976607213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22369836976030255875238469 4194344433005672976607213)
      ·
        refine ⟨1572879162377127366227705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4194344433005672976607213 1572879162377127366227705)
        ·
          refine ⟨1179659371782845524670779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1572879162377127366227705 1179659371782845524670779)
          ·
            refine ⟨1769489057674268287006169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179659371782845524670779 1769489057674268287006169)
            ·
              refine ⟨1327116793255701215254627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1769489057674268287006169 1327116793255701215254627)
              ·
                refine ⟨1990675189883551822881941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327116793255701215254627 1990675189883551822881941)
                ·
                  refine ⟨93312899525791491697591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1990675189883551822881941 93312899525791491697591)
                  ·
                    rfl

theorem cell22_817768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 6].length) (baseStart_817768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817768 prefixEnd_817768 := by exact prefixLift 817768
  have htrace : WordTrace (prefixWord ++ tailWord_817768) baseStart_817768 baseEnd_817768 := by
    simpa [prefixWord, tailWord_817768, baseEnd_817768] using wordTrace_append hprefix tailTrace_817768
  have hstable : (prefixWord ++ tailWord_817768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817768).length < 2 ^ (prefixWord ++ tailWord_817768).sum := by decide
  have hdescent : baseEnd_817768 < baseStart_817768 := by decide
  rcases family_descends (prefixWord ++ tailWord_817768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817796 : List Nat := [2, 3, 2, 1, 3, 2, 1, 8]
def baseStart_817796 : Nat := 118140960795 + 817796 * 2 ^ 59
def prefixEnd_817796 : Nat := 4983230072969 + 3 ^ 40 * 817796 * 2
def baseEnd_817796 : Nat := 31105364838843526154743

theorem tailTrace_817796 : CollatzResearch.WordTrace tailWord_817796 prefixEnd_817796 31105364838843526154743 := by
  unfold tailWord_817796
  simp only [CollatzResearch.WordTrace]
  refine ⟨14913735272636117641168621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19884980363514823521558161 14913735272636117641168621)
  ·
    refine ⟨5592650727238544115438233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14913735272636117641168621 5592650727238544115438233)
    ·
      refine ⟨4194488045428908086578675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5592650727238544115438233 4194488045428908086578675)
      ·
        refine ⟨6291732068143362129868013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4194488045428908086578675 6291732068143362129868013)
        ·
          refine ⟨2359399525553760798700505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6291732068143362129868013 2359399525553760798700505)
          ·
            refine ⟨1769549644165320599025379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2359399525553760798700505 1769549644165320599025379)
            ·
              refine ⟨2654324466247980898538069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1769549644165320599025379 2654324466247980898538069)
              ·
                refine ⟨31105364838843526154743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2654324466247980898538069 31105364838843526154743)
                ·
                  rfl

theorem cell22_817796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 8].length) (baseStart_817796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817796 prefixEnd_817796 := by exact prefixLift 817796
  have htrace : WordTrace (prefixWord ++ tailWord_817796) baseStart_817796 baseEnd_817796 := by
    simpa [prefixWord, tailWord_817796, baseEnd_817796] using wordTrace_append hprefix tailTrace_817796
  have hstable : (prefixWord ++ tailWord_817796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817796).length < 2 ^ (prefixWord ++ tailWord_817796).sum := by decide
  have hdescent : baseEnd_817796 < baseStart_817796 := by decide
  rcases family_descends (prefixWord ++ tailWord_817796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817802 : List Nat := [3, 1, 2, 3, 4, 1, 1, 3, 4]
def baseStart_817802 : Nat := 118140960795 + 817802 * 2 ^ 59
def prefixEnd_817802 : Nat := 4983230072969 + 3 ^ 40 * 817802 * 2
def baseEnd_817802 : Nat := 93316779157403239914223

theorem tailTrace_817802 : CollatzResearch.WordTrace tailWord_817802 prefixEnd_817802 93316779157403239914223 := by
  unfold tailWord_817802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456922345812624576763915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19885126255500332204703773 7456922345812624576763915)
  ·
    refine ⟨11185383518718936865145873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7456922345812624576763915 11185383518718936865145873)
    ·
      refine ⟨8389037639039202648859405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11185383518718936865145873 8389037639039202648859405)
      ·
        refine ⟨3145889114639700993322277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8389037639039202648859405 3145889114639700993322277)
        ·
          refine ⟨589854208994943936247927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3145889114639700993322277 589854208994943936247927)
          ·
            refine ⟨884781313492415904371891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589854208994943936247927 884781313492415904371891)
            ·
              refine ⟨1327171970238623856557837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884781313492415904371891 1327171970238623856557837)
              ·
                refine ⟨497689488839483946209189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1327171970238623856557837 497689488839483946209189)
                ·
                  refine ⟨93316779157403239914223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 497689488839483946209189 93316779157403239914223)
                  ·
                    rfl

theorem cell22_817802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_817802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817802 prefixEnd_817802 := by exact prefixLift 817802
  have htrace : WordTrace (prefixWord ++ tailWord_817802) baseStart_817802 baseEnd_817802 := by
    simpa [prefixWord, tailWord_817802, baseEnd_817802] using wordTrace_append hprefix tailTrace_817802
  have hstable : (prefixWord ++ tailWord_817802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817802).length < 2 ^ (prefixWord ++ tailWord_817802).sum := by decide
  have hdescent : baseEnd_817802 < baseStart_817802 := by decide
  rcases family_descends (prefixWord ++ tailWord_817802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817922 : List Nat := [3, 4, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_817922 : Nat := 118140960795 + 817922 * 2 ^ 59
def prefixEnd_817922 : Nat := 4983230072969 + 3 ^ 40 * 817922 * 2
def baseEnd_817922 : Nat := 279991415924569406742301

theorem tailTrace_817922 : CollatzResearch.WordTrace tailWord_817922 prefixEnd_817922 279991415924569406742301 := by
  unfold tailWord_817922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7458016535703939700356005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19888044095210505867616013 7458016535703939700356005)
  ·
    refine ⟨1398378100444488693816751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7458016535703939700356005 1398378100444488693816751)
    ·
      refine ⟨2097567150666733040725127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1398378100444488693816751 2097567150666733040725127)
      ·
        refine ⟨3146350726000099561087691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2097567150666733040725127 3146350726000099561087691)
        ·
          refine ⟨4719526089000149341631537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146350726000099561087691 4719526089000149341631537)
          ·
            refine ⟨3539644566750112006223653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4719526089000149341631537 3539644566750112006223653)
            ·
              refine ⟨663683356265646001166935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3539644566750112006223653 663683356265646001166935)
              ·
                refine ⟨995525034398469001750403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663683356265646001166935 995525034398469001750403)
                ·
                  refine ⟨1493287551597703502625605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995525034398469001750403 1493287551597703502625605)
                  ·
                    refine ⟨279991415924569406742301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1493287551597703502625605 279991415924569406742301)
                    ·
                      rfl

theorem cell22_817922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_817922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817922 prefixEnd_817922 := by exact prefixLift 817922
  have htrace : WordTrace (prefixWord ++ tailWord_817922) baseStart_817922 baseEnd_817922 := by
    simpa [prefixWord, tailWord_817922, baseEnd_817922] using wordTrace_append hprefix tailTrace_817922
  have hstable : (prefixWord ++ tailWord_817922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817922).length < 2 ^ (prefixWord ++ tailWord_817922).sum := by decide
  have hdescent : baseEnd_817922 < baseStart_817922 := by decide
  rcases family_descends (prefixWord ++ tailWord_817922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817952 : List Nat := [2, 1, 1, 5, 1, 3, 3, 1, 2, 3]
def baseStart_817952 : Nat := 118140960795 + 817952 * 2 ^ 59
def prefixEnd_817952 : Nat := 4983230072969 + 3 ^ 40 * 817952 * 2
def baseEnd_817952 : Nat := 280001685537659328492209

theorem tailTrace_817952 : CollatzResearch.WordTrace tailWord_817952 prefixEnd_817952 280001685537659328492209 := by
  unfold tailWord_817952
  simp only [CollatzResearch.WordTrace]
  refine ⟨14916580166353536962508055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19888773555138049283344073 14916580166353536962508055)
  ·
    refine ⟨22374870249530305443762083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14916580166353536962508055 22374870249530305443762083)
    ·
      refine ⟨33562305374295458165643125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22374870249530305443762083 33562305374295458165643125)
      ·
        refine ⟨3146466128840199203029043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33562305374295458165643125 3146466128840199203029043)
        ·
          refine ⟨4719699193260298804543565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146466128840199203029043 4719699193260298804543565)
          ·
            refine ⟨1769887197472612051703837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4719699193260298804543565 1769887197472612051703837)
            ·
              refine ⟨663707699052229519388939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1769887197472612051703837 663707699052229519388939)
              ·
                refine ⟨995561548578344279083409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663707699052229519388939 995561548578344279083409)
                ·
                  refine ⟨746671161433758209312557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 995561548578344279083409 746671161433758209312557)
                  ·
                    refine ⟨280001685537659328492209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 746671161433758209312557 280001685537659328492209)
                    ·
                      rfl

theorem cell22_817952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 2, 3].length) (baseStart_817952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817952 prefixEnd_817952 := by exact prefixLift 817952
  have htrace : WordTrace (prefixWord ++ tailWord_817952) baseStart_817952 baseEnd_817952 := by
    simpa [prefixWord, tailWord_817952, baseEnd_817952] using wordTrace_append hprefix tailTrace_817952
  have hstable : (prefixWord ++ tailWord_817952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817952).length < 2 ^ (prefixWord ++ tailWord_817952).sum := by decide
  have hdescent : baseEnd_817952 < baseStart_817952 := by decide
  rcases family_descends (prefixWord ++ tailWord_817952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817976 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 9]
def baseStart_817976 : Nat := 118140960795 + 817976 * 2 ^ 59
def prefixEnd_817976 : Nat := 4983230072969 + 3 ^ 40 * 817976 * 2
def baseEnd_817976 : Nat := 93336633742710421964045

theorem tailTrace_817976 : CollatzResearch.WordTrace tailWord_817976 prefixEnd_817976 93336633742710421964045 := by
  unfold tailWord_817976
  simp only [CollatzResearch.WordTrace]
  refine ⟨14917017842310063011944891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19889357123080084015926521 14917017842310063011944891)
  ·
    refine ⟨22375526763465094517917337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14917017842310063011944891 22375526763465094517917337)
    ·
      refine ⟨16781645072598820888438003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22375526763465094517917337 16781645072598820888438003)
      ·
        refine ⟨25172467608898231332657005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16781645072598820888438003 25172467608898231332657005)
        ·
          refine ⟨9439675353336836749746377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25172467608898231332657005 9439675353336836749746377)
          ·
            refine ⟨7079756515002627562309783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9439675353336836749746377 7079756515002627562309783)
            ·
              refine ⟨10619634772503941343464675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7079756515002627562309783 10619634772503941343464675)
              ·
                refine ⟨15929452158755912015197013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10619634772503941343464675 15929452158755912015197013)
                ·
                  refine ⟨93336633742710421964045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15929452158755912015197013 93336633742710421964045)
                  ·
                    rfl

theorem cell22_817976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_817976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_817976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_817976 prefixEnd_817976 := by exact prefixLift 817976
  have htrace : WordTrace (prefixWord ++ tailWord_817976) baseStart_817976 baseEnd_817976 := by
    simpa [prefixWord, tailWord_817976, baseEnd_817976] using wordTrace_append hprefix tailTrace_817976
  have hstable : (prefixWord ++ tailWord_817976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817976).length < 2 ^ (prefixWord ++ tailWord_817976).sum := by decide
  have hdescent : baseEnd_817976 < baseStart_817976 := by decide
  rcases family_descends (prefixWord ++ tailWord_817976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818010 : List Nat := [3, 1, 1, 2, 1, 4, 4, 1, 5]
def baseStart_818010 : Nat := 118140960795 + 818010 * 2 ^ 59
def prefixEnd_818010 : Nat := 4983230072969 + 3 ^ 40 * 818010 * 2
def baseEnd_818010 : Nat := 93340513374322170180677

theorem tailTrace_818010 : CollatzResearch.WordTrace tailWord_818010 prefixEnd_818010 93340513374322170180677 := by
  unfold tailWord_818010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7458818941624237457656871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19890183844331299887084989 7458818941624237457656871)
  ·
    refine ⟨11188228412436356186485307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7458818941624237457656871 11188228412436356186485307)
    ·
      refine ⟨16782342618654534279727961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11188228412436356186485307 16782342618654534279727961)
      ·
        refine ⟨12586756963990900709795971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16782342618654534279727961 12586756963990900709795971)
        ·
          refine ⟨18880135445986351064693957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12586756963990900709795971 18880135445986351064693957)
          ·
            refine ⟨3540025396122440824630117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18880135445986351064693957 3540025396122440824630117)
            ·
              refine ⟨663754761772957654618147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3540025396122440824630117 663754761772957654618147)
              ·
                refine ⟨995632142659436481927221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663754761772957654618147 995632142659436481927221)
                ·
                  refine ⟨93340513374322170180677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 995632142659436481927221 93340513374322170180677)
                  ·
                    rfl

theorem cell22_818010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_818010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818010 prefixEnd_818010 := by exact prefixLift 818010
  have htrace : WordTrace (prefixWord ++ tailWord_818010) baseStart_818010 baseEnd_818010 := by
    simpa [prefixWord, tailWord_818010, baseEnd_818010] using wordTrace_append hprefix tailTrace_818010
  have hstable : (prefixWord ++ tailWord_818010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818010).length < 2 ^ (prefixWord ++ tailWord_818010).sum := by decide
  have hdescent : baseEnd_818010 < baseStart_818010 := by decide
  rcases family_descends (prefixWord ++ tailWord_818010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818132 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_818132 : Nat := 118140960795 + 818132 * 2 ^ 59
def prefixEnd_818132 : Nat := 4983230072969 + 3 ^ 40 * 818132 * 2
def baseEnd_818132 : Nat := 280063303216198858991657

theorem tailTrace_818132 : CollatzResearch.WordTrace tailWord_818132 prefixEnd_818132 280063303216198858991657 := by
  unfold tailWord_818132
  simp only [CollatzResearch.WordTrace]
  refine ⟨14919862736027482333284325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19893150314703309777712433 14919862736027482333284325)
  ·
    refine ⟨2797474263005152937490811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14919862736027482333284325 2797474263005152937490811)
    ·
      refine ⟨4196211394507729406236217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2797474263005152937490811 4196211394507729406236217)
      ·
        refine ⟨3147158545880797054677163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4196211394507729406236217 3147158545880797054677163)
        ·
          refine ⟨4720737818821195582015745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3147158545880797054677163 4720737818821195582015745)
          ·
            refine ⟨3540553364115896686511809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4720737818821195582015745 3540553364115896686511809)
            ·
              refine ⟨2655415023086922514883857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3540553364115896686511809 2655415023086922514883857)
              ·
                refine ⟨1991561267315191886162893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2655415023086922514883857 1991561267315191886162893)
                ·
                  refine ⟨746835475243196957311085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1991561267315191886162893 746835475243196957311085)
                  ·
                    refine ⟨280063303216198858991657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 746835475243196957311085 280063303216198858991657)
                    ·
                      rfl

theorem cell22_818132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_818132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818132 prefixEnd_818132 := by exact prefixLift 818132
  have htrace : WordTrace (prefixWord ++ tailWord_818132) baseStart_818132 baseEnd_818132 := by
    simpa [prefixWord, tailWord_818132, baseEnd_818132] using wordTrace_append hprefix tailTrace_818132
  have hstable : (prefixWord ++ tailWord_818132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818132).length < 2 ^ (prefixWord ++ tailWord_818132).sum := by decide
  have hdescent : baseEnd_818132 < baseStart_818132 := by decide
  rcases family_descends (prefixWord ++ tailWord_818132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818134 : List Nat := [5, 2, 1, 1, 2, 3, 2, 6]
def baseStart_818134 : Nat := 118140960795 + 818134 * 2 ^ 59
def prefixEnd_818134 : Nat := 4983230072969 + 3 ^ 40 * 818134 * 2
def baseEnd_818134 : Nat := 31118220873007946715739

theorem tailTrace_818134 : CollatzResearch.WordTrace tailWord_818134 prefixEnd_818134 31118220873007946715739 := by
  unfold tailWord_818134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1864987401127982438008841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19893198945365146005427637 1864987401127982438008841)
  ·
    refine ⟨1398740550845986828506631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1864987401127982438008841 1398740550845986828506631)
    ·
      refine ⟨2098110826268980242759947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1398740550845986828506631 2098110826268980242759947)
      ·
        refine ⟨3147166239403470364139921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2098110826268980242759947 3147166239403470364139921)
        ·
          refine ⟨2360374679552602773104941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3147166239403470364139921 2360374679552602773104941)
          ·
            refine ⟨885140504832226039914353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2360374679552602773104941 885140504832226039914353)
            ·
              refine ⟨663855378624169529935765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885140504832226039914353 663855378624169529935765)
              ·
                refine ⟨31118220873007946715739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 663855378624169529935765 31118220873007946715739)
                ·
                  rfl

theorem cell22_818134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_818134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818134 prefixEnd_818134 := by exact prefixLift 818134
  have htrace : WordTrace (prefixWord ++ tailWord_818134) baseStart_818134 baseEnd_818134 := by
    simpa [prefixWord, tailWord_818134, baseEnd_818134] using wordTrace_append hprefix tailTrace_818134
  have hstable : (prefixWord ++ tailWord_818134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818134).length < 2 ^ (prefixWord ++ tailWord_818134).sum := by decide
  have hdescent : baseEnd_818134 < baseStart_818134 := by decide
  rcases family_descends (prefixWord ++ tailWord_818134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818203 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 5, 6]
def baseStart_818203 : Nat := 118140960795 + 818203 * 2 ^ 59
def prefixEnd_818203 : Nat := 4983230072969 + 3 ^ 40 * 818203 * 2
def baseEnd_818203 : Nat := 280087607967178340466439

theorem tailTrace_818203 : CollatzResearch.WordTrace tailWord_818203 prefixEnd_818203 280087607967178340466439 := by
  unfold tailWord_818203
  simp only [CollatzResearch.WordTrace]
  refine ⟨29842315054797743792403263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19894876703198495861602175 29842315054797743792403263)
  ·
    refine ⟨44763472582196615688604895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29842315054797743792403263 44763472582196615688604895)
    ·
      refine ⟨67145208873294923532907343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44763472582196615688604895 67145208873294923532907343)
      ·
        refine ⟨100717813309942385299361015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67145208873294923532907343 100717813309942385299361015)
        ·
          refine ⟨151076719964913577949041523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100717813309942385299361015 151076719964913577949041523)
          ·
            refine ⟨226615079947370366923562285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151076719964913577949041523 226615079947370366923562285)
            ·
              refine ⟨84980654980263887596335857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226615079947370366923562285 84980654980263887596335857)
              ·
                refine ⟨63735491235197915697251893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84980654980263887596335857 63735491235197915697251893)
                ·
                  refine ⟨5975202303299804596617365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63735491235197915697251893 5975202303299804596617365)
                  ·
                    refine ⟨280087607967178340466439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5975202303299804596617365 280087607967178340466439)
                    ·
                      rfl

theorem cell22_818203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_818203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818203 prefixEnd_818203 := by exact prefixLift 818203
  have htrace : WordTrace (prefixWord ++ tailWord_818203) baseStart_818203 baseEnd_818203 := by
    simpa [prefixWord, tailWord_818203, baseEnd_818203] using wordTrace_append hprefix tailTrace_818203
  have hstable : (prefixWord ++ tailWord_818203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818203).length < 2 ^ (prefixWord ++ tailWord_818203).sum := by decide
  have hdescent : baseEnd_818203 < baseStart_818203 := by decide
  rcases family_descends (prefixWord ++ tailWord_818203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818209 : List Nat := [1, 2, 3, 2, 3, 2, 3, 1, 1, 4]
def baseStart_818209 : Nat := 118140960795 + 818209 * 2 ^ 59
def prefixEnd_818209 : Nat := 4983230072969 + 3 ^ 40 * 818209 * 2
def baseEnd_818209 : Nat := 280089661889796324816421

theorem tailTrace_818209 : CollatzResearch.WordTrace tailWord_818209 prefixEnd_818209 280089661889796324816421 := by
  unfold tailWord_818209
  simp only [CollatzResearch.WordTrace]
  refine ⟨29842533892776006817121681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19895022595184004544747787 29842533892776006817121681)
  ·
    refine ⟨22381900419582005112841261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29842533892776006817121681 22381900419582005112841261)
    ·
      refine ⟨8393212657343251917315473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22381900419582005112841261 8393212657343251917315473)
      ·
        refine ⟨6294909493007438937986605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8393212657343251917315473 6294909493007438937986605)
        ·
          refine ⟨2360591059877789601744977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6294909493007438937986605 2360591059877789601744977)
          ·
            refine ⟨1770443294908342201308733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2360591059877789601744977 1770443294908342201308733)
            ·
              refine ⟨663916235590628325490775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1770443294908342201308733 663916235590628325490775)
              ·
                refine ⟨995874353385942488236163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663916235590628325490775 995874353385942488236163)
                ·
                  refine ⟨1493811530078913732354245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995874353385942488236163 1493811530078913732354245)
                  ·
                    refine ⟨280089661889796324816421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1493811530078913732354245 280089661889796324816421)
                    ·
                      rfl

theorem cell22_818209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_818209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818209 prefixEnd_818209 := by exact prefixLift 818209
  have htrace : WordTrace (prefixWord ++ tailWord_818209) baseStart_818209 baseEnd_818209 := by
    simpa [prefixWord, tailWord_818209, baseEnd_818209] using wordTrace_append hprefix tailTrace_818209
  have hstable : (prefixWord ++ tailWord_818209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818209).length < 2 ^ (prefixWord ++ tailWord_818209).sum := by decide
  have hdescent : baseEnd_818209 < baseStart_818209 := by decide
  rcases family_descends (prefixWord ++ tailWord_818209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818220 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_818220 : Nat := 118140960795 + 818220 * 2 ^ 59
def prefixEnd_818220 : Nat := 4983230072969 + 3 ^ 40 * 818220 * 2
def baseEnd_818220 : Nat := 280093427414595962791387

theorem tailTrace_818220 : CollatzResearch.WordTrace tailWord_818220 prefixEnd_818220 280093427414595962791387 := by
  unfold tailWord_818220
  simp only [CollatzResearch.WordTrace]
  refine ⟨14921467547868077847886057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19895290063824103797181409 14921467547868077847886057)
  ·
    refine ⟨11191100660901058385914543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14921467547868077847886057 11191100660901058385914543)
    ·
      refine ⟨16786650991351587578871815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11191100660901058385914543 16786650991351587578871815)
      ·
        refine ⟨25179976487027381368307723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16786650991351587578871815 25179976487027381368307723)
        ·
          refine ⟨37769964730541072052461585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25179976487027381368307723 37769964730541072052461585)
          ·
            refine ⟨28327473547905804039346189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37769964730541072052461585 28327473547905804039346189)
            ·
              refine ⟨10622802580464676514754821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28327473547905804039346189 10622802580464676514754821)
              ·
                refine ⟨1991775483837126846516529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10622802580464676514754821 1991775483837126846516529)
                ·
                  refine ⟨1493831612877845134887397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1991775483837126846516529 1493831612877845134887397)
                  ·
                    refine ⟨280093427414595962791387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1493831612877845134887397 280093427414595962791387)
                    ·
                      rfl

theorem cell22_818220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_818220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818220 prefixEnd_818220 := by exact prefixLift 818220
  have htrace : WordTrace (prefixWord ++ tailWord_818220) baseStart_818220 baseEnd_818220 := by
    simpa [prefixWord, tailWord_818220, baseEnd_818220] using wordTrace_append hprefix tailTrace_818220
  have hstable : (prefixWord ++ tailWord_818220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818220).length < 2 ^ (prefixWord ++ tailWord_818220).sum := by decide
  have hdescent : baseEnd_818220 < baseStart_818220 := by decide
  rcases family_descends (prefixWord ++ tailWord_818220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818284 : List Nat := [2, 2, 1, 1, 3, 2, 1, 6, 1, 3]
def baseStart_818284 : Nat := 118140960795 + 818284 * 2 ^ 59
def prefixEnd_818284 : Nat := 4983230072969 + 3 ^ 40 * 818284 * 2
def baseEnd_818284 : Nat := 280115335922521129191191

theorem tailTrace_818284 : CollatzResearch.WordTrace tailWord_818284 prefixEnd_818284 280115335922521129191191 := by
  unfold tailWord_818284
  simp only [CollatzResearch.WordTrace]
  refine ⟨14922634683752147313050953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19896846245002863084067937 14922634683752147313050953)
  ·
    refine ⟨11191976012814110484788215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14922634683752147313050953 11191976012814110484788215)
    ·
      refine ⟨16787964019221165727182323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11191976012814110484788215 16787964019221165727182323)
      ·
        refine ⟨25181946028831748590773485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16787964019221165727182323 25181946028831748590773485)
        ·
          refine ⟨9443229760811905721540057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25181946028831748590773485 9443229760811905721540057)
          ·
            refine ⟨7082422320608929291155043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9443229760811905721540057 7082422320608929291155043)
            ·
              refine ⟨10623633480913393936732565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7082422320608929291155043 10623633480913393936732565)
              ·
                refine ⟨497982819417815340784339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10623633480913393936732565 497982819417815340784339)
                ·
                  refine ⟨746974229126723011176509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497982819417815340784339 746974229126723011176509)
                  ·
                    refine ⟨280115335922521129191191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 746974229126723011176509 280115335922521129191191)
                    ·
                      rfl

theorem cell22_818284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_818284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818284 prefixEnd_818284 := by exact prefixLift 818284
  have htrace : WordTrace (prefixWord ++ tailWord_818284) baseStart_818284 baseEnd_818284 := by
    simpa [prefixWord, tailWord_818284, baseEnd_818284] using wordTrace_append hprefix tailTrace_818284
  have hstable : (prefixWord ++ tailWord_818284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818284).length < 2 ^ (prefixWord ++ tailWord_818284).sum := by decide
  have hdescent : baseEnd_818284 < baseStart_818284 := by decide
  rcases family_descends (prefixWord ++ tailWord_818284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818295 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 2, 5]
def baseStart_818295 : Nat := 118140960795 + 818295 * 2 ^ 59
def prefixEnd_818295 : Nat := 4983230072969 + 3 ^ 40 * 818295 * 2
def baseEnd_818295 : Nat := 280119101447320767166157

theorem tailTrace_818295 : CollatzResearch.WordTrace tailWord_818295 prefixEnd_818295 280119101447320767166157 := by
  unfold tailWord_818295
  simp only [CollatzResearch.WordTrace]
  refine ⟨29845670570464443504752339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19897113713642962336501559 29845670570464443504752339)
  ·
    refine ⟨44768505855696665257128509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29845670570464443504752339 44768505855696665257128509)
    ·
      refine ⟨16788189695886249471423191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44768505855696665257128509 16788189695886249471423191)
      ·
        refine ⟨25182284543829374207134787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16788189695886249471423191 25182284543829374207134787)
        ·
          refine ⟨37773426815744061310702181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25182284543829374207134787 37773426815744061310702181)
          ·
            refine ⟨7082517527952011495756659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37773426815744061310702181 7082517527952011495756659)
            ·
              refine ⟨10623776291928017243634989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7082517527952011495756659 10623776291928017243634989)
              ·
                refine ⟨3983916109473006466363121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10623776291928017243634989 3983916109473006466363121)
                ·
                  refine ⟨2987937082104754849772341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3983916109473006466363121 2987937082104754849772341)
                  ·
                    refine ⟨280119101447320767166157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2987937082104754849772341 280119101447320767166157)
                    ·
                      rfl

theorem cell22_818295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_818295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818295 prefixEnd_818295 := by exact prefixLift 818295
  have htrace : WordTrace (prefixWord ++ tailWord_818295) baseStart_818295 baseEnd_818295 := by
    simpa [prefixWord, tailWord_818295, baseEnd_818295] using wordTrace_append hprefix tailTrace_818295
  have hstable : (prefixWord ++ tailWord_818295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818295).length < 2 ^ (prefixWord ++ tailWord_818295).sum := by decide
  have hdescent : baseEnd_818295 < baseStart_818295 := by decide
  rcases family_descends (prefixWord ++ tailWord_818295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818318 : List Nat := [4, 1, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_818318 : Nat := 118140960795 + 818318 * 2 ^ 59
def prefixEnd_818318 : Nat := 4983230072969 + 3 ^ 40 * 818318 * 2
def baseEnd_818318 : Nat := 280126974817356373841087

theorem tailTrace_818318 : CollatzResearch.WordTrace tailWord_818318 prefixEnd_818318 280126974817356373841087 := by
  unfold tailWord_818318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730813681172639804104951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19897672966254078955226405 3730813681172639804104951)
  ·
    refine ⟨5596220521758959706157427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3730813681172639804104951 5596220521758959706157427)
    ·
      refine ⟨8394330782638439559236141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5596220521758959706157427 8394330782638439559236141)
      ·
        refine ⟨3147874043489414834713553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8394330782638439559236141 3147874043489414834713553)
        ·
          refine ⟨2360905532617061126035165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3147874043489414834713553 2360905532617061126035165)
          ·
            refine ⟨885339574731397922263187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2360905532617061126035165 885339574731397922263187)
            ·
              refine ⟨1328009362097096883394781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885339574731397922263187 1328009362097096883394781)
              ·
                refine ⟨498003510786411331273043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1328009362097096883394781 498003510786411331273043)
                ·
                  refine ⟨747005266179616996909565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498003510786411331273043 747005266179616996909565)
                  ·
                    refine ⟨280126974817356373841087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 747005266179616996909565 280126974817356373841087)
                    ·
                      rfl

theorem cell22_818318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_818318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818318 prefixEnd_818318 := by exact prefixLift 818318
  have htrace : WordTrace (prefixWord ++ tailWord_818318) baseStart_818318 baseEnd_818318 := by
    simpa [prefixWord, tailWord_818318, baseEnd_818318] using wordTrace_append hprefix tailTrace_818318
  have hstable : (prefixWord ++ tailWord_818318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818318).length < 2 ^ (prefixWord ++ tailWord_818318).sum := by decide
  have hdescent : baseEnd_818318 < baseStart_818318 := by decide
  rcases family_descends (prefixWord ++ tailWord_818318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818355 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 3, 6]
def baseStart_818355 : Nat := 118140960795 + 818355 * 2 ^ 59
def prefixEnd_818355 : Nat := 4983230072969 + 3 ^ 40 * 818355 * 2
def baseEnd_818355 : Nat := 280139640673500610665973

theorem tailTrace_818355 : CollatzResearch.WordTrace tailWord_818355 prefixEnd_818355 280139640673500610665973 := by
  unfold tailWord_818355
  simp only [CollatzResearch.WordTrace]
  refine ⟨29847858950247073751936519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19898572633498049167957679 29847858950247073751936519)
  ·
    refine ⟨44771788425370610627904779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29847858950247073751936519 44771788425370610627904779)
    ·
      refine ⟨67157682638055915941857169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44771788425370610627904779 67157682638055915941857169)
      ·
        refine ⟨50368261978541936956392877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67157682638055915941857169 50368261978541936956392877)
        ·
          refine ⟨18888098241953226358647329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50368261978541936956392877 18888098241953226358647329)
          ·
            refine ⟨14166073681464919768985497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18888098241953226358647329 14166073681464919768985497)
            ·
              refine ⟨10624555261098689826739123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14166073681464919768985497 10624555261098689826739123)
              ·
                refine ⟨15936832891648034740108685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10624555261098689826739123 15936832891648034740108685)
                ·
                  refine ⟨5976312334368013027540757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15936832891648034740108685 5976312334368013027540757)
                  ·
                    refine ⟨280139640673500610665973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5976312334368013027540757 280139640673500610665973)
                    ·
                      rfl

theorem cell22_818355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_818355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818355 prefixEnd_818355 := by exact prefixLift 818355
  have htrace : WordTrace (prefixWord ++ tailWord_818355) baseStart_818355 baseEnd_818355 := by
    simpa [prefixWord, tailWord_818355, baseEnd_818355] using wordTrace_append hprefix tailTrace_818355
  have hstable : (prefixWord ++ tailWord_818355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818355).length < 2 ^ (prefixWord ++ tailWord_818355).sum := by decide
  have hdescent : baseEnd_818355 < baseStart_818355 := by decide
  rcases family_descends (prefixWord ++ tailWord_818355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818389 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_818389 : Nat := 118140960795 + 818389 * 2 ^ 59
def prefixEnd_818389 : Nat := 4983230072969 + 3 ^ 40 * 818389 * 2
def baseEnd_818389 : Nat := 280151279568335855315869

theorem tailTrace_818389 : CollatzResearch.WordTrace tailWord_818389 prefixEnd_818389 280151279568335855315869 := by
  unfold tailWord_818389
  simp only [CollatzResearch.WordTrace]
  refine ⟨29849099032123897558674221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19899399354749265039116147 29849099032123897558674221)
  ·
    refine ⟨11193412137046461584502833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29849099032123897558674221 11193412137046461584502833)
    ·
      refine ⟨8395059102784846188377125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11193412137046461584502833 8395059102784846188377125)
      ·
        refine ⟨1574073581772158660320711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8395059102784846188377125 1574073581772158660320711)
        ·
          refine ⟨2361110372658237990481067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574073581772158660320711 2361110372658237990481067)
          ·
            refine ⟨3541665558987356985721601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361110372658237990481067 3541665558987356985721601)
            ·
              refine ⟨2656249169240517739291201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3541665558987356985721601 2656249169240517739291201)
              ·
                refine ⟨1992186876930388304468401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2656249169240517739291201 1992186876930388304468401)
                ·
                  refine ⟨1494140157697791228351301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1992186876930388304468401 1494140157697791228351301)
                  ·
                    refine ⟨280151279568335855315869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1494140157697791228351301 280151279568335855315869)
                    ·
                      rfl

theorem cell22_818389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_818389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818389 prefixEnd_818389 := by exact prefixLift 818389
  have htrace : WordTrace (prefixWord ++ tailWord_818389) baseStart_818389 baseEnd_818389 := by
    simpa [prefixWord, tailWord_818389, baseEnd_818389] using wordTrace_append hprefix tailTrace_818389
  have hstable : (prefixWord ++ tailWord_818389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818389).length < 2 ^ (prefixWord ++ tailWord_818389).sum := by decide
  have hdescent : baseEnd_818389 < baseStart_818389 := by decide
  rcases family_descends (prefixWord ++ tailWord_818389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818419 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 3, 3]
def baseStart_818419 : Nat := 118140960795 + 818419 * 2 ^ 59
def prefixEnd_818419 : Nat := 4983230072969 + 3 ^ 40 * 818419 * 2
def baseEnd_818419 : Nat := 280161549181425777065777

theorem tailTrace_818419 : CollatzResearch.WordTrace tailWord_818419 prefixEnd_818419 280161549181425777065777 := by
  unfold tailWord_818419
  simp only [CollatzResearch.WordTrace]
  refine ⟨29850193222015212682266311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19900128814676808454844207 29850193222015212682266311)
  ·
    refine ⟨44775289833022819023399467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29850193222015212682266311 44775289833022819023399467)
    ·
      refine ⟨67162934749534228535099201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44775289833022819023399467 67162934749534228535099201)
      ·
        refine ⟨50372201062150671401324401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67162934749534228535099201 50372201062150671401324401)
        ·
          refine ⟨37779150796613003550993301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50372201062150671401324401 37779150796613003550993301)
          ·
            refine ⟨1770897693591234541452811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37779150796613003550993301 1770897693591234541452811)
            ·
              refine ⟨2656346540386851812179217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1770897693591234541452811 2656346540386851812179217)
              ·
                refine ⟨1992259905290138859134413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2656346540386851812179217 1992259905290138859134413)
                ·
                  refine ⟨747097464483802072175405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1992259905290138859134413 747097464483802072175405)
                  ·
                    refine ⟨280161549181425777065777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 747097464483802072175405 280161549181425777065777)
                    ·
                      rfl

theorem cell22_818419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 3].length) (baseStart_818419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818419 prefixEnd_818419 := by exact prefixLift 818419
  have htrace : WordTrace (prefixWord ++ tailWord_818419) baseStart_818419 baseEnd_818419 := by
    simpa [prefixWord, tailWord_818419, baseEnd_818419] using wordTrace_append hprefix tailTrace_818419
  have hstable : (prefixWord ++ tailWord_818419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818419).length < 2 ^ (prefixWord ++ tailWord_818419).sum := by decide
  have hdescent : baseEnd_818419 < baseStart_818419 := by decide
  rcases family_descends (prefixWord ++ tailWord_818419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818522 : List Nat := [3, 1, 1, 2, 1, 2, 3, 9]
def baseStart_818522 : Nat := 118140960795 + 818522 * 2 ^ 59
def prefixEnd_818522 : Nat := 4983230072969 + 3 ^ 40 * 818522 * 2
def baseEnd_818522 : Nat := 31132978687374204637829

theorem tailTrace_818522 : CollatzResearch.WordTrace tailWord_818522 prefixEnd_818522 31132978687374204637829 := by
  unfold tailWord_818522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7463487485160515318316455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19902633293761374182177213 7463487485160515318316455)
  ·
    refine ⟨11195231227740772977474683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7463487485160515318316455 11195231227740772977474683)
    ·
      refine ⟨16792846841611159466212025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11195231227740772977474683 16792846841611159466212025)
      ·
        refine ⟨12594635131208369599659019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16792846841611159466212025 12594635131208369599659019)
        ·
          refine ⟨18891952696812554399488529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12594635131208369599659019 18891952696812554399488529)
          ·
            refine ⟨14168964522609415799616397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18891952696812554399488529 14168964522609415799616397)
            ·
              refine ⟨5313361695978530924856149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14168964522609415799616397 5313361695978530924856149)
              ·
                refine ⟨31132978687374204637829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5313361695978530924856149 31132978687374204637829)
                ·
                  rfl

theorem cell22_818522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_818522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818522 prefixEnd_818522 := by exact prefixLift 818522
  have htrace : WordTrace (prefixWord ++ tailWord_818522) baseStart_818522 baseEnd_818522 := by
    simpa [prefixWord, tailWord_818522, baseEnd_818522] using wordTrace_append hprefix tailTrace_818522
  have hstable : (prefixWord ++ tailWord_818522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818522).length < 2 ^ (prefixWord ++ tailWord_818522).sum := by decide
  have hdescent : baseEnd_818522 < baseStart_818522 := by decide
  rcases family_descends (prefixWord ++ tailWord_818522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818541 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_818541 : Nat := 118140960795 + 818541 * 2 ^ 59
def prefixEnd_818541 : Nat := 4983230072969 + 3 ^ 40 * 818541 * 2
def baseEnd_818541 : Nat := 280203312274658125515403

theorem tailTrace_818541 : CollatzResearch.WordTrace tailWord_818541 prefixEnd_818541 280203312274658125515403 := by
  unfold tailWord_818541
  simp only [CollatzResearch.WordTrace]
  refine ⟨29854642927573227518207477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19903095285048818345471651 29854642927573227518207477)
  ·
    refine ⟨2798872774459990079831951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29854642927573227518207477 2798872774459990079831951)
    ·
      refine ⟨4198309161689985119747927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798872774459990079831951 4198309161689985119747927)
      ·
        refine ⟨6297463742534977679621891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4198309161689985119747927 6297463742534977679621891)
        ·
          refine ⟨9446195613802466519432837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6297463742534977679621891 9446195613802466519432837)
          ·
            refine ⟨1771161677587962472393657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9446195613802466519432837 1771161677587962472393657)
            ·
              refine ⟨1328371258190971854295243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1771161677587962472393657 1328371258190971854295243)
              ·
                refine ⟨1992556887286457781442865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328371258190971854295243 1992556887286457781442865)
                ·
                  refine ⟨1494417665464843336082149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1992556887286457781442865 1494417665464843336082149)
                  ·
                    refine ⟨280203312274658125515403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1494417665464843336082149 280203312274658125515403)
                    ·
                      rfl

theorem cell22_818541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_818541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818541 prefixEnd_818541 := by exact prefixLift 818541
  have htrace : WordTrace (prefixWord ++ tailWord_818541) baseStart_818541 baseEnd_818541 := by
    simpa [prefixWord, tailWord_818541, baseEnd_818541] using wordTrace_append hprefix tailTrace_818541
  have hstable : (prefixWord ++ tailWord_818541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818541).length < 2 ^ (prefixWord ++ tailWord_818541).sum := by decide
  have hdescent : baseEnd_818541 < baseStart_818541 := by decide
  rcases family_descends (prefixWord ++ tailWord_818541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818552 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 6, 6]
def baseStart_818552 : Nat := 118140960795 + 818552 * 2 ^ 59
def prefixEnd_818552 : Nat := 4983230072969 + 3 ^ 40 * 818552 * 2
def baseEnd_818552 : Nat := 280207077799457763490369

theorem tailTrace_818552 : CollatzResearch.WordTrace tailWord_818552 prefixEnd_818552 280207077799457763490369 := by
  unfold tailWord_818552
  simp only [CollatzResearch.WordTrace]
  refine ⟨14927522065266688198428955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19903362753688917597905273 14927522065266688198428955)
  ·
    refine ⟨22391283097900032297643433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14927522065266688198428955 22391283097900032297643433)
    ·
      refine ⟨16793462323425024223232575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22391283097900032297643433 16793462323425024223232575)
      ·
        refine ⟨25190193485137536334848863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16793462323425024223232575 25190193485137536334848863)
        ·
          refine ⟨37785290227706304502273295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25190193485137536334848863 37785290227706304502273295)
          ·
            refine ⟨56677935341559456753409943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37785290227706304502273295 56677935341559456753409943)
            ·
              refine ⟨85016903012339185130114915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56677935341559456753409943 85016903012339185130114915)
              ·
                refine ⟨127525354518508777695172373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85016903012339185130114915 127525354518508777695172373)
                ·
                  refine ⟨5977750993055098954461205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127525354518508777695172373 5977750993055098954461205)
                  ·
                    refine ⟨280207077799457763490369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5977750993055098954461205 280207077799457763490369)
                    ·
                      rfl

theorem cell22_818552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_818552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818552 prefixEnd_818552 := by exact prefixLift 818552
  have htrace : WordTrace (prefixWord ++ tailWord_818552) baseStart_818552 baseEnd_818552 := by
    simpa [prefixWord, tailWord_818552, baseEnd_818552] using wordTrace_append hprefix tailTrace_818552
  have hstable : (prefixWord ++ tailWord_818552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818552).length < 2 ^ (prefixWord ++ tailWord_818552).sum := by decide
  have hdescent : baseEnd_818552 < baseStart_818552 := by decide
  rcases family_descends (prefixWord ++ tailWord_818552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818554 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 5, 3]
def baseStart_818554 : Nat := 118140960795 + 818554 * 2 ^ 59
def prefixEnd_818554 : Nat := 4983230072969 + 3 ^ 40 * 818554 * 2
def baseEnd_818554 : Nat := 280207762440330424940363

theorem tailTrace_818554 : CollatzResearch.WordTrace tailWord_818554 prefixEnd_818554 280207762440330424940363 := by
  unfold tailWord_818554
  simp only [CollatzResearch.WordTrace]
  refine ⟨7463779269131532684607679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19903411384350753825620477 7463779269131532684607679)
  ·
    refine ⟨11195668903697299026911519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7463779269131532684607679 11195668903697299026911519)
    ·
      refine ⟨16793503355545948540367279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11195668903697299026911519 16793503355545948540367279)
      ·
        refine ⟨25190255033318922810550919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16793503355545948540367279 25190255033318922810550919)
        ·
          refine ⟨37785382549978384215826379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25190255033318922810550919 37785382549978384215826379)
          ·
            refine ⟨56678073824967576323739569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37785382549978384215826379 56678073824967576323739569)
            ·
              refine ⟨42508555368725682242804677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56678073824967576323739569 42508555368725682242804677)
              ·
                refine ⟨7970354131636065420525877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42508555368725682242804677 7970354131636065420525877)
                ·
                  refine ⟨747220699840881133174301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7970354131636065420525877 747220699840881133174301)
                  ·
                    refine ⟨280207762440330424940363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 747220699840881133174301 280207762440330424940363)
                    ·
                      rfl

theorem cell22_818554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_818554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818554 prefixEnd_818554 := by exact prefixLift 818554
  have htrace : WordTrace (prefixWord ++ tailWord_818554) baseStart_818554 baseEnd_818554 := by
    simpa [prefixWord, tailWord_818554, baseEnd_818554] using wordTrace_append hprefix tailTrace_818554
  have hstable : (prefixWord ++ tailWord_818554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818554).length < 2 ^ (prefixWord ++ tailWord_818554).sum := by decide
  have hdescent : baseEnd_818554 < baseStart_818554 := by decide
  rcases family_descends (prefixWord ++ tailWord_818554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818562 : List Nat := [3, 4, 2, 1, 1, 3, 2, 2, 4]
def baseStart_818562 : Nat := 118140960795 + 818562 * 2 ^ 59
def prefixEnd_818562 : Nat := 4983230072969 + 3 ^ 40 * 818562 * 2
def baseEnd_818562 : Nat := 93403500334607023580113

theorem tailTrace_818562 : CollatzResearch.WordTrace tailWord_818562 prefixEnd_818562 93403500334607023580113 := by
  unfold tailWord_818562
  simp only [CollatzResearch.WordTrace]
  refine ⟨7463852215124287026180485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19903605906998098736481293 7463852215124287026180485)
  ·
    refine ⟨1399472290335803817408841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7463852215124287026180485 1399472290335803817408841)
    ·
      refine ⟨1049604217751852863056631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1399472290335803817408841 1049604217751852863056631)
      ·
        refine ⟨1574406326627779294584947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049604217751852863056631 1574406326627779294584947)
        ·
          refine ⟨2361609489941668941877421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574406326627779294584947 2361609489941668941877421)
          ·
            refine ⟨885603558728125853204033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2361609489941668941877421 885603558728125853204033)
            ·
              refine ⟨664202669046094389903025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885603558728125853204033 664202669046094389903025)
              ·
                refine ⟨498152001784570792427269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664202669046094389903025 498152001784570792427269)
                ·
                  refine ⟨93403500334607023580113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 498152001784570792427269 93403500334607023580113)
                  ·
                    rfl

theorem cell22_818562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_818562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818562 prefixEnd_818562 := by exact prefixLift 818562
  have htrace : WordTrace (prefixWord ++ tailWord_818562) baseStart_818562 baseEnd_818562 := by
    simpa [prefixWord, tailWord_818562, baseEnd_818562] using wordTrace_append hprefix tailTrace_818562
  have hstable : (prefixWord ++ tailWord_818562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818562).length < 2 ^ (prefixWord ++ tailWord_818562).sum := by decide
  have hdescent : baseEnd_818562 < baseStart_818562 := by decide
  rcases family_descends (prefixWord ++ tailWord_818562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818599 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 1, 7]
def baseStart_818599 : Nat := 118140960795 + 818599 * 2 ^ 59
def prefixEnd_818599 : Nat := 4983230072969 + 3 ^ 40 * 818599 * 2
def baseEnd_818599 : Nat := 280223166859965307565225

theorem tailTrace_818599 : CollatzResearch.WordTrace tailWord_818599 prefixEnd_818599 280223166859965307565225 := by
  unfold tailWord_818599
  simp only [CollatzResearch.WordTrace]
  refine ⟨29856758361363103423818851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19904505574242068949212567 29856758361363103423818851)
  ·
    refine ⟨44785137542044655135728277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29856758361363103423818851 44785137542044655135728277)
    ·
      refine ⟨2099303322283343209487263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44785137542044655135728277 2099303322283343209487263)
      ·
        refine ⟨3148954983425014814230895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099303322283343209487263 3148954983425014814230895)
        ·
          refine ⟨4723432475137522221346343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3148954983425014814230895 4723432475137522221346343)
          ·
            refine ⟨7085148712706283332019515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4723432475137522221346343 7085148712706283332019515)
            ·
              refine ⟨10627723069059424998029273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7085148712706283332019515 10627723069059424998029273)
              ·
                refine ⟨7970792301794568748521955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10627723069059424998029273 7970792301794568748521955)
                ·
                  refine ⟨11956188452691853122782933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7970792301794568748521955 11956188452691853122782933)
                  ·
                    refine ⟨280223166859965307565225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11956188452691853122782933 280223166859965307565225)
                    ·
                      rfl

theorem cell22_818599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_818599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818599 prefixEnd_818599 := by exact prefixLift 818599
  have htrace : WordTrace (prefixWord ++ tailWord_818599) baseStart_818599 baseEnd_818599 := by
    simpa [prefixWord, tailWord_818599, baseEnd_818599] using wordTrace_append hprefix tailTrace_818599
  have hstable : (prefixWord ++ tailWord_818599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818599).length < 2 ^ (prefixWord ++ tailWord_818599).sum := by decide
  have hdescent : baseEnd_818599 < baseStart_818599 := by decide
  rcases family_descends (prefixWord ++ tailWord_818599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818605 : List Nat := [1, 5, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_818605 : Nat := 118140960795 + 818605 * 2 ^ 59
def prefixEnd_818605 : Nat := 4983230072969 + 3 ^ 40 * 818605 * 2
def baseEnd_818605 : Nat := 280225220782583291915207

theorem tailTrace_818605 : CollatzResearch.WordTrace tailWord_818605 prefixEnd_818605 280225220782583291915207 := by
  unfold tailWord_818605
  simp only [CollatzResearch.WordTrace]
  refine ⟨29856977199341366448537269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19904651466227577632358179 29856977199341366448537269)
  ·
    refine ⟨2799091612438253104550369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29856977199341366448537269 2799091612438253104550369)
    ·
      refine ⟨2099318709328689828412777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2799091612438253104550369 2099318709328689828412777)
      ·
        refine ⟨1574489031996517371309583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2099318709328689828412777 1574489031996517371309583)
        ·
          refine ⟨2361733547994776056964375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574489031996517371309583 2361733547994776056964375)
          ·
            refine ⟨3542600321992164085446563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361733547994776056964375 3542600321992164085446563)
            ·
              refine ⟨5313900482988246128169845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542600321992164085446563 5313900482988246128169845)
              ·
                refine ⟨498178170280148074515923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5313900482988246128169845 498178170280148074515923)
                ·
                  refine ⟨747267255420222111773885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498178170280148074515923 747267255420222111773885)
                  ·
                    refine ⟨280225220782583291915207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 747267255420222111773885 280225220782583291915207)
                    ·
                      rfl

theorem cell22_818605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_818605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818605 prefixEnd_818605 := by exact prefixLift 818605
  have htrace : WordTrace (prefixWord ++ tailWord_818605) baseStart_818605 baseEnd_818605 := by
    simpa [prefixWord, tailWord_818605, baseEnd_818605] using wordTrace_append hprefix tailTrace_818605
  have hstable : (prefixWord ++ tailWord_818605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818605).length < 2 ^ (prefixWord ++ tailWord_818605).sum := by decide
  have hdescent : baseEnd_818605 < baseStart_818605 := by decide
  rcases family_descends (prefixWord ++ tailWord_818605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818663 : List Nat := [1, 1, 5, 2, 1, 2, 3, 3, 4]
def baseStart_818663 : Nat := 118140960795 + 818663 * 2 ^ 59
def prefixEnd_818663 : Nat := 4983230072969 + 3 ^ 40 * 818663 * 2
def baseEnd_818663 : Nat := 93415025122630157988343

theorem tailTrace_818663 : CollatzResearch.WordTrace tailWord_818663 prefixEnd_818663 93415025122630157988343 := by
  unfold tailWord_818663
  simp only [CollatzResearch.WordTrace]
  refine ⟨29859092633131242354148643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19906061755420828236099095 29859092633131242354148643)
  ·
    refine ⟨44788638949696863531222965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29859092633131242354148643 44788638949696863531222965)
    ·
      refine ⟨4198934901534080956052153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44788638949696863531222965 4198934901534080956052153)
      ·
        refine ⟨3149201176150560717039115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4198934901534080956052153 3149201176150560717039115)
        ·
          refine ⟨4723801764225841075558673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149201176150560717039115 4723801764225841075558673)
          ·
            refine ⟨3542851323169380806669005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4723801764225841075558673 3542851323169380806669005)
            ·
              refine ⟨1328569246188517802500877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3542851323169380806669005 1328569246188517802500877)
              ·
                refine ⟨498213467320694175937829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1328569246188517802500877 498213467320694175937829)
                ·
                  refine ⟨93415025122630157988343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 498213467320694175937829 93415025122630157988343)
                  ·
                    rfl

theorem cell22_818663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 4].length) (baseStart_818663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818663 prefixEnd_818663 := by exact prefixLift 818663
  have htrace : WordTrace (prefixWord ++ tailWord_818663) baseStart_818663 baseEnd_818663 := by
    simpa [prefixWord, tailWord_818663, baseEnd_818663] using wordTrace_append hprefix tailTrace_818663
  have hstable : (prefixWord ++ tailWord_818663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818663).length < 2 ^ (prefixWord ++ tailWord_818663).sum := by decide
  have hdescent : baseEnd_818663 < baseStart_818663 := by decide
  rcases family_descends (prefixWord ++ tailWord_818663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818678 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_818678 : Nat := 118140960795 + 818678 * 2 ^ 59
def prefixEnd_818678 : Nat := 4983230072969 + 3 ^ 40 * 818678 * 2
def baseEnd_818678 : Nat := 280250210174435434839983

theorem tailTrace_818678 : CollatzResearch.WordTrace tailWord_818678 prefixEnd_818678 280250210174435434839983 := by
  unfold tailWord_818678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1866227483004806244746543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19906426485384599943963125 1866227483004806244746543)
  ·
    refine ⟨2799341224507209367119815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1866227483004806244746543 2799341224507209367119815)
    ·
      refine ⟨4199011836760814050679723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2799341224507209367119815 4199011836760814050679723)
      ·
        refine ⟨6298517755141221076019585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4199011836760814050679723 6298517755141221076019585)
        ·
          refine ⟨4723888316355915807014689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6298517755141221076019585 4723888316355915807014689)
          ·
            refine ⟨3542916237266936855261017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4723888316355915807014689 3542916237266936855261017)
            ·
              refine ⟨2657187177950202641445763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3542916237266936855261017 2657187177950202641445763)
              ·
                refine ⟨3985780766925303962168645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657187177950202641445763 3985780766925303962168645)
                ·
                  refine ⟨747333893798494492906621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3985780766925303962168645 747333893798494492906621)
                  ·
                    refine ⟨280250210174435434839983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 747333893798494492906621 280250210174435434839983)
                    ·
                      rfl

theorem cell22_818678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_818678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818678 prefixEnd_818678 := by exact prefixLift 818678
  have htrace : WordTrace (prefixWord ++ tailWord_818678) baseStart_818678 baseEnd_818678 := by
    simpa [prefixWord, tailWord_818678, baseEnd_818678] using wordTrace_append hprefix tailTrace_818678
  have hstable : (prefixWord ++ tailWord_818678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818678).length < 2 ^ (prefixWord ++ tailWord_818678).sum := by decide
  have hdescent : baseEnd_818678 < baseStart_818678 := by decide
  rcases family_descends (prefixWord ++ tailWord_818678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818695 : List Nat := [1, 1, 4, 3, 2, 1, 4, 1, 2, 3]
def baseStart_818695 : Nat := 118140960795 + 818695 * 2 ^ 59
def prefixEnd_818695 : Nat := 4983230072969 + 3 ^ 40 * 818695 * 2
def baseEnd_818695 : Nat := 280256029621853057164931

theorem tailTrace_818695 : CollatzResearch.WordTrace tailWord_818695 prefixEnd_818695 280256029621853057164931 := by
  unfold tailWord_818695
  simp only [CollatzResearch.WordTrace]
  refine ⟨29860259769015311819313539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19906839846010207879542359 29860259769015311819313539)
  ·
    refine ⟨44790389653522967728970309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29860259769015311819313539 44790389653522967728970309)
    ·
      refine ⟨8398198060035556449181933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44790389653522967728970309 8398198060035556449181933)
      ·
        refine ⟨3149324272513333668443225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8398198060035556449181933 3149324272513333668443225)
        ·
          refine ⟨2361993204385000251332419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3149324272513333668443225 2361993204385000251332419)
          ·
            refine ⟨3542989806577500376998629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361993204385000251332419 3542989806577500376998629)
            ·
              refine ⟨664310588733281320687243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3542989806577500376998629 664310588733281320687243)
              ·
                refine ⟨996465883099921981030865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664310588733281320687243 996465883099921981030865)
                ·
                  refine ⟨747349412324941485773149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 996465883099921981030865 747349412324941485773149)
                  ·
                    refine ⟨280256029621853057164931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 747349412324941485773149 280256029621853057164931)
                    ·
                      rfl

theorem cell22_818695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_818695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818695 prefixEnd_818695 := by exact prefixLift 818695
  have htrace : WordTrace (prefixWord ++ tailWord_818695) baseStart_818695 baseEnd_818695 := by
    simpa [prefixWord, tailWord_818695, baseEnd_818695] using wordTrace_append hprefix tailTrace_818695
  have hstable : (prefixWord ++ tailWord_818695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818695).length < 2 ^ (prefixWord ++ tailWord_818695).sum := by decide
  have hdescent : baseEnd_818695 < baseStart_818695 := by decide
  rcases family_descends (prefixWord ++ tailWord_818695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818719 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 9]
def baseStart_818719 : Nat := 118140960795 + 818719 * 2 ^ 59
def prefixEnd_818719 : Nat := 4983230072969 + 3 ^ 40 * 818719 * 2
def baseEnd_818719 : Nat := 93421415104108331521619

theorem tailTrace_818719 : CollatzResearch.WordTrace tailWord_818719 prefixEnd_818719 93421415104108331521619 := by
  unfold tailWord_818719
  simp only [CollatzResearch.WordTrace]
  refine ⟨29861135120928363918187211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19907423413952242612124807 29861135120928363918187211)
  ·
    refine ⟨44791702681392545877280817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29861135120928363918187211 44791702681392545877280817)
    ·
      refine ⟨33593777011044409407960613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44791702681392545877280817 33593777011044409407960613)
      ·
        refine ⟨6298833189570826763992615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33593777011044409407960613 6298833189570826763992615)
        ·
          refine ⟨9448249784356240145988923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6298833189570826763992615 9448249784356240145988923)
          ·
            refine ⟨14172374676534360218983385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9448249784356240145988923 14172374676534360218983385)
            ·
              refine ⟨10629281007400770164237539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14172374676534360218983385 10629281007400770164237539)
              ·
                refine ⟨15943921511101155246356309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10629281007400770164237539 15943921511101155246356309)
                ·
                  refine ⟨93421415104108331521619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15943921511101155246356309 93421415104108331521619)
                  ·
                    rfl

theorem cell22_818719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 9].length) (baseStart_818719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818719 prefixEnd_818719 := by exact prefixLift 818719
  have htrace : WordTrace (prefixWord ++ tailWord_818719) baseStart_818719 baseEnd_818719 := by
    simpa [prefixWord, tailWord_818719, baseEnd_818719] using wordTrace_append hprefix tailTrace_818719
  have hstable : (prefixWord ++ tailWord_818719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818719).length < 2 ^ (prefixWord ++ tailWord_818719).sum := by decide
  have hdescent : baseEnd_818719 < baseStart_818719 := by decide
  rcases family_descends (prefixWord ++ tailWord_818719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818751 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 2, 5]
def baseStart_818751 : Nat := 118140960795 + 818751 * 2 ^ 59
def prefixEnd_818751 : Nat := 4983230072969 + 3 ^ 40 * 818751 * 2
def baseEnd_818751 : Nat := 280275199566287577764759

theorem tailTrace_818751 : CollatzResearch.WordTrace tailWord_818751 prefixEnd_818751 280275199566287577764759 := by
  unfold tailWord_818751
  simp only [CollatzResearch.WordTrace]
  refine ⟨29862302256812433383352107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19908201504541622255568071 29862302256812433383352107)
  ·
    refine ⟨44793453385218650075028161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29862302256812433383352107 44793453385218650075028161)
    ·
      refine ⟨33595090038913987556271121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44793453385218650075028161 33595090038913987556271121)
      ·
        refine ⟨25196317529185490667203341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33595090038913987556271121 25196317529185490667203341)
        ·
          refine ⟨9448619073444559000201253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25196317529185490667203341 9448619073444559000201253)
          ·
            refine ⟨1771616076270854812537735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9448619073444559000201253 1771616076270854812537735)
            ·
              refine ⟨2657424114406282218806603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771616076270854812537735 2657424114406282218806603)
              ·
                refine ⟨3986136171609423328209905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657424114406282218806603 3986136171609423328209905)
                ·
                  refine ⟨2989602128707067496157429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3986136171609423328209905 2989602128707067496157429)
                  ·
                    refine ⟨280275199566287577764759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2989602128707067496157429 280275199566287577764759)
                    ·
                      rfl

theorem cell22_818751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_818751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818751 prefixEnd_818751 := by exact prefixLift 818751
  have htrace : WordTrace (prefixWord ++ tailWord_818751) baseStart_818751 baseEnd_818751 := by
    simpa [prefixWord, tailWord_818751, baseEnd_818751] using wordTrace_append hprefix tailTrace_818751
  have hstable : (prefixWord ++ tailWord_818751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818751).length < 2 ^ (prefixWord ++ tailWord_818751).sum := by decide
  have hdescent : baseEnd_818751 < baseStart_818751 := by decide
  rcases family_descends (prefixWord ++ tailWord_818751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818813 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_818813 : Nat := 118140960795 + 818813 * 2 ^ 59
def prefixEnd_818813 : Nat := 4983230072969 + 3 ^ 40 * 818813 * 2
def baseEnd_818813 : Nat := 280296423433340082714569

theorem tailTrace_818813 : CollatzResearch.WordTrace tailWord_818813 prefixEnd_818813 280296423433340082714569 := by
  unfold tailWord_818813
  simp only [CollatzResearch.WordTrace]
  refine ⟨29864563582587817972109093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19909709055058545314739395 29864563582587817972109093)
  ·
    refine ⟨5599605671735215869770455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29864563582587817972109093 5599605671735215869770455)
    ·
      refine ⟨8399408507602823804655683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5599605671735215869770455 8399408507602823804655683)
      ·
        refine ⟨12599112761404235706983525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8399408507602823804655683 12599112761404235706983525)
        ·
          refine ⟨2362333642763294195059411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12599112761404235706983525 2362333642763294195059411)
          ·
            refine ⟨3543500464144941292589117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2362333642763294195059411 3543500464144941292589117)
            ·
              refine ⟨1328812674054352984720919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3543500464144941292589117 1328812674054352984720919)
              ·
                refine ⟨1993219011081529477081379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328812674054352984720919 1993219011081529477081379)
                ·
                  refine ⟨2989828516622294215622069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993219011081529477081379 2989828516622294215622069)
                  ·
                    refine ⟨280296423433340082714569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2989828516622294215622069 280296423433340082714569)
                    ·
                      rfl

theorem cell22_818813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_818813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818813 prefixEnd_818813 := by exact prefixLift 818813
  have htrace : WordTrace (prefixWord ++ tailWord_818813) baseStart_818813 baseEnd_818813 := by
    simpa [prefixWord, tailWord_818813, baseEnd_818813] using wordTrace_append hprefix tailTrace_818813
  have hstable : (prefixWord ++ tailWord_818813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818813).length < 2 ^ (prefixWord ++ tailWord_818813).sum := by decide
  have hdescent : baseEnd_818813 < baseStart_818813 := by decide
  rcases family_descends (prefixWord ++ tailWord_818813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818965 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 4, 3]
def baseStart_818965 : Nat := 118140960795 + 818965 * 2 ^ 59
def prefixEnd_818965 : Nat := 4983230072969 + 3 ^ 40 * 818965 * 2
def baseEnd_818965 : Nat := 280348456139662352914103

theorem tailTrace_818965 : CollatzResearch.WordTrace tailWord_818965 prefixEnd_818965 280348456139662352914103 := by
  unfold tailWord_818965
  simp only [CollatzResearch.WordTrace]
  refine ⟨29870107478037147931642349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19913404985358098621094899 29870107478037147931642349)
  ·
    refine ⟨11201290304263930474365881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29870107478037147931642349 11201290304263930474365881)
    ·
      refine ⟨8400967728197947855774411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11201290304263930474365881 8400967728197947855774411)
      ·
        refine ⟨12601451592296921783661617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8400967728197947855774411 12601451592296921783661617)
        ·
          refine ⟨9451088694222691337746213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12601451592296921783661617 9451088694222691337746213)
          ·
            refine ⟨1772079130166754625827415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9451088694222691337746213 1772079130166754625827415)
            ·
              refine ⟨2658118695250131938741123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772079130166754625827415 2658118695250131938741123)
              ·
                refine ⟨3987178042875197908111685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2658118695250131938741123 3987178042875197908111685)
                ·
                  refine ⟨747595883039099607770941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3987178042875197908111685 747595883039099607770941)
                  ·
                    refine ⟨280348456139662352914103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 747595883039099607770941 280348456139662352914103)
                    ·
                      rfl

theorem cell22_818965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_818965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818965 prefixEnd_818965 := by exact prefixLift 818965
  have htrace : WordTrace (prefixWord ++ tailWord_818965) baseStart_818965 baseEnd_818965 := by
    simpa [prefixWord, tailWord_818965, baseEnd_818965] using wordTrace_append hprefix tailTrace_818965
  have hstable : (prefixWord ++ tailWord_818965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818965).length < 2 ^ (prefixWord ++ tailWord_818965).sum := by decide
  have hdescent : baseEnd_818965 < baseStart_818965 := by decide
  rcases family_descends (prefixWord ++ tailWord_818965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818978 : List Nat := [3, 3, 1, 1, 2, 1, 2, 9]
def baseStart_818978 : Nat := 118140960795 + 818978 * 2 ^ 59
def prefixEnd_818978 : Nat := 4983230072969 + 3 ^ 40 * 818978 * 2
def baseEnd_818978 : Nat := 31150322922814961371007

theorem tailTrace_818978 : CollatzResearch.WordTrace tailWord_818978 prefixEnd_818978 31150322922814961371007 := by
  unfold tailWord_818978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7467645406747512787966397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19913721084660034101243725 7467645406747512787966397)
  ·
    refine ⟨2800367027530317295487399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7467645406747512787966397 2800367027530317295487399)
    ·
      refine ⟨4200550541295475943231099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2800367027530317295487399 4200550541295475943231099)
      ·
        refine ⟨6300825811943213914846649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4200550541295475943231099 6300825811943213914846649)
        ·
          refine ⟨4725619358957410436134987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6300825811943213914846649 4725619358957410436134987)
          ·
            refine ⟨7088429038436115654202481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4725619358957410436134987 7088429038436115654202481)
            ·
              refine ⟨5316321778827086740651861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7088429038436115654202481 5316321778827086740651861)
              ·
                refine ⟨31150322922814961371007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5316321778827086740651861 31150322922814961371007)
                ·
                  rfl

theorem cell22_818978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_818978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_818978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_818978 prefixEnd_818978 := by exact prefixLift 818978
  have htrace : WordTrace (prefixWord ++ tailWord_818978) baseStart_818978 baseEnd_818978 := by
    simpa [prefixWord, tailWord_818978, baseEnd_818978] using wordTrace_append hprefix tailTrace_818978
  have hstable : (prefixWord ++ tailWord_818978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818978).length < 2 ^ (prefixWord ++ tailWord_818978).sum := by decide
  have hdescent : baseEnd_818978 < baseStart_818978 := by decide
  rcases family_descends (prefixWord ++ tailWord_818978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819001 : List Nat := [1, 2, 1, 7, 2, 1, 1, 3, 4]
def baseStart_819001 : Nat := 118140960795 + 819001 * 2 ^ 59
def prefixEnd_819001 : Nat := 4983230072969 + 3 ^ 40 * 819001 * 2
def baseEnd_819001 : Nat := 93453593225123419671331

theorem tailTrace_819001 : CollatzResearch.WordTrace tailWord_819001 prefixEnd_819001 93453593225123419671331 := by
  unfold tailWord_819001
  simp only [CollatzResearch.WordTrace]
  refine ⟨29871420505906726079952857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19914280337271150719968571 29871420505906726079952857)
  ·
    refine ⟨22403565379430044559964643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29871420505906726079952857 22403565379430044559964643)
    ·
      refine ⟨33605348069145066839946965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22403565379430044559964643 33605348069145066839946965)
      ·
        refine ⟨787625345370587504061257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 33605348069145066839946965 787625345370587504061257)
        ·
          refine ⟨590719009027940628045943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 787625345370587504061257 590719009027940628045943)
          ·
            refine ⟨886078513541910942068915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590719009027940628045943 886078513541910942068915)
            ·
              refine ⟨1329117770312866413103373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886078513541910942068915 1329117770312866413103373)
              ·
                refine ⟨498419163867324904913765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1329117770312866413103373 498419163867324904913765)
                ·
                  refine ⟨93453593225123419671331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 498419163867324904913765 93453593225123419671331)
                  ·
                    rfl

theorem cell22_819001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 4].length) (baseStart_819001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819001 prefixEnd_819001 := by exact prefixLift 819001
  have htrace : WordTrace (prefixWord ++ tailWord_819001) baseStart_819001 baseEnd_819001 := by
    simpa [prefixWord, tailWord_819001, baseEnd_819001] using wordTrace_append hprefix tailTrace_819001
  have hstable : (prefixWord ++ tailWord_819001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819001).length < 2 ^ (prefixWord ++ tailWord_819001).sum := by decide
  have hdescent : baseEnd_819001 < baseStart_819001 := by decide
  rcases family_descends (prefixWord ++ tailWord_819001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819014 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_819014 : Nat := 118140960795 + 819014 * 2 ^ 59
def prefixEnd_819014 : Nat := 4983230072969 + 3 ^ 40 * 819014 * 2
def baseEnd_819014 : Nat := 280365229841042558438953

theorem tailTrace_819014 : CollatzResearch.WordTrace tailWord_819014 prefixEnd_819014 280365229841042558438953 := by
  unfold tailWord_819014
  simp only [CollatzResearch.WordTrace]
  refine ⟨933496707964363415630503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19914596436573086200117397 933496707964363415630503)
  ·
    refine ⟨1400245061946545123445755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 933496707964363415630503 1400245061946545123445755)
    ·
      refine ⟨2100367592919817685168633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1400245061946545123445755 2100367592919817685168633)
      ·
        refine ⟨1575275694689863263876475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2100367592919817685168633 1575275694689863263876475)
        ·
          refine ⟨2362913542034794895814713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1575275694689863263876475 2362913542034794895814713)
          ·
            refine ⟨1772185156526096171861035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2362913542034794895814713 1772185156526096171861035)
            ·
              refine ⟨2658277734789144257791553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772185156526096171861035 2658277734789144257791553)
              ·
                refine ⟨1993708301091858193343665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2658277734789144257791553 1993708301091858193343665)
                ·
                  refine ⟨1495281225818893645007749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1993708301091858193343665 1495281225818893645007749)
                  ·
                    refine ⟨280365229841042558438953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1495281225818893645007749 280365229841042558438953)
                    ·
                      rfl

theorem cell22_819014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_819014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819014 prefixEnd_819014 := by exact prefixLift 819014
  have htrace : WordTrace (prefixWord ++ tailWord_819014) baseStart_819014 baseEnd_819014 := by
    simpa [prefixWord, tailWord_819014, baseEnd_819014] using wordTrace_append hprefix tailTrace_819014
  have hstable : (prefixWord ++ tailWord_819014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819014).length < 2 ^ (prefixWord ++ tailWord_819014).sum := by decide
  have hdescent : baseEnd_819014 < baseStart_819014 := by decide
  rcases family_descends (prefixWord ++ tailWord_819014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819040 : List Nat := [2, 1, 1, 3, 3, 3, 1, 3, 5]
def baseStart_819040 : Nat := 118140960795 + 819040 * 2 ^ 59
def prefixEnd_819040 : Nat := 4983230072969 + 3 ^ 40 * 819040 * 2
def baseEnd_819040 : Nat := 93458043390795719096291

theorem tailTrace_819040 : CollatzResearch.WordTrace tailWord_819040 prefixEnd_819040 93458043390795719096291 := by
  unfold tailWord_819040
  simp only [CollatzResearch.WordTrace]
  refine ⟨14936421476382717870311287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19915228635176957160415049 14936421476382717870311287)
  ·
    refine ⟨22404632214574076805466931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14936421476382717870311287 22404632214574076805466931)
    ·
      refine ⟨33606948321861115208200397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22404632214574076805466931 33606948321861115208200397)
      ·
        refine ⟨12602605620697918203075149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33606948321861115208200397 12602605620697918203075149)
        ·
          refine ⟨4725977107761719326153181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12602605620697918203075149 4725977107761719326153181)
          ·
            refine ⟨1772241415410644747307443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4725977107761719326153181 1772241415410644747307443)
            ·
              refine ⟨2658362123115967120961165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772241415410644747307443 2658362123115967120961165)
              ·
                refine ⟨996885796168487670360437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2658362123115967120961165 996885796168487670360437)
                ·
                  refine ⟨93458043390795719096291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 996885796168487670360437 93458043390795719096291)
                  ·
                    rfl

theorem cell22_819040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 5].length) (baseStart_819040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819040 prefixEnd_819040 := by exact prefixLift 819040
  have htrace : WordTrace (prefixWord ++ tailWord_819040) baseStart_819040 baseEnd_819040 := by
    simpa [prefixWord, tailWord_819040, baseEnd_819040] using wordTrace_append hprefix tailTrace_819040
  have hstable : (prefixWord ++ tailWord_819040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819040).length < 2 ^ (prefixWord ++ tailWord_819040).sum := by decide
  have hdescent : baseEnd_819040 < baseStart_819040 := by decide
  rcases family_descends (prefixWord ++ tailWord_819040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819083 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 5, 5]
def baseStart_819083 : Nat := 118140960795 + 819083 * 2 ^ 59
def prefixEnd_819083 : Nat := 4983230072969 + 3 ^ 40 * 819083 * 2
def baseEnd_819083 : Nat := 280388849951149378463741

theorem tailTrace_819083 : CollatzResearch.WordTrace tailWord_819083 prefixEnd_819083 280388849951149378463741 := by
  unfold tailWord_819083
  simp only [CollatzResearch.WordTrace]
  refine ⟨29874411291609654084437903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19916274194406436056291935 29874411291609654084437903)
  ·
    refine ⟨44811616937414481126656855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29874411291609654084437903 44811616937414481126656855)
    ·
      refine ⟨67217425406121721689985283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44811616937414481126656855 67217425406121721689985283)
      ·
        refine ⟨100826138109182582534977925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67217425406121721689985283 100826138109182582534977925)
        ·
          refine ⟨18904900895471734225308361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100826138109182582534977925 18904900895471734225308361)
          ·
            refine ⟨14178675671603800668981271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18904900895471734225308361 14178675671603800668981271)
            ·
              refine ⟨21268013507405701003471907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14178675671603800668981271 21268013507405701003471907)
              ·
                refine ⟨31902020261108551505207861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21268013507405701003471907 31902020261108551505207861)
                ·
                  refine ⟨2990814399478926703613237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31902020261108551505207861 2990814399478926703613237)
                  ·
                    refine ⟨280388849951149378463741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2990814399478926703613237 280388849951149378463741)
                    ·
                      rfl

theorem cell22_819083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 5].length) (baseStart_819083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819083 prefixEnd_819083 := by exact prefixLift 819083
  have htrace : WordTrace (prefixWord ++ tailWord_819083) baseStart_819083 baseEnd_819083 := by
    simpa [prefixWord, tailWord_819083, baseEnd_819083] using wordTrace_append hprefix tailTrace_819083
  have hstable : (prefixWord ++ tailWord_819083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819083).length < 2 ^ (prefixWord ++ tailWord_819083).sum := by decide
  have hdescent : baseEnd_819083 < baseStart_819083 := by decide
  rcases family_descends (prefixWord ++ tailWord_819083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819134 : List Nat := [4, 2, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_819134 : Nat := 118140960795 + 819134 * 2 ^ 59
def prefixEnd_819134 : Nat := 4983230072969 + 3 ^ 40 * 819134 * 2
def baseEnd_819134 : Nat := 280406308293402245438585

theorem tailTrace_819134 : CollatzResearch.WordTrace tailWord_819134 prefixEnd_819134 280406308293402245438585 := by
  unfold tailWord_819134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3734533926803111224318057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19917514276283259863029637 3734533926803111224318057)
  ·
    refine ⟨2800900445102333418238543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3734533926803111224318057 2800900445102333418238543)
    ·
      refine ⟨4201350667653500127357815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2800900445102333418238543 4201350667653500127357815)
      ·
        refine ⟨6302026001480250191036723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4201350667653500127357815 6302026001480250191036723)
        ·
          refine ⟨9453039002220375286555085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6302026001480250191036723 9453039002220375286555085)
          ·
            refine ⟨3544889625832640732458157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9453039002220375286555085 3544889625832640732458157)
            ·
              refine ⟨1329333609687240274671809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3544889625832640732458157 1329333609687240274671809)
              ·
                refine ⟨997000207265430206003857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1329333609687240274671809 997000207265430206003857)
                ·
                  refine ⟨747750155449072654502893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 997000207265430206003857 747750155449072654502893)
                  ·
                    refine ⟨280406308293402245438585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 747750155449072654502893 280406308293402245438585)
                    ·
                      rfl

theorem cell22_819134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_819134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819134 prefixEnd_819134 := by exact prefixLift 819134
  have htrace : WordTrace (prefixWord ++ tailWord_819134) baseStart_819134 baseEnd_819134 := by
    simpa [prefixWord, tailWord_819134, baseEnd_819134] using wordTrace_append hprefix tailTrace_819134
  have hstable : (prefixWord ++ tailWord_819134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819134).length < 2 ^ (prefixWord ++ tailWord_819134).sum := by decide
  have hdescent : baseEnd_819134 < baseStart_819134 := by decide
  rcases family_descends (prefixWord ++ tailWord_819134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819145 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 7, 3]
def baseStart_819145 : Nat := 118140960795 + 819145 * 2 ^ 59
def prefixEnd_819145 : Nat := 4983230072969 + 3 ^ 40 * 819145 * 2
def baseEnd_819145 : Nat := 280410073818201883413551

theorem tailTrace_819145 : CollatzResearch.WordTrace tailWord_819145 prefixEnd_819145 280410073818201883413551 := by
  unfold tailWord_819145
  simp only [CollatzResearch.WordTrace]
  refine ⟨29876672617385038673194889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19917781744923359115463259 29876672617385038673194889)
  ·
    refine ⟨22407504463038779004896167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29876672617385038673194889 22407504463038779004896167)
    ·
      refine ⟨33611256694558168507344251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22407504463038779004896167 33611256694558168507344251)
      ·
        refine ⟨50416885041837252761016377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33611256694558168507344251 50416885041837252761016377)
        ·
          refine ⟨37812663781377939570762283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50416885041837252761016377 37812663781377939570762283)
          ·
            refine ⟨56718995672066909356143425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37812663781377939570762283 56718995672066909356143425)
            ·
              refine ⟨42539246754050182017107569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56718995672066909356143425 42539246754050182017107569)
              ·
                refine ⟨31904435065537636512830677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42539246754050182017107569 31904435065537636512830677)
                ·
                  refine ⟨747760196848538355769469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 31904435065537636512830677 747760196848538355769469)
                  ·
                    refine ⟨280410073818201883413551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 747760196848538355769469 280410073818201883413551)
                    ·
                      rfl

theorem cell22_819145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 3].length) (baseStart_819145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819145 prefixEnd_819145 := by exact prefixLift 819145
  have htrace : WordTrace (prefixWord ++ tailWord_819145) baseStart_819145 baseEnd_819145 := by
    simpa [prefixWord, tailWord_819145, baseEnd_819145] using wordTrace_append hprefix tailTrace_819145
  have hstable : (prefixWord ++ tailWord_819145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819145).length < 2 ^ (prefixWord ++ tailWord_819145).sum := by decide
  have hdescent : baseEnd_819145 < baseStart_819145 := by decide
  rcases family_descends (prefixWord ++ tailWord_819145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819196 : List Nat := [2, 2, 2, 1, 2, 2, 5, 2, 1, 3]
def baseStart_819196 : Nat := 118140960795 + 819196 * 2 ^ 59
def prefixEnd_819196 : Nat := 4983230072969 + 3 ^ 40 * 819196 * 2
def baseEnd_819196 : Nat := 280427532160454750388395

theorem tailTrace_819196 : CollatzResearch.WordTrace tailWord_819196 prefixEnd_819196 280427532160454750388395 := by
  unfold tailWord_819196
  simp only [CollatzResearch.WordTrace]
  refine ⟨14939266370100137191650721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19919021826800182922200961 14939266370100137191650721)
  ·
    refine ⟨11204449777575102893738041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14939266370100137191650721 11204449777575102893738041)
    ·
      refine ⟨8403337333181327170303531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11204449777575102893738041 8403337333181327170303531)
      ·
        refine ⟨12605005999771990755455297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8403337333181327170303531 12605005999771990755455297)
        ·
          refine ⟨9453754499828993066591473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12605005999771990755455297 9453754499828993066591473)
          ·
            refine ⟨7090315874871744799943605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9453754499828993066591473 7090315874871744799943605)
            ·
              refine ⟨664717113269226074994713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7090315874871744799943605 664717113269226074994713)
              ·
                refine ⟨498537834951919556246035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664717113269226074994713 498537834951919556246035)
                ·
                  refine ⟨747806752427879334369053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498537834951919556246035 747806752427879334369053)
                  ·
                    refine ⟨280427532160454750388395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 747806752427879334369053 280427532160454750388395)
                    ·
                      rfl

theorem cell22_819196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_819196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819196 prefixEnd_819196 := by exact prefixLift 819196
  have htrace : WordTrace (prefixWord ++ tailWord_819196) baseStart_819196 baseEnd_819196 := by
    simpa [prefixWord, tailWord_819196, baseEnd_819196] using wordTrace_append hprefix tailTrace_819196
  have hstable : (prefixWord ++ tailWord_819196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819196).length < 2 ^ (prefixWord ++ tailWord_819196).sum := by decide
  have hdescent : baseEnd_819196 < baseStart_819196 := by decide
  rcases family_descends (prefixWord ++ tailWord_819196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819286 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_819286 : Nat := 118140960795 + 819286 * 2 ^ 59
def prefixEnd_819286 : Nat := 4983230072969 + 3 ^ 40 * 819286 * 2
def baseEnd_819286 : Nat := 280458340999724515638119

theorem tailTrace_819286 : CollatzResearch.WordTrace tailWord_819286 prefixEnd_819286 280458340999724515638119 := by
  unfold tailWord_819286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1867613456867138734629857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19921210206582813169385141 1867613456867138734629857)
  ·
    refine ⟨1400710092650354050972393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1867613456867138734629857 1400710092650354050972393)
    ·
      refine ⟨1050532569487765538229295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1400710092650354050972393 1050532569487765538229295)
      ·
        refine ⟨1575798854231648307343943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050532569487765538229295 1575798854231648307343943)
        ·
          refine ⟨2363698281347472461015915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1575798854231648307343943 2363698281347472461015915)
          ·
            refine ⟨3545547422021208691523873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2363698281347472461015915 3545547422021208691523873)
            ·
              refine ⟨2659160566515906518642905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3545547422021208691523873 2659160566515906518642905)
              ·
                refine ⟨1994370424886929888982179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2659160566515906518642905 1994370424886929888982179)
                ·
                  refine ⟨2991555637330394833473269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994370424886929888982179 2991555637330394833473269)
                  ·
                    refine ⟨280458340999724515638119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2991555637330394833473269 280458340999724515638119)
                    ·
                      rfl

theorem cell22_819286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_819286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819286 prefixEnd_819286 := by exact prefixLift 819286
  have htrace : WordTrace (prefixWord ++ tailWord_819286) baseStart_819286 baseEnd_819286 := by
    simpa [prefixWord, tailWord_819286, baseEnd_819286] using wordTrace_append hprefix tailTrace_819286
  have hstable : (prefixWord ++ tailWord_819286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819286).length < 2 ^ (prefixWord ++ tailWord_819286).sum := by decide
  have hdescent : baseEnd_819286 < baseStart_819286 := by decide
  rcases family_descends (prefixWord ++ tailWord_819286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819295 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 1, 8]
def baseStart_819295 : Nat := 118140960795 + 819295 * 2 ^ 59
def prefixEnd_819295 : Nat := 4983230072969 + 3 ^ 40 * 819295 * 2
def baseEnd_819295 : Nat := 280461421883651492163091

theorem tailTrace_819295 : CollatzResearch.WordTrace tailWord_819295 prefixEnd_819295 280461421883651492163091 := by
  unfold tailWord_819295
  simp only [CollatzResearch.WordTrace]
  refine ⟨29882143566841614291155339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19921429044561076194103559 29882143566841614291155339)
  ·
    refine ⟨44823215350262421436733009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29882143566841614291155339 44823215350262421436733009)
    ·
      refine ⟨33617411512696816077549757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44823215350262421436733009 33617411512696816077549757)
      ·
        refine ⟨12606529317261306029081159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33617411512696816077549757 12606529317261306029081159)
        ·
          refine ⟨18909793975891959043621739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12606529317261306029081159 18909793975891959043621739)
          ·
            refine ⟨28364690963837938565432609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18909793975891959043621739 28364690963837938565432609)
            ·
              refine ⟨21273518222878453924074457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28364690963837938565432609 21273518222878453924074457)
              ·
                refine ⟨15955138667158840443055843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21273518222878453924074457 15955138667158840443055843)
                ·
                  refine ⟨23932708000738260664583765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15955138667158840443055843 23932708000738260664583765)
                  ·
                    refine ⟨280461421883651492163091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23932708000738260664583765 280461421883651492163091)
                    ·
                      rfl

theorem cell22_819295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_819295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819295 prefixEnd_819295 := by exact prefixLift 819295
  have htrace : WordTrace (prefixWord ++ tailWord_819295) baseStart_819295 baseEnd_819295 := by
    simpa [prefixWord, tailWord_819295, baseEnd_819295] using wordTrace_append hprefix tailTrace_819295
  have hstable : (prefixWord ++ tailWord_819295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819295).length < 2 ^ (prefixWord ++ tailWord_819295).sum := by decide
  have hdescent : baseEnd_819295 < baseStart_819295 := by decide
  rcases family_descends (prefixWord ++ tailWord_819295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819297 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 7, 3]
def baseStart_819297 : Nat := 118140960795 + 819297 * 2 ^ 59
def prefixEnd_819297 : Nat := 4983230072969 + 3 ^ 40 * 819297 * 2
def baseEnd_819297 : Nat := 280462106524524153613085

theorem tailTrace_819297 : CollatzResearch.WordTrace tailWord_819297 prefixEnd_819297 280462106524524153613085 := by
  unfold tailWord_819297
  simp only [CollatzResearch.WordTrace]
  refine ⟨29882216512834368632728145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19921477675222912421818763 29882216512834368632728145)
  ·
    refine ⟨22411662384625776474546109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29882216512834368632728145 22411662384625776474546109)
    ·
      refine ⟨8404373394234666177954791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22411662384625776474546109 8404373394234666177954791)
      ·
        refine ⟨12606560091351999266932187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8404373394234666177954791 12606560091351999266932187)
        ·
          refine ⟨18909840137027998900398281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12606560091351999266932187 18909840137027998900398281)
          ·
            refine ⟨14182380102770999175298711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18909840137027998900398281 14182380102770999175298711)
            ·
              refine ⟨21273570154156498762948067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14182380102770999175298711 21273570154156498762948067)
              ·
                refine ⟨31910355231234748144422101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21273570154156498762948067 31910355231234748144422101)
                ·
                  refine ⟨747898950732064409634893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 31910355231234748144422101 747898950732064409634893)
                  ·
                    refine ⟨280462106524524153613085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 747898950732064409634893 280462106524524153613085)
                    ·
                      rfl

theorem cell22_819297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_819297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819297 prefixEnd_819297 := by exact prefixLift 819297
  have htrace : WordTrace (prefixWord ++ tailWord_819297) baseStart_819297 baseEnd_819297 := by
    simpa [prefixWord, tailWord_819297, baseEnd_819297] using wordTrace_append hprefix tailTrace_819297
  have hstable : (prefixWord ++ tailWord_819297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819297).length < 2 ^ (prefixWord ++ tailWord_819297).sum := by decide
  have hdescent : baseEnd_819297 < baseStart_819297 := by decide
  rcases family_descends (prefixWord ++ tailWord_819297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819314 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_819314 : Nat := 118140960795 + 819314 * 2 ^ 59
def prefixEnd_819314 : Nat := 4983230072969 + 3 ^ 40 * 819314 * 2
def baseEnd_819314 : Nat := 280467925971941775938033

theorem tailTrace_819314 : CollatzResearch.WordTrace tailWord_819314 prefixEnd_819314 280467925971941775938033 := by
  unfold tailWord_819314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7470709138443195134024249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19921891035848520357397997 7470709138443195134024249)
  ·
    refine ⟨5603031853832396350518187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7470709138443195134024249 5603031853832396350518187)
    ·
      refine ⟨8404547780748594525777281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5603031853832396350518187 8404547780748594525777281)
      ·
        refine ⟨6303410835561445894332961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8404547780748594525777281 6303410835561445894332961)
        ·
          refine ⟨4727558126671084420749721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6303410835561445894332961 4727558126671084420749721)
          ·
            refine ⟨3545668595003313315562291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4727558126671084420749721 3545668595003313315562291)
            ·
              refine ⟨5318502892504969973343437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3545668595003313315562291 5318502892504969973343437)
              ·
                refine ⟨1994438584689363740003789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5318502892504969973343437 1994438584689363740003789)
                ·
                  refine ⟨747914469258511402501421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1994438584689363740003789 747914469258511402501421)
                  ·
                    refine ⟨280467925971941775938033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 747914469258511402501421 280467925971941775938033)
                    ·
                      rfl

theorem cell22_819314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_819314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819314 prefixEnd_819314 := by exact prefixLift 819314
  have htrace : WordTrace (prefixWord ++ tailWord_819314) baseStart_819314 baseEnd_819314 := by
    simpa [prefixWord, tailWord_819314, baseEnd_819314] using wordTrace_append hprefix tailTrace_819314
  have hstable : (prefixWord ++ tailWord_819314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819314).length < 2 ^ (prefixWord ++ tailWord_819314).sum := by decide
  have hdescent : baseEnd_819314 < baseStart_819314 := by decide
  rcases family_descends (prefixWord ++ tailWord_819314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819350 : List Nat := [5, 3, 2, 1, 1, 2, 8]
def baseStart_819350 : Nat := 118140960795 + 819350 * 2 ^ 59
def prefixEnd_819350 : Nat := 4983230072969 + 3 ^ 40 * 819350 * 2
def baseEnd_819350 : Nat := 10388157389172210445849

theorem tailTrace_819350 : CollatzResearch.WordTrace tailWord_819350 prefixEnd_819350 10388157389172210445849 := by
  unfold tailWord_819350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1867759348852647417775469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19922766387761572456271669 1867759348852647417775469)
  ·
    refine ⟨700409755819742781665801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1867759348852647417775469 700409755819742781665801)
    ·
      refine ⟨525307316864807086249351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 700409755819742781665801 525307316864807086249351)
      ·
        refine ⟨787960975297210629374027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525307316864807086249351 787960975297210629374027)
        ·
          refine ⟨1181941462945815944061041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787960975297210629374027 1181941462945815944061041)
          ·
            refine ⟨886456097209361958045781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1181941462945815944061041 886456097209361958045781)
            ·
              refine ⟨10388157389172210445849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 886456097209361958045781 10388157389172210445849)
              ·
                rfl

theorem cell22_819350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 8].length) (baseStart_819350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819350 prefixEnd_819350 := by exact prefixLift 819350
  have htrace : WordTrace (prefixWord ++ tailWord_819350) baseStart_819350 baseEnd_819350 := by
    simpa [prefixWord, tailWord_819350, baseEnd_819350] using wordTrace_append hprefix tailTrace_819350
  have hstable : (prefixWord ++ tailWord_819350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819350).length < 2 ^ (prefixWord ++ tailWord_819350).sum := by decide
  have hdescent : baseEnd_819350 < baseStart_819350 := by decide
  rcases family_descends (prefixWord ++ tailWord_819350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819387 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 1, 5]
def baseStart_819387 : Nat := 118140960795 + 819387 * 2 ^ 59
def prefixEnd_819387 : Nat := 4983230072969 + 3 ^ 40 * 819387 * 2
def baseEnd_819387 : Nat := 280492915363793918862809

theorem tailTrace_819387 : CollatzResearch.WordTrace tailWord_819387 prefixEnd_819387 280492915363793918862809 := by
  unfold tailWord_819387
  simp only [CollatzResearch.WordTrace]
  refine ⟨29885499082508314003504415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19923666055005542669002943 29885499082508314003504415)
  ·
    refine ⟨44828248623762471005256623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29885499082508314003504415 44828248623762471005256623)
    ·
      refine ⟨67242372935643706507884935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44828248623762471005256623 67242372935643706507884935)
      ·
        refine ⟨100863559403465559761827403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67242372935643706507884935 100863559403465559761827403)
        ·
          refine ⟨151295339105198339642741105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100863559403465559761827403 151295339105198339642741105)
          ·
            refine ⟨113471504328898754732055829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151295339105198339642741105 113471504328898754732055829)
            ·
              refine ⟨5318976765417129128065117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113471504328898754732055829 5318976765417129128065117)
              ·
                refine ⟨1994616287031423423024419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5318976765417129128065117 1994616287031423423024419)
                ·
                  refine ⟨2991924430547135134536629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994616287031423423024419 2991924430547135134536629)
                  ·
                    refine ⟨280492915363793918862809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2991924430547135134536629 280492915363793918862809)
                    ·
                      rfl

theorem cell22_819387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 5].length) (baseStart_819387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819387 prefixEnd_819387 := by exact prefixLift 819387
  have htrace : WordTrace (prefixWord ++ tailWord_819387) baseStart_819387 baseEnd_819387 := by
    simpa [prefixWord, tailWord_819387, baseEnd_819387] using wordTrace_append hprefix tailTrace_819387
  have hstable : (prefixWord ++ tailWord_819387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819387).length < 2 ^ (prefixWord ++ tailWord_819387).sum := by decide
  have hdescent : baseEnd_819387 < baseStart_819387 := by decide
  rcases family_descends (prefixWord ++ tailWord_819387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819479 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 7]
def baseStart_819479 : Nat := 118140960795 + 819479 * 2 ^ 59
def prefixEnd_819479 : Nat := 4983230072969 + 3 ^ 40 * 819479 * 2
def baseEnd_819479 : Nat := 93508136281312115187509

theorem tailTrace_819479 : CollatzResearch.WordTrace tailWord_819479 prefixEnd_819479 93508136281312115187509 := by
  unfold tailWord_819479
  simp only [CollatzResearch.WordTrace]
  refine ⟨29888854598175013715853491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19925903065450009143902327 29888854598175013715853491)
  ·
    refine ⟨44833281897262520573780237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29888854598175013715853491 44833281897262520573780237)
    ·
      refine ⟨16812480711473445215167589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44833281897262520573780237 16812480711473445215167589)
      ·
        refine ⟨3152340133401270977843923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16812480711473445215167589 3152340133401270977843923)
        ·
          refine ⟨4728510200101906466765885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152340133401270977843923 4728510200101906466765885)
          ·
            refine ⟨1773191325038214925037207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4728510200101906466765885 1773191325038214925037207)
            ·
              refine ⟨2659786987557322387555811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773191325038214925037207 2659786987557322387555811)
              ·
                refine ⟨3989680481335983581333717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659786987557322387555811 3989680481335983581333717)
                ·
                  refine ⟨93508136281312115187509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3989680481335983581333717 93508136281312115187509)
                  ·
                    rfl

theorem cell22_819479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 7].length) (baseStart_819479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819479 prefixEnd_819479 := by exact prefixLift 819479
  have htrace : WordTrace (prefixWord ++ tailWord_819479) baseStart_819479 baseEnd_819479 := by
    simpa [prefixWord, tailWord_819479, baseEnd_819479] using wordTrace_append hprefix tailTrace_819479
  have hstable : (prefixWord ++ tailWord_819479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819479).length < 2 ^ (prefixWord ++ tailWord_819479).sum := by decide
  have hdescent : baseEnd_819479 < baseStart_819479 := by decide
  rcases family_descends (prefixWord ++ tailWord_819479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819586 : List Nat := [3, 4, 2, 1, 12]
def baseStart_819586 : Nat := 118140960795 + 819586 * 2 ^ 59
def prefixEnd_819586 : Nat := 4983230072969 + 3 ^ 40 * 819586 * 2
def baseEnd_819586 : Nat := 1154572169261826062293

theorem tailTrace_819586 : CollatzResearch.WordTrace tailWord_819586 prefixEnd_819586 1154572169261826062293 := by
  unfold tailWord_819586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7473189302196842747499653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19928504805858247326665741 7473189302196842747499653)
  ·
    refine ⟨1401222994161908015156185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7473189302196842747499653 1401222994161908015156185)
    ·
      refine ⟨1050917245621431011367139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1401222994161908015156185 1050917245621431011367139)
      ·
        refine ⟨1576375868432146517050709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050917245621431011367139 1576375868432146517050709)
        ·
          refine ⟨1154572169261826062293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1576375868432146517050709 1154572169261826062293)
          ·
            rfl

theorem cell22_819586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 12].length) (baseStart_819586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819586 prefixEnd_819586 := by exact prefixLift 819586
  have htrace : WordTrace (prefixWord ++ tailWord_819586) baseStart_819586 baseEnd_819586 := by
    simpa [prefixWord, tailWord_819586, baseEnd_819586] using wordTrace_append hprefix tailTrace_819586
  have hstable : (prefixWord ++ tailWord_819586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819586).length < 2 ^ (prefixWord ++ tailWord_819586).sum := by decide
  have hdescent : baseEnd_819586 < baseStart_819586 := by decide
  rcases family_descends (prefixWord ++ tailWord_819586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819618 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_819618 : Nat := 118140960795 + 819618 * 2 ^ 59
def prefixEnd_819618 : Nat := 4983230072969 + 3 ^ 40 * 819618 * 2
def baseEnd_819618 : Nat := 280571991384586316337101

theorem tailTrace_819618 : CollatzResearch.WordTrace tailWord_819618 prefixEnd_819618 280571991384586316337101 := by
  unfold tailWord_819618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7473481086167860113790877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19929282896447626970109005 7473481086167860113790877)
  ·
    refine ⟨2802555407312947542671579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7473481086167860113790877 2802555407312947542671579)
    ·
      refine ⟨4203833110969421314007369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2802555407312947542671579 4203833110969421314007369)
      ·
        refine ⟨3152874833227065985505527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4203833110969421314007369 3152874833227065985505527)
        ·
          refine ⟨4729312249840598978258291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152874833227065985505527 4729312249840598978258291)
          ·
            refine ⟨7093968374760898467387437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4729312249840598978258291 7093968374760898467387437)
            ·
              refine ⟨2660238140535336925270289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7093968374760898467387437 2660238140535336925270289)
              ·
                refine ⟨1995178605401502693952717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2660238140535336925270289 1995178605401502693952717)
                ·
                  refine ⟨748191977025563510232269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1995178605401502693952717 748191977025563510232269)
                  ·
                    refine ⟨280571991384586316337101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 748191977025563510232269 280571991384586316337101)
                    ·
                      rfl

theorem cell22_819618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_819618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819618 prefixEnd_819618 := by exact prefixLift 819618
  have htrace : WordTrace (prefixWord ++ tailWord_819618) baseStart_819618 baseEnd_819618 := by
    simpa [prefixWord, tailWord_819618, baseEnd_819618] using wordTrace_append hprefix tailTrace_819618
  have hstable : (prefixWord ++ tailWord_819618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819618).length < 2 ^ (prefixWord ++ tailWord_819618).sum := by decide
  have hdescent : baseEnd_819618 < baseStart_819618 := by decide
  rcases family_descends (prefixWord ++ tailWord_819618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819646 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_819646 : Nat := 118140960795 + 819646 * 2 ^ 59
def prefixEnd_819646 : Nat := 4983230072969 + 3 ^ 40 * 819646 * 2
def baseEnd_819646 : Nat := 280581576356803576637015

theorem tailTrace_819646 : CollatzResearch.WordTrace tailWord_819646 prefixEnd_819646 280581576356803576637015 := by
  unfold tailWord_819646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3736868198571250154647849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19929963725713334158121861 3736868198571250154647849)
  ·
    refine ⟨2802651148928437615985887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3736868198571250154647849 2802651148928437615985887)
    ·
      refine ⟨4203976723392656423978831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2802651148928437615985887 4203976723392656423978831)
      ·
        refine ⟨6305965085088984635968247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4203976723392656423978831 6305965085088984635968247)
        ·
          refine ⟨9458947627633476953952371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6305965085088984635968247 9458947627633476953952371)
          ·
            refine ⟨14188421441450215430928557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9458947627633476953952371 14188421441450215430928557)
            ·
              refine ⟨5320658040543830786598209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14188421441450215430928557 5320658040543830786598209)
              ·
                refine ⟨3990493530407873089948657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5320658040543830786598209 3990493530407873089948657)
                ·
                  refine ⟨2992870147805904817461493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3990493530407873089948657 2992870147805904817461493)
                  ·
                    refine ⟨280581576356803576637015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2992870147805904817461493 280581576356803576637015)
                    ·
                      rfl

theorem cell22_819646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_819646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819646 prefixEnd_819646 := by exact prefixLift 819646
  have htrace : WordTrace (prefixWord ++ tailWord_819646) baseStart_819646 baseEnd_819646 := by
    simpa [prefixWord, tailWord_819646, baseEnd_819646] using wordTrace_append hprefix tailTrace_819646
  have hstable : (prefixWord ++ tailWord_819646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819646).length < 2 ^ (prefixWord ++ tailWord_819646).sum := by decide
  have hdescent : baseEnd_819646 < baseStart_819646 := by decide
  rcases family_descends (prefixWord ++ tailWord_819646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819691 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 6, 3]
def baseStart_819691 : Nat := 118140960795 + 819691 * 2 ^ 59
def prefixEnd_819691 : Nat := 4983230072969 + 3 ^ 40 * 819691 * 2
def baseEnd_819691 : Nat := 280596980776438459261877

theorem tailTrace_819691 : CollatzResearch.WordTrace tailWord_819691 prefixEnd_819691 280596980776438459261877 := by
  unfold tailWord_819691
  simp only [CollatzResearch.WordTrace]
  refine ⟨29896586873406973922570927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19931057915604649281713951 29896586873406973922570927)
  ·
    refine ⟨44844880310110460883856391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29896586873406973922570927 44844880310110460883856391)
    ·
      refine ⟨67267320465165691325784587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44844880310110460883856391 67267320465165691325784587)
      ·
        refine ⟨100900980697748536988676881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67267320465165691325784587 100900980697748536988676881)
        ·
          refine ⟨75675735523311402741507661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100900980697748536988676881 75675735523311402741507661)
          ·
            refine ⟨28378400821241776028065373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75675735523311402741507661 28378400821241776028065373)
            ·
              refine ⟨10641900307965666010524515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28378400821241776028065373 10641900307965666010524515)
              ·
                refine ⟨15962850461948499015786773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10641900307965666010524515 15962850461948499015786773)
                ·
                  refine ⟨748258615403835891365005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15962850461948499015786773 748258615403835891365005)
                  ·
                    refine ⟨280596980776438459261877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 748258615403835891365005 280596980776438459261877)
                    ·
                      rfl

theorem cell22_819691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 3].length) (baseStart_819691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819691 prefixEnd_819691 := by exact prefixLift 819691
  have htrace : WordTrace (prefixWord ++ tailWord_819691) baseStart_819691 baseEnd_819691 := by
    simpa [prefixWord, tailWord_819691, baseEnd_819691] using wordTrace_append hprefix tailTrace_819691
  have hstable : (prefixWord ++ tailWord_819691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819691).length < 2 ^ (prefixWord ++ tailWord_819691).sum := by decide
  have hdescent : baseEnd_819691 < baseStart_819691 := by decide
  rcases family_descends (prefixWord ++ tailWord_819691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819708 : List Nat := [2, 2, 2, 1, 2, 1, 1, 6, 2, 3]
def baseStart_819708 : Nat := 118140960795 + 819708 * 2 ^ 59
def prefixEnd_819708 : Nat := 4983230072969 + 3 ^ 40 * 819708 * 2
def baseEnd_819708 : Nat := 280602800223856081586825

theorem tailTrace_819708 : CollatzResearch.WordTrace tailWord_819708 prefixEnd_819708 280602800223856081586825 := by
  unfold tailWord_819708
  simp only [CollatzResearch.WordTrace]
  refine ⟨14948603457172692912969889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19931471276230257217293185 14948603457172692912969889)
  ·
    refine ⟨11211452592879519684727417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14948603457172692912969889 11211452592879519684727417)
    ·
      refine ⟨8408589444659639763545563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11211452592879519684727417 8408589444659639763545563)
      ·
        refine ⟨12612884166989459645318345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8408589444659639763545563 12612884166989459645318345)
        ·
          refine ⟨9459663125242094733988759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12612884166989459645318345 9459663125242094733988759)
          ·
            refine ⟨14189494687863142100983139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9459663125242094733988759 14189494687863142100983139)
            ·
              refine ⟨21284242031794713151474709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14189494687863142100983139 21284242031794713151474709)
              ·
                refine ⟨997698845240377178975377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21284242031794713151474709 997698845240377178975377)
                ·
                  refine ⟨748274133930282884231533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 997698845240377178975377 748274133930282884231533)
                  ·
                    refine ⟨280602800223856081586825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 748274133930282884231533 280602800223856081586825)
                    ·
                      rfl

theorem cell22_819708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_819708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819708 prefixEnd_819708 := by exact prefixLift 819708
  have htrace : WordTrace (prefixWord ++ tailWord_819708) baseStart_819708 baseEnd_819708 := by
    simpa [prefixWord, tailWord_819708, baseEnd_819708] using wordTrace_append hprefix tailTrace_819708
  have hstable : (prefixWord ++ tailWord_819708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819708).length < 2 ^ (prefixWord ++ tailWord_819708).sum := by decide
  have hdescent : baseEnd_819708 < baseStart_819708 := by decide
  rcases family_descends (prefixWord ++ tailWord_819708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819781 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_819781 : Nat := 118140960795 + 819781 * 2 ^ 59
def prefixEnd_819781 : Nat := 4983230072969 + 3 ^ 40 * 819781 * 2
def baseEnd_819781 : Nat := 280627789615708224511601

theorem tailTrace_819781 : CollatzResearch.WordTrace tailWord_819781 prefixEnd_819781 280627789615708224511601 := by
  unfold tailWord_819781
  simp only [CollatzResearch.WordTrace]
  refine ⟨29899869443080919293347197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19933246295387279528898131 29899869443080919293347197)
  ·
    refine ⟨11212451041155344735005199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29899869443080919293347197 11212451041155344735005199)
    ·
      refine ⟨16818676561733017102507799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11212451041155344735005199 16818676561733017102507799)
      ·
        refine ⟨25228014842599525653761699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16818676561733017102507799 25228014842599525653761699)
        ·
          refine ⟨37842022263899288480642549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25228014842599525653761699 37842022263899288480642549)
          ·
            refine ⟨3547689587240558295060239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37842022263899288480642549 3547689587240558295060239)
            ·
              refine ⟨5321534380860837442590359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3547689587240558295060239 5321534380860837442590359)
              ·
                refine ⟨7982301571291256163885539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5321534380860837442590359 7982301571291256163885539)
                ·
                  refine ⟨11973452356936884245828309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7982301571291256163885539 11973452356936884245828309)
                  ·
                    refine ⟨280627789615708224511601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11973452356936884245828309 280627789615708224511601)
                    ·
                      rfl

theorem cell22_819781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_819781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819781 prefixEnd_819781 := by exact prefixLift 819781
  have htrace : WordTrace (prefixWord ++ tailWord_819781) baseStart_819781 baseEnd_819781 := by
    simpa [prefixWord, tailWord_819781, baseEnd_819781] using wordTrace_append hprefix tailTrace_819781
  have hstable : (prefixWord ++ tailWord_819781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819781).length < 2 ^ (prefixWord ++ tailWord_819781).sum := by decide
  have hdescent : baseEnd_819781 < baseStart_819781 := by decide
  rcases family_descends (prefixWord ++ tailWord_819781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819783 : List Nat := [1, 1, 4, 1, 4, 1, 2, 3, 5]
def baseStart_819783 : Nat := 118140960795 + 819783 * 2 ^ 59
def prefixEnd_819783 : Nat := 4983230072969 + 3 ^ 40 * 819783 * 2
def baseEnd_819783 : Nat := 93542824752193628653865

theorem tailTrace_819783 : CollatzResearch.WordTrace tailWord_819783 prefixEnd_819783 93542824752193628653865 := by
  unfold tailWord_819783
  simp only [CollatzResearch.WordTrace]
  refine ⟨29899942389073673634920003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19933294926049115756613335 29899942389073673634920003)
  ·
    refine ⟨44849913583610510452380005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29899942389073673634920003 44849913583610510452380005)
    ·
      refine ⟨8409358796926970709821251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44849913583610510452380005 8409358796926970709821251)
      ·
        refine ⟨12614038195390456064731877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8409358796926970709821251 12614038195390456064731877)
        ·
          refine ⟨2365132161635710512137227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12614038195390456064731877 2365132161635710512137227)
          ·
            refine ⟨3547698242453565768205841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365132161635710512137227 3547698242453565768205841)
            ·
              refine ⟨2660773681840174326154381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3547698242453565768205841 2660773681840174326154381)
              ·
                refine ⟨997790130690065372307893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2660773681840174326154381 997790130690065372307893)
                ·
                  refine ⟨93542824752193628653865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 997790130690065372307893 93542824752193628653865)
                  ·
                    rfl

theorem cell22_819783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 5].length) (baseStart_819783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819783 prefixEnd_819783 := by exact prefixLift 819783
  have htrace : WordTrace (prefixWord ++ tailWord_819783) baseStart_819783 baseEnd_819783 := by
    simpa [prefixWord, tailWord_819783, baseEnd_819783] using wordTrace_append hprefix tailTrace_819783
  have hstable : (prefixWord ++ tailWord_819783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819783).length < 2 ^ (prefixWord ++ tailWord_819783).sum := by decide
  have hdescent : baseEnd_819783 < baseStart_819783 := by decide
  rcases family_descends (prefixWord ++ tailWord_819783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819804 : List Nat := [2, 2, 4, 1, 3, 1, 2, 3, 1, 3]
def baseStart_819804 : Nat := 118140960795 + 819804 * 2 ^ 59
def prefixEnd_819804 : Nat := 4983230072969 + 3 ^ 40 * 819804 * 2
def baseEnd_819804 : Nat := 280635662985743831186531

theorem tailTrace_819804 : CollatzResearch.WordTrace tailWord_819804 prefixEnd_819804 280635662985743831186531 := by
  unfold tailWord_819804
  simp only [CollatzResearch.WordTrace]
  refine ⟨14950354160998797110717233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19933805547998396147622977 14950354160998797110717233)
  ·
    refine ⟨11212765620749097833037925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14950354160998797110717233 11212765620749097833037925)
    ·
      refine ⟨2102393553890455843694611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11212765620749097833037925 2102393553890455843694611)
      ·
        refine ⟨3153590330835683765541917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102393553890455843694611 3153590330835683765541917)
        ·
          refine ⟨1182596374063381412078219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3153590330835683765541917 1182596374063381412078219)
          ·
            refine ⟨1773894561095072118117329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182596374063381412078219 1773894561095072118117329)
            ·
              refine ⟨1330420920821304088587997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1773894561095072118117329 1330420920821304088587997)
              ·
                refine ⟨498907845307989033220499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1330420920821304088587997 498907845307989033220499)
                ·
                  refine ⟨748361767961983549830749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498907845307989033220499 748361767961983549830749)
                  ·
                    refine ⟨280635662985743831186531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 748361767961983549830749 280635662985743831186531)
                    ·
                      rfl

theorem cell22_819804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_819804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819804 prefixEnd_819804 := by exact prefixLift 819804
  have htrace : WordTrace (prefixWord ++ tailWord_819804) baseStart_819804 baseEnd_819804 := by
    simpa [prefixWord, tailWord_819804, baseEnd_819804] using wordTrace_append hprefix tailTrace_819804
  have hstable : (prefixWord ++ tailWord_819804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819804).length < 2 ^ (prefixWord ++ tailWord_819804).sum := by decide
  have hdescent : baseEnd_819804 < baseStart_819804 := by decide
  rcases family_descends (prefixWord ++ tailWord_819804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819811 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 8]
def baseStart_819811 : Nat := 118140960795 + 819811 * 2 ^ 59
def prefixEnd_819811 : Nat := 4983230072969 + 3 ^ 40 * 819811 * 2
def baseEnd_819811 : Nat := 93546019742932715420503

theorem tailTrace_819811 : CollatzResearch.WordTrace tailWord_819811 prefixEnd_819811 93546019742932715420503 := by
  unfold tailWord_819811
  simp only [CollatzResearch.WordTrace]
  refine ⟨29900963632972234416939287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19933975755314822944626191 29900963632972234416939287)
  ·
    refine ⟨44851445449458351625408931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29900963632972234416939287 44851445449458351625408931)
    ·
      refine ⟨67277168174187527438113397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44851445449458351625408931 67277168174187527438113397)
      ·
        refine ⟨6307234516330080697323131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67277168174187527438113397 6307234516330080697323131)
        ·
          refine ⟨9460851774495121045984697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6307234516330080697323131 9460851774495121045984697)
          ·
            refine ⟨7095638830871340784488523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9460851774495121045984697 7095638830871340784488523)
            ·
              refine ⟨10643458246307011176732785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7095638830871340784488523 10643458246307011176732785)
              ·
                refine ⟨7982593684730258382549589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10643458246307011176732785 7982593684730258382549589)
                ·
                  refine ⟨93546019742932715420503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7982593684730258382549589 93546019742932715420503)
                  ·
                    rfl

theorem cell22_819811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 8].length) (baseStart_819811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819811 prefixEnd_819811 := by exact prefixLift 819811
  have htrace : WordTrace (prefixWord ++ tailWord_819811) baseStart_819811 baseEnd_819811 := by
    simpa [prefixWord, tailWord_819811, baseEnd_819811] using wordTrace_append hprefix tailTrace_819811
  have hstable : (prefixWord ++ tailWord_819811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819811).length < 2 ^ (prefixWord ++ tailWord_819811).sum := by decide
  have hdescent : baseEnd_819811 < baseStart_819811 := by decide
  rcases family_descends (prefixWord ++ tailWord_819811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819843 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 1, 5]
def baseStart_819843 : Nat := 118140960795 + 819843 * 2 ^ 59
def prefixEnd_819843 : Nat := 4983230072969 + 3 ^ 40 * 819843 * 2
def baseEnd_819843 : Nat := 280649013482760729461411

theorem tailTrace_819843 : CollatzResearch.WordTrace tailWord_819843 prefixEnd_819843 280649013482760729461411 := by
  unfold tailWord_819843
  simp only [CollatzResearch.WordTrace]
  refine ⟨29902130768856303882104183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19934753845904202588069455 29902130768856303882104183)
  ·
    refine ⟨44853196153284455823156275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29902130768856303882104183 44853196153284455823156275)
    ·
      refine ⟨67279794229926683734734413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44853196153284455823156275 67279794229926683734734413)
      ·
        refine ⟨25229922836222506400525405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67279794229926683734734413 25229922836222506400525405)
        ·
          refine ⟨9461221063583439900197027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25229922836222506400525405 9461221063583439900197027)
          ·
            refine ⟨14191831595375159850295541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9461221063583439900197027 14191831595375159850295541)
            ·
              refine ⟨1330484212066421235965207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14191831595375159850295541 1330484212066421235965207)
              ·
                refine ⟨1995726318099631853947811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330484212066421235965207 1995726318099631853947811)
                ·
                  refine ⟨2993589477149447780921717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995726318099631853947811 2993589477149447780921717)
                  ·
                    refine ⟨280649013482760729461411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2993589477149447780921717 280649013482760729461411)
                    ·
                      rfl

theorem cell22_819843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 5].length) (baseStart_819843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819843 prefixEnd_819843 := by exact prefixLift 819843
  have htrace : WordTrace (prefixWord ++ tailWord_819843) baseStart_819843 baseEnd_819843 := by
    simpa [prefixWord, tailWord_819843, baseEnd_819843] using wordTrace_append hprefix tailTrace_819843
  have hstable : (prefixWord ++ tailWord_819843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819843).length < 2 ^ (prefixWord ++ tailWord_819843).sum := by decide
  have hdescent : baseEnd_819843 < baseStart_819843 := by decide
  rcases family_descends (prefixWord ++ tailWord_819843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819879 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 6]
def baseStart_819879 : Nat := 118140960795 + 819879 * 2 ^ 59
def prefixEnd_819879 : Nat := 4983230072969 + 3 ^ 40 * 819879 * 2
def baseEnd_819879 : Nat := 93553779006156211853767

theorem tailTrace_819879 : CollatzResearch.WordTrace tailWord_819879 prefixEnd_819879 93553779006156211853767 := by
  unfold tailWord_819879
  simp only [CollatzResearch.WordTrace]
  refine ⟨29903443796725882030414691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19935629197817254686943127 29903443796725882030414691)
  ·
    refine ⟨44855165695088823045622037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29903443796725882030414691 44855165695088823045622037)
    ·
      refine ⟨2102585891957288580263533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44855165695088823045622037 2102585891957288580263533)
      ·
        refine ⟨788469709483983217598825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2102585891957288580263533 788469709483983217598825)
        ·
          refine ⟨591352282112987413199119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 788469709483983217598825 591352282112987413199119)
          ·
            refine ⟨887028423169481119798679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591352282112987413199119 887028423169481119798679)
            ·
              refine ⟨1330542634754221679698019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887028423169481119798679 1330542634754221679698019)
              ·
                refine ⟨1995813952131332519547029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330542634754221679698019 1995813952131332519547029)
                ·
                  refine ⟨93553779006156211853767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1995813952131332519547029 93553779006156211853767)
                  ·
                    rfl

theorem cell22_819879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 6].length) (baseStart_819879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819879 prefixEnd_819879 := by exact prefixLift 819879
  have htrace : WordTrace (prefixWord ++ tailWord_819879) baseStart_819879 baseEnd_819879 := by
    simpa [prefixWord, tailWord_819879, baseEnd_819879] using wordTrace_append hprefix tailTrace_819879
  have hstable : (prefixWord ++ tailWord_819879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819879).length < 2 ^ (prefixWord ++ tailWord_819879).sum := by decide
  have hdescent : baseEnd_819879 < baseStart_819879 := by decide
  rcases family_descends (prefixWord ++ tailWord_819879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819935 : List Nat := [1, 1, 2, 3, 2, 4, 2, 2, 5]
def baseStart_819935 : Nat := 118140960795 + 819935 * 2 ^ 59
def prefixEnd_819935 : Nat := 4983230072969 + 3 ^ 40 * 819935 * 2
def baseEnd_819935 : Nat := 93560168987634385387043

theorem tailTrace_819935 : CollatzResearch.WordTrace tailWord_819935 prefixEnd_819935 93560168987634385387043 := by
  unfold tailWord_819935
  simp only [CollatzResearch.WordTrace]
  refine ⟨29905486284523003594453259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19936990856348669062968839 29905486284523003594453259)
  ·
    refine ⟨44858229426784505391679889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29905486284523003594453259 44858229426784505391679889)
    ·
      refine ⟨33643672070088379043759917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44858229426784505391679889 33643672070088379043759917)
      ·
        refine ⟨12616377026283142141409969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33643672070088379043759917 12616377026283142141409969)
        ·
          refine ⟨9462282769712356606057477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12616377026283142141409969 9462282769712356606057477)
          ·
            refine ⟨1774178019321066863635777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9462282769712356606057477 1774178019321066863635777)
            ·
              refine ⟨1330633514490800147726833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1774178019321066863635777 1330633514490800147726833)
              ·
                refine ⟨997975135868100110795125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1330633514490800147726833 997975135868100110795125)
                ·
                  refine ⟨93560168987634385387043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 997975135868100110795125 93560168987634385387043)
                  ·
                    rfl

theorem cell22_819935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 5].length) (baseStart_819935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819935 prefixEnd_819935 := by exact prefixLift 819935
  have htrace : WordTrace (prefixWord ++ tailWord_819935) baseStart_819935 baseEnd_819935 := by
    simpa [prefixWord, tailWord_819935, baseEnd_819935] using wordTrace_append hprefix tailTrace_819935
  have hstable : (prefixWord ++ tailWord_819935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819935).length < 2 ^ (prefixWord ++ tailWord_819935).sum := by decide
  have hdescent : baseEnd_819935 < baseStart_819935 := by decide
  rcases family_descends (prefixWord ++ tailWord_819935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819939 : List Nat := [1, 1, 1, 7, 1, 2, 1, 4, 1, 3]
def baseStart_819939 : Nat := 118140960795 + 819939 * 2 ^ 59
def prefixEnd_819939 : Nat := 4983230072969 + 3 ^ 40 * 819939 * 2
def baseEnd_819939 : Nat := 280681876244648479061117

theorem tailTrace_819939 : CollatzResearch.WordTrace tailWord_819939 prefixEnd_819939 280681876244648479061117 := by
  unfold tailWord_819939
  simp only [CollatzResearch.WordTrace]
  refine ⟨29905632176508512277598871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19937088117672341518399247 29905632176508512277598871)
  ·
    refine ⟨44858448264762768416398307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29905632176508512277598871 44858448264762768416398307)
    ·
      refine ⟨67287672397144152624597461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44858448264762768416398307 67287672397144152624597461)
      ·
        refine ⟨1577054821808066077139003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 67287672397144152624597461 1577054821808066077139003)
        ·
          refine ⟨2365582232712099115708505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577054821808066077139003 2365582232712099115708505)
          ·
            refine ⟨1774186674534074336781379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2365582232712099115708505 1774186674534074336781379)
            ·
              refine ⟨2661280011801111505172069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774186674534074336781379 2661280011801111505172069)
              ·
                refine ⟨498990002212708407219763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2661280011801111505172069 498990002212708407219763)
                ·
                  refine ⟨748485003319062610829645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498990002212708407219763 748485003319062610829645)
                  ·
                    refine ⟨280681876244648479061117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 748485003319062610829645 280681876244648479061117)
                    ·
                      rfl

theorem cell22_819939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 1, 3].length) (baseStart_819939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819939 prefixEnd_819939 := by exact prefixLift 819939
  have htrace : WordTrace (prefixWord ++ tailWord_819939) baseStart_819939 baseEnd_819939 := by
    simpa [prefixWord, tailWord_819939, baseEnd_819939] using wordTrace_append hprefix tailTrace_819939
  have hstable : (prefixWord ++ tailWord_819939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819939).length < 2 ^ (prefixWord ++ tailWord_819939).sum := by decide
  have hdescent : baseEnd_819939 < baseStart_819939 := by decide
  rcases family_descends (prefixWord ++ tailWord_819939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819950 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_819950 : Nat := 118140960795 + 819950 * 2 ^ 59
def prefixEnd_819950 : Nat := 4983230072969 + 3 ^ 40 * 819950 * 2
def baseEnd_819950 : Nat := 280685641769448117036083

theorem tailTrace_819950 : CollatzResearch.WordTrace tailWord_819950 prefixEnd_819950 280685641769448117036083 := by
  unfold tailWord_819950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3738254172433582644531163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19937355586312440770832869 3738254172433582644531163)
  ·
    refine ⟨5607381258650373966796745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3738254172433582644531163 5607381258650373966796745)
    ·
      refine ⟨4205535943987780475097559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5607381258650373966796745 4205535943987780475097559)
      ·
        refine ⟨6308303915981670712646339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4205535943987780475097559 6308303915981670712646339)
        ·
          refine ⟨9462455873972506068969509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6308303915981670712646339 9462455873972506068969509)
          ·
            refine ⟨1774210476369844887931783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9462455873972506068969509 1774210476369844887931783)
            ·
              refine ⟨2661315714554767331897675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774210476369844887931783 2661315714554767331897675)
              ·
                refine ⟨3991973571832150997846513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2661315714554767331897675 3991973571832150997846513)
                ·
                  refine ⟨2993980178874113248384885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3991973571832150997846513 2993980178874113248384885)
                  ·
                    refine ⟨280685641769448117036083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2993980178874113248384885 280685641769448117036083)
                    ·
                      rfl

theorem cell22_819950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_819950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819950 prefixEnd_819950 := by exact prefixLift 819950
  have htrace : WordTrace (prefixWord ++ tailWord_819950) baseStart_819950 baseEnd_819950 := by
    simpa [prefixWord, tailWord_819950, baseEnd_819950] using wordTrace_append hprefix tailTrace_819950
  have hstable : (prefixWord ++ tailWord_819950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819950).length < 2 ^ (prefixWord ++ tailWord_819950).sum := by decide
  have hdescent : baseEnd_819950 < baseStart_819950 := by decide
  rcases family_descends (prefixWord ++ tailWord_819950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819956 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_819956 : Nat := 118140960795 + 819956 * 2 ^ 59
def prefixEnd_819956 : Nat := 4983230072969 + 3 ^ 40 * 819956 * 2
def baseEnd_819956 : Nat := 280687695692066101386065

theorem tailTrace_819956 : CollatzResearch.WordTrace tailWord_819956 prefixEnd_819956 280687695692066101386065 := by
  unfold tailWord_819956
  simp only [CollatzResearch.WordTrace]
  refine ⟨14953126108723462090483861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19937501478297949453978481 14953126108723462090483861)
  ·
    refine ⟨700927786346412285491431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14953126108723462090483861 700927786346412285491431)
    ·
      refine ⟨1051391679519618428237147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700927786346412285491431 1051391679519618428237147)
      ·
        refine ⟨1577087519279427642355721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1051391679519618428237147 1577087519279427642355721)
        ·
          refine ⟨1182815639459570731766791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1577087519279427642355721 1182815639459570731766791)
          ·
            refine ⟨1774223459189356097650187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182815639459570731766791 1774223459189356097650187)
            ·
              refine ⟨2661335188784034146475281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774223459189356097650187 2661335188784034146475281)
              ·
                refine ⟨1996001391588025609856461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2661335188784034146475281 1996001391588025609856461)
                ·
                  refine ⟨748500521845509603696173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1996001391588025609856461 748500521845509603696173)
                  ·
                    refine ⟨280687695692066101386065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 748500521845509603696173 280687695692066101386065)
                    ·
                      rfl

theorem cell22_819956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_819956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819956 prefixEnd_819956 := by exact prefixLift 819956
  have htrace : WordTrace (prefixWord ++ tailWord_819956) baseStart_819956 baseEnd_819956 := by
    simpa [prefixWord, tailWord_819956, baseEnd_819956] using wordTrace_append hprefix tailTrace_819956
  have hstable : (prefixWord ++ tailWord_819956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819956).length < 2 ^ (prefixWord ++ tailWord_819956).sum := by decide
  have hdescent : baseEnd_819956 < baseStart_819956 := by decide
  rcases family_descends (prefixWord ++ tailWord_819956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819965 : List Nat := [1, 4, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_819965 : Nat := 118140960795 + 819965 * 2 ^ 59
def prefixEnd_819965 : Nat := 4983230072969 + 3 ^ 40 * 819965 * 2
def baseEnd_819965 : Nat := 280690776575993077911037

theorem tailTrace_819965 : CollatzResearch.WordTrace tailWord_819965 prefixEnd_819965 280690776575993077911037 := by
  unfold tailWord_819965
  simp only [CollatzResearch.WordTrace]
  refine ⟨29906580474414318718045349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19937720316276212478696899 29906580474414318718045349)
  ·
    refine ⟨5607483838952684759633503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29906580474414318718045349 5607483838952684759633503)
    ·
      refine ⟨8411225758429027139450255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5607483838952684759633503 8411225758429027139450255)
      ·
        refine ⟨12616838637643540709175383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8411225758429027139450255 12616838637643540709175383)
        ·
          refine ⟨18925257956465311063763075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12616838637643540709175383 18925257956465311063763075)
          ·
            refine ⟨28387886934697966595644613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18925257956465311063763075 28387886934697966595644613)
            ·
              refine ⟨5322728800255868736683365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28387886934697966595644613 5322728800255868736683365)
              ·
                refine ⟨998011650047975388128131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5322728800255868736683365 998011650047975388128131)
                ·
                  refine ⟨1497017475071963082192197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998011650047975388128131 1497017475071963082192197)
                  ·
                    refine ⟨280690776575993077911037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1497017475071963082192197 280690776575993077911037)
                    ·
                      rfl

theorem cell22_819965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_819965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819965 prefixEnd_819965 := by exact prefixLift 819965
  have htrace : WordTrace (prefixWord ++ tailWord_819965) baseStart_819965 baseEnd_819965 := by
    simpa [prefixWord, tailWord_819965, baseEnd_819965] using wordTrace_append hprefix tailTrace_819965
  have hstable : (prefixWord ++ tailWord_819965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819965).length < 2 ^ (prefixWord ++ tailWord_819965).sum := by decide
  have hdescent : baseEnd_819965 < baseStart_819965 := by decide
  rcases family_descends (prefixWord ++ tailWord_819965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819986 : List Nat := [3, 2, 4, 1, 3, 1, 1, 2, 5]
def baseStart_819986 : Nat := 118140960795 + 819986 * 2 ^ 59
def prefixEnd_819986 : Nat := 4983230072969 + 3 ^ 40 * 819986 * 2
def baseEnd_819986 : Nat := 93565988435052007711991

theorem tailTrace_819986 : CollatzResearch.WordTrace tailWord_819986 prefixEnd_819986 93565988435052007711991 := by
  unfold tailWord_819986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7476836601834559826139953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19938230938225492869706541 7476836601834559826139953)
  ·
    refine ⟨5607627451375919869604965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7476836601834559826139953 5607627451375919869604965)
    ·
      refine ⟨1051430147132984975550931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5607627451375919869604965 1051430147132984975550931)
      ·
        refine ⟨1577145220699477463326397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1051430147132984975550931 1577145220699477463326397)
        ·
          refine ⟨591429457762304048747399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1577145220699477463326397 591429457762304048747399)
          ·
            refine ⟨887144186643456073121099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591429457762304048747399 887144186643456073121099)
            ·
              refine ⟨1330716279965184109681649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887144186643456073121099 1330716279965184109681649)
              ·
                refine ⟨998037209973888082261237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1330716279965184109681649 998037209973888082261237)
                ·
                  refine ⟨93565988435052007711991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 998037209973888082261237 93565988435052007711991)
                  ·
                    rfl

theorem cell22_819986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_819986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_819986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_819986 prefixEnd_819986 := by exact prefixLift 819986
  have htrace : WordTrace (prefixWord ++ tailWord_819986) baseStart_819986 baseEnd_819986 := by
    simpa [prefixWord, tailWord_819986, baseEnd_819986] using wordTrace_append hprefix tailTrace_819986
  have hstable : (prefixWord ++ tailWord_819986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819986).length < 2 ^ (prefixWord ++ tailWord_819986).sum := by decide
  have hdescent : baseEnd_819986 < baseStart_819986 := by decide
  rcases family_descends (prefixWord ++ tailWord_819986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820023 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 2, 7]
def baseStart_820023 : Nat := 118140960795 + 820023 * 2 ^ 59
def prefixEnd_820023 : Nat := 4983230072969 + 3 ^ 40 * 820023 * 2
def baseEnd_820023 : Nat := 280710631161300259960859

theorem tailTrace_820023 : CollatzResearch.WordTrace tailWord_820023 prefixEnd_820023 280710631161300259960859 := by
  unfold tailWord_820023
  simp only [CollatzResearch.WordTrace]
  refine ⟨29908695908204194623656723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19939130605469463082437815 29908695908204194623656723)
  ·
    refine ⟨44863043862306291935485085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29908695908204194623656723 44863043862306291935485085)
    ·
      refine ⟨16823641448364859475806907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44863043862306291935485085 16823641448364859475806907)
      ·
        refine ⟨25235462172547289213710361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16823641448364859475806907 25235462172547289213710361)
        ·
          refine ⟨18926596629410466910282771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25235462172547289213710361 18926596629410466910282771)
          ·
            refine ⟨28389894944115700365424157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18926596629410466910282771 28389894944115700365424157)
            ·
              refine ⟨10646210604043387637034059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28389894944115700365424157 10646210604043387637034059)
              ·
                refine ⟨15969315906065081455551089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10646210604043387637034059 15969315906065081455551089)
                ·
                  refine ⟨11976986929548811091663317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15969315906065081455551089 11976986929548811091663317)
                  ·
                    refine ⟨280710631161300259960859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11976986929548811091663317 280710631161300259960859)
                    ·
                      rfl

theorem cell22_820023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_820023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820023 prefixEnd_820023 := by exact prefixLift 820023
  have htrace : WordTrace (prefixWord ++ tailWord_820023) baseStart_820023 baseEnd_820023 := by
    simpa [prefixWord, tailWord_820023, baseEnd_820023] using wordTrace_append hprefix tailTrace_820023
  have hstable : (prefixWord ++ tailWord_820023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820023).length < 2 ^ (prefixWord ++ tailWord_820023).sum := by decide
  have hdescent : baseEnd_820023 < baseStart_820023 := by decide
  rcases family_descends (prefixWord ++ tailWord_820023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820057 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 3, 3]
def baseStart_820057 : Nat := 118140960795 + 820057 * 2 ^ 59
def prefixEnd_820057 : Nat := 4983230072969 + 3 ^ 40 * 820057 * 2
def baseEnd_820057 : Nat := 280722270056135504610755

theorem tailTrace_820057 : CollatzResearch.WordTrace tailWord_820057 prefixEnd_820057 280722270056135504610755 := by
  unfold tailWord_820057
  simp only [CollatzResearch.WordTrace]
  refine ⟨29909935990081018430394425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19939957326720678953596283 29909935990081018430394425)
  ·
    refine ⟨22432451992560763822795819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29909935990081018430394425 22432451992560763822795819)
    ·
      refine ⟨33648677988841145734193729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22432451992560763822795819 33648677988841145734193729)
      ·
        refine ⟨25236508491630859300645297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33648677988841145734193729 25236508491630859300645297)
        ·
          refine ⟨18927381368723144475483973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25236508491630859300645297 18927381368723144475483973)
          ·
            refine ⟨3548884006635589589153245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18927381368723144475483973 3548884006635589589153245)
            ·
              refine ⟨1330831502488346095932467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3548884006635589589153245 1330831502488346095932467)
              ·
                refine ⟨1996247253732519143898701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330831502488346095932467 1996247253732519143898701)
                ·
                  refine ⟨748592720149694678962013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1996247253732519143898701 748592720149694678962013)
                  ·
                    refine ⟨280722270056135504610755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 748592720149694678962013 280722270056135504610755)
                    ·
                      rfl

theorem cell22_820057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 3].length) (baseStart_820057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820057 prefixEnd_820057 := by exact prefixLift 820057
  have htrace : WordTrace (prefixWord ++ tailWord_820057) baseStart_820057 baseEnd_820057 := by
    simpa [prefixWord, tailWord_820057, baseEnd_820057] using wordTrace_append hprefix tailTrace_820057
  have hstable : (prefixWord ++ tailWord_820057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820057).length < 2 ^ (prefixWord ++ tailWord_820057).sum := by decide
  have hdescent : baseEnd_820057 < baseStart_820057 := by decide
  rcases family_descends (prefixWord ++ tailWord_820057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820149 : List Nat := [1, 3, 3, 2, 1, 1, 4, 3, 4]
def baseStart_820149 : Nat := 118140960795 + 820149 * 2 ^ 59
def prefixEnd_820149 : Nat := 4983230072969 + 3 ^ 40 * 820149 * 2
def baseEnd_820149 : Nat := 93584587845425977103491

theorem tailTrace_820149 : CollatzResearch.WordTrace tailWord_820149 prefixEnd_820149 93584587845425977103491 := by
  unfold tailWord_820149
  simp only [CollatzResearch.WordTrace]
  refine ⟨29913291505747718142743501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19942194337165145428495667 29913291505747718142743501)
  ·
    refine ⟨11217484314655394303528813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29913291505747718142743501 11217484314655394303528813)
    ·
      refine ⟨4206556617995772863823305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11217484314655394303528813 4206556617995772863823305)
      ·
        refine ⟨3154917463496829647867479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4206556617995772863823305 3154917463496829647867479)
        ·
          refine ⟨4732376195245244471801219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3154917463496829647867479 4732376195245244471801219)
          ·
            refine ⟨7098564292867866707701829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4732376195245244471801219 7098564292867866707701829)
            ·
              refine ⟨1330980804912725007694093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7098564292867866707701829 1330980804912725007694093)
              ·
                refine ⟨499117801842271877885285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1330980804912725007694093 499117801842271877885285)
                ·
                  refine ⟨93584587845425977103491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 499117801842271877885285 93584587845425977103491)
                  ·
                    rfl

theorem cell22_820149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_820149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820149 prefixEnd_820149 := by exact prefixLift 820149
  have htrace : WordTrace (prefixWord ++ tailWord_820149) baseStart_820149 baseEnd_820149 := by
    simpa [prefixWord, tailWord_820149, baseEnd_820149] using wordTrace_append hprefix tailTrace_820149
  have hstable : (prefixWord ++ tailWord_820149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820149).length < 2 ^ (prefixWord ++ tailWord_820149).sum := by decide
  have hdescent : baseEnd_820149 < baseStart_820149 := by decide
  rcases family_descends (prefixWord ++ tailWord_820149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820160 : List Nat := [2, 1, 1, 2, 3, 4, 9]
def baseStart_820160 : Nat := 118140960795 + 820160 * 2 ^ 59
def prefixEnd_820160 : Nat := 4983230072969 + 3 ^ 40 * 820160 * 2
def baseEnd_820160 : Nat := 10398427002262132195757

theorem tailTrace_820160 : CollatzResearch.WordTrace tailWord_820160 prefixEnd_820160 10398427002262132195757 := by
  unfold tailWord_820160
  simp only [CollatzResearch.WordTrace]
  refine ⟨14956846354353933510696967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19942461805805244680929289 14956846354353933510696967)
  ·
    refine ⟨22435269531530900266045451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14956846354353933510696967 22435269531530900266045451)
    ·
      refine ⟨33652904297296350399068177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22435269531530900266045451 33652904297296350399068177)
      ·
        refine ⟨25239678222972262799301133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33652904297296350399068177 25239678222972262799301133)
        ·
          refine ⟨9464879333614598549737925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25239678222972262799301133 9464879333614598549737925)
          ·
            refine ⟨1774664875052737228075861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9464879333614598549737925 1774664875052737228075861)
            ·
              refine ⟨10398427002262132195757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1774664875052737228075861 10398427002262132195757)
              ·
                rfl

theorem cell22_820160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 9].length) (baseStart_820160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820160 prefixEnd_820160 := by exact prefixLift 820160
  have htrace : WordTrace (prefixWord ++ tailWord_820160) baseStart_820160 baseEnd_820160 := by
    simpa [prefixWord, tailWord_820160, baseEnd_820160] using wordTrace_append hprefix tailTrace_820160
  have hstable : (prefixWord ++ tailWord_820160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820160).length < 2 ^ (prefixWord ++ tailWord_820160).sum := by decide
  have hdescent : baseEnd_820160 < baseStart_820160 := by decide
  rcases family_descends (prefixWord ++ tailWord_820160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820181 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 1, 5]
def baseStart_820181 : Nat := 118140960795 + 820181 * 2 ^ 59
def prefixEnd_820181 : Nat := 4983230072969 + 3 ^ 40 * 820181 * 2
def baseEnd_820181 : Nat := 280764717790240514510375

theorem tailTrace_820181 : CollatzResearch.WordTrace tailWord_820181 prefixEnd_820181 280764717790240514510375 := by
  unfold tailWord_820181
  simp only [CollatzResearch.WordTrace]
  refine ⟨29914458641631787607908397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19942972427754525071938931 29914458641631787607908397)
  ·
    refine ⟨11217921990611920352965649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29914458641631787607908397 11217921990611920352965649)
    ·
      refine ⟨8413441492958940264724237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11217921990611920352965649 8413441492958940264724237)
      ·
        refine ⟨3155040559859602599271589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8413441492958940264724237 3155040559859602599271589)
        ·
          refine ⟨591570104973675487363423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3155040559859602599271589 591570104973675487363423)
          ·
            refine ⟨887355157460513231045135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591570104973675487363423 887355157460513231045135)
            ·
              refine ⟨1331032736190769846567703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887355157460513231045135 1331032736190769846567703)
              ·
                refine ⟨1996549104286154769851555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331032736190769846567703 1996549104286154769851555)
                ·
                  refine ⟨2994823656429232154777333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996549104286154769851555 2994823656429232154777333)
                  ·
                    refine ⟨280764717790240514510375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2994823656429232154777333 280764717790240514510375)
                    ·
                      rfl

theorem cell22_820181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_820181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820181 prefixEnd_820181 := by exact prefixLift 820181
  have htrace : WordTrace (prefixWord ++ tailWord_820181) baseStart_820181 baseEnd_820181 := by
    simpa [prefixWord, tailWord_820181, baseEnd_820181] using wordTrace_append hprefix tailTrace_820181
  have hstable : (prefixWord ++ tailWord_820181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820181).length < 2 ^ (prefixWord ++ tailWord_820181).sum := by decide
  have hdescent : baseEnd_820181 < baseStart_820181 := by decide
  rcases family_descends (prefixWord ++ tailWord_820181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820194 : List Nat := [3, 3, 3, 1, 1, 2, 1, 8]
def baseStart_820194 : Nat := 118140960795 + 820194 * 2 ^ 59
def prefixEnd_820194 : Nat := 4983230072969 + 3 ^ 40 * 820194 * 2
def baseEnd_820194 : Nat := 31196574217323645992815

theorem tailTrace_820194 : CollatzResearch.WordTrace tailWord_820194 prefixEnd_820194 31196574217323645992815 := by
  unfold tailWord_820194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7478733197646172707032909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19943288527056460552087757 7478733197646172707032909)
  ·
    refine ⟨2804524949117314765137341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7478733197646172707032909 2804524949117314765137341)
    ·
      refine ⟨1051696855918993036926503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2804524949117314765137341 1051696855918993036926503)
      ·
        refine ⟨1577545283878489555389755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1051696855918993036926503 1577545283878489555389755)
        ·
          refine ⟨2366317925817734333084633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577545283878489555389755 2366317925817734333084633)
          ·
            refine ⟨1774738444363300749813475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2366317925817734333084633 1774738444363300749813475)
            ·
              refine ⟨2662107666544951124720213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774738444363300749813475 2662107666544951124720213)
              ·
                refine ⟨31196574217323645992815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2662107666544951124720213 31196574217323645992815)
                ·
                  rfl

theorem cell22_820194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_820194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820194 prefixEnd_820194 := by exact prefixLift 820194
  have htrace : WordTrace (prefixWord ++ tailWord_820194) baseStart_820194 baseEnd_820194 := by
    simpa [prefixWord, tailWord_820194, baseEnd_820194] using wordTrace_append hprefix tailTrace_820194
  have hstable : (prefixWord ++ tailWord_820194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820194).length < 2 ^ (prefixWord ++ tailWord_820194).sum := by decide
  have hdescent : baseEnd_820194 < baseStart_820194 := by decide
  rcases family_descends (prefixWord ++ tailWord_820194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820333 : List Nat := [1, 5, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_820333 : Nat := 118140960795 + 820333 * 2 ^ 59
def prefixEnd_820333 : Nat := 4983230072969 + 3 ^ 40 * 820333 * 2
def baseEnd_820333 : Nat := 280816750496562784709909

theorem tailTrace_820333 : CollatzResearch.WordTrace tailWord_820333 prefixEnd_820333 280816750496562784709909 := by
  unfold tailWord_820333
  simp only [CollatzResearch.WordTrace]
  refine ⟨29920002537081117567441653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19946668358054078378294435 29920002537081117567441653)
  ·
    refine ⟨2805000237851354771947655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29920002537081117567441653 2805000237851354771947655)
    ·
      refine ⟨4207500356777032157921483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2805000237851354771947655 4207500356777032157921483)
      ·
        refine ⟨6311250535165548236882225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4207500356777032157921483 6311250535165548236882225)
        ·
          refine ⟨4733437901374161177661669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6311250535165548236882225 4733437901374161177661669)
          ·
            refine ⟨887519606507655220811563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4733437901374161177661669 887519606507655220811563)
            ·
              refine ⟨1331279409761482831217345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887519606507655220811563 1331279409761482831217345)
              ·
                refine ⟨998459557321112123413009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1331279409761482831217345 998459557321112123413009)
                ·
                  refine ⟨748844667990834092559757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 998459557321112123413009 748844667990834092559757)
                  ·
                    refine ⟨280816750496562784709909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 748844667990834092559757 280816750496562784709909)
                    ·
                      rfl

theorem cell22_820333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_820333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820333 prefixEnd_820333 := by exact prefixLift 820333
  have htrace : WordTrace (prefixWord ++ tailWord_820333) baseStart_820333 baseEnd_820333 := by
    simpa [prefixWord, tailWord_820333, baseEnd_820333] using wordTrace_append hprefix tailTrace_820333
  have hstable : (prefixWord ++ tailWord_820333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820333).length < 2 ^ (prefixWord ++ tailWord_820333).sum := by decide
  have hdescent : baseEnd_820333 < baseStart_820333 := by decide
  rcases family_descends (prefixWord ++ tailWord_820333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820344 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 3, 3]
def baseStart_820344 : Nat := 118140960795 + 820344 * 2 ^ 59
def prefixEnd_820344 : Nat := 4983230072969 + 3 ^ 40 * 820344 * 2
def baseEnd_820344 : Nat := 280820516021362422684875

theorem tailTrace_820344 : CollatzResearch.WordTrace tailWord_820344 prefixEnd_820344 280820516021362422684875 := by
  unfold tailWord_820344
  simp only [CollatzResearch.WordTrace]
  refine ⟨14960201870020633223046043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19946935826694177630728057 14960201870020633223046043)
  ·
    refine ⟨22440302805030949834569065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14960201870020633223046043 22440302805030949834569065)
    ·
      refine ⟨16830227103773212375926799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22440302805030949834569065 16830227103773212375926799)
      ·
        refine ⟨25245340655659818563890199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16830227103773212375926799 25245340655659818563890199)
        ·
          refine ⟨37868010983489727845835299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25245340655659818563890199 37868010983489727845835299)
          ·
            refine ⟨56802016475234591768752949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37868010983489727845835299 56802016475234591768752949)
            ·
              refine ⟨5325189044553242978320589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56802016475234591768752949 5325189044553242978320589)
              ·
                refine ⟨1996945891707466116870221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5325189044553242978320589 1996945891707466116870221)
                ·
                  refine ⟨748854709390299793826333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1996945891707466116870221 748854709390299793826333)
                  ·
                    refine ⟨280820516021362422684875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 748854709390299793826333 280820516021362422684875)
                    ·
                      rfl

theorem cell22_820344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_820344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820344 prefixEnd_820344 := by exact prefixLift 820344
  have htrace : WordTrace (prefixWord ++ tailWord_820344) baseStart_820344 baseEnd_820344 := by
    simpa [prefixWord, tailWord_820344, baseEnd_820344] using wordTrace_append hprefix tailTrace_820344
  have hstable : (prefixWord ++ tailWord_820344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820344).length < 2 ^ (prefixWord ++ tailWord_820344).sum := by decide
  have hdescent : baseEnd_820344 < baseStart_820344 := by decide
  rcases family_descends (prefixWord ++ tailWord_820344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820453 : List Nat := [1, 3, 1, 4, 3, 1, 1, 4, 4]
def baseStart_820453 : Nat := 118140960795 + 820453 * 2 ^ 59
def prefixEnd_820453 : Nat := 4983230072969 + 3 ^ 40 * 820453 * 2
def baseEnd_820453 : Nat := 93619276316307490569847

theorem tailTrace_820453 : CollatzResearch.WordTrace tailWord_820453 prefixEnd_820453 93619276316307490569847 := by
  unfold tailWord_820453
  simp only [CollatzResearch.WordTrace]
  refine ⟨29924379296646378061810013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19949586197764252041206675 29924379296646378061810013)
  ·
    refine ⟨11221642236242391773178755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29924379296646378061810013 11221642236242391773178755)
    ·
      refine ⟨16832463354363587659768133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11221642236242391773178755 16832463354363587659768133)
      ·
        refine ⟨3156086878943172686206525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16832463354363587659768133 3156086878943172686206525)
        ·
          refine ⟨1183532579603689757327447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3156086878943172686206525 1183532579603689757327447)
          ·
            refine ⟨1775298869405534635991171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183532579603689757327447 1775298869405534635991171)
            ·
              refine ⟨2662948304108301953986757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775298869405534635991171 2662948304108301953986757)
              ·
                refine ⟨499302807020306616372517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2662948304108301953986757 499302807020306616372517)
                ·
                  refine ⟨93619276316307490569847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 499302807020306616372517 93619276316307490569847)
                  ·
                    rfl

theorem cell22_820453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_820453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820453 prefixEnd_820453 := by exact prefixLift 820453
  have htrace : WordTrace (prefixWord ++ tailWord_820453) baseStart_820453 baseEnd_820453 := by
    simpa [prefixWord, tailWord_820453, baseEnd_820453] using wordTrace_append hprefix tailTrace_820453
  have hstable : (prefixWord ++ tailWord_820453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820453).length < 2 ^ (prefixWord ++ tailWord_820453).sum := by decide
  have hdescent : baseEnd_820453 < baseStart_820453 := by decide
  rcases family_descends (prefixWord ++ tailWord_820453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820481 : List Nat := [1, 2, 4, 1, 1, 4, 3, 6]
def baseStart_820481 : Nat := 118140960795 + 820481 * 2 ^ 59
def prefixEnd_820481 : Nat := 4983230072969 + 3 ^ 40 * 820481 * 2
def baseEnd_820481 : Nat := 31207490435682192445495

theorem tailTrace_820481 : CollatzResearch.WordTrace tailWord_820481 prefixEnd_820481 31207490435682192445495 := by
  unfold tailWord_820481
  simp only [CollatzResearch.WordTrace]
  refine ⟨29925400540544938843829297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19950267027029959229219531 29925400540544938843829297)
  ·
    refine ⟨22444050405408704132871973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29925400540544938843829297 22444050405408704132871973)
    ·
      refine ⟨4208259451014132024913495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22444050405408704132871973 4208259451014132024913495)
      ·
        refine ⟨6312389176521198037370243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4208259451014132024913495 6312389176521198037370243)
        ·
          refine ⟨9468583764781797056055365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6312389176521198037370243 9468583764781797056055365)
          ·
            refine ⟨1775359455896586948010381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9468583764781797056055365 1775359455896586948010381)
            ·
              refine ⟨665759795961220105503893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1775359455896586948010381 665759795961220105503893)
              ·
                refine ⟨31207490435682192445495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 665759795961220105503893 31207490435682192445495)
                ·
                  rfl

theorem cell22_820481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 6].length) (baseStart_820481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820481 prefixEnd_820481 := by exact prefixLift 820481
  have htrace : WordTrace (prefixWord ++ tailWord_820481) baseStart_820481 baseEnd_820481 := by
    simpa [prefixWord, tailWord_820481, baseEnd_820481] using wordTrace_append hprefix tailTrace_820481
  have hstable : (prefixWord ++ tailWord_820481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820481).length < 2 ^ (prefixWord ++ tailWord_820481).sum := by decide
  have hdescent : baseEnd_820481 < baseStart_820481 := by decide
  rcases family_descends (prefixWord ++ tailWord_820481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820498 : List Nat := [3, 2, 4, 2, 1, 1, 9]
def baseStart_820498 : Nat := 118140960795 + 820498 * 2 ^ 59
def prefixEnd_820498 : Nat := 4983230072969 + 3 ^ 40 * 820498 * 2
def baseEnd_820498 : Nat := 10402712346983605716089

theorem tailTrace_820498 : CollatzResearch.WordTrace tailWord_820498 prefixEnd_820498 10402712346983605716089 := by
  unfold tailWord_820498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7481505145370837686799537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19950680387655567164798765 7481505145370837686799537)
  ·
    refine ⟨5611128859028128265099653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7481505145370837686799537 5611128859028128265099653)
    ·
      refine ⟨1052086661067774049706185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5611128859028128265099653 1052086661067774049706185)
      ·
        refine ⟨789064995800830537279639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1052086661067774049706185 789064995800830537279639)
        ·
          refine ⟨1183597493701245805919459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789064995800830537279639 1183597493701245805919459)
          ·
            refine ⟨1775396240551868708879189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183597493701245805919459 1775396240551868708879189)
            ·
              refine ⟨10402712346983605716089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1775396240551868708879189 10402712346983605716089)
              ·
                rfl

theorem cell22_820498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 9].length) (baseStart_820498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820498 prefixEnd_820498 := by exact prefixLift 820498
  have htrace : WordTrace (prefixWord ++ tailWord_820498) baseStart_820498 baseEnd_820498 := by
    simpa [prefixWord, tailWord_820498, baseEnd_820498] using wordTrace_append hprefix tailTrace_820498
  have hstable : (prefixWord ++ tailWord_820498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820498).length < 2 ^ (prefixWord ++ tailWord_820498).sum := by decide
  have hdescent : baseEnd_820498 < baseStart_820498 := by decide
  rcases family_descends (prefixWord ++ tailWord_820498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820539 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 9, 4]
def baseStart_820539 : Nat := 118140960795 + 820539 * 2 ^ 59
def prefixEnd_820539 : Nat := 4983230072969 + 3 ^ 40 * 820539 * 2
def baseEnd_820539 : Nat := 280887268506446914059277

theorem tailTrace_820539 : CollatzResearch.WordTrace tailWord_820539 prefixEnd_820539 280887268506446914059277 := by
  unfold tailWord_820539
  simp only [CollatzResearch.WordTrace]
  refine ⟨29927515974334814749440671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19951677316223209832960447 29927515974334814749440671)
  ·
    refine ⟨44891273961502222124161007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29927515974334814749440671 44891273961502222124161007)
    ·
      refine ⟨67336910942253333186241511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44891273961502222124161007 67336910942253333186241511)
      ·
        refine ⟨101005366413379999779362267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67336910942253333186241511 101005366413379999779362267)
        ·
          refine ⟨151508049620069999669043401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101005366413379999779362267 151508049620069999669043401)
          ·
            refine ⟨113631037215052499751782551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151508049620069999669043401 113631037215052499751782551)
            ·
              refine ⟨170446555822578749627673827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113631037215052499751782551 170446555822578749627673827)
              ·
                refine ⟨255669833733868124441510741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170446555822578749627673827 255669833733868124441510741)
                ·
                  refine ⟨1498065432034383541649477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 255669833733868124441510741 1498065432034383541649477)
                  ·
                    refine ⟨280887268506446914059277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1498065432034383541649477 280887268506446914059277)
                    ·
                      rfl

theorem cell22_820539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 4].length) (baseStart_820539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820539 prefixEnd_820539 := by exact prefixLift 820539
  have htrace : WordTrace (prefixWord ++ tailWord_820539) baseStart_820539 baseEnd_820539 := by
    simpa [prefixWord, tailWord_820539, baseEnd_820539] using wordTrace_append hprefix tailTrace_820539
  have hstable : (prefixWord ++ tailWord_820539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820539).length < 2 ^ (prefixWord ++ tailWord_820539).sum := by decide
  have hdescent : baseEnd_820539 < baseStart_820539 := by decide
  rcases family_descends (prefixWord ++ tailWord_820539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820554 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 8]
def baseStart_820554 : Nat := 118140960795 + 820554 * 2 ^ 59
def prefixEnd_820554 : Nat := 4983230072969 + 3 ^ 40 * 820554 * 2
def baseEnd_820554 : Nat := 93630801104330624978077

theorem tailTrace_820554 : CollatzResearch.WordTrace tailWord_820554 prefixEnd_820554 93630801104330624978077 := by
  unfold tailWord_820554
  simp only [CollatzResearch.WordTrace]
  refine ⟨7482015767320118077809179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19952042046186981540824477 7482015767320118077809179)
  ·
    refine ⟨11223023650980177116713769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7482015767320118077809179 11223023650980177116713769)
    ·
      refine ⟨8417267738235132837535327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11223023650980177116713769 8417267738235132837535327)
      ·
        refine ⟨12625901607352699256302991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8417267738235132837535327 12625901607352699256302991)
        ·
          refine ⟨18938852411029048884454487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12625901607352699256302991 18938852411029048884454487)
          ·
            refine ⟨28408278616543573326681731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18938852411029048884454487 28408278616543573326681731)
            ·
              refine ⟨42612417924815359990022597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28408278616543573326681731 42612417924815359990022597)
              ·
                refine ⟨7989828360902879998129237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42612417924815359990022597 7989828360902879998129237)
                ·
                  refine ⟨93630801104330624978077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7989828360902879998129237 93630801104330624978077)
                  ·
                    rfl

theorem cell22_820554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_820554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820554 prefixEnd_820554 := by exact prefixLift 820554
  have htrace : WordTrace (prefixWord ++ tailWord_820554) baseStart_820554 baseEnd_820554 := by
    simpa [prefixWord, tailWord_820554, baseEnd_820554] using wordTrace_append hprefix tailTrace_820554
  have hstable : (prefixWord ++ tailWord_820554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820554).length < 2 ^ (prefixWord ++ tailWord_820554).sum := by decide
  have hdescent : baseEnd_820554 < baseStart_820554 := by decide
  rcases family_descends (prefixWord ++ tailWord_820554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820590 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_820590 : Nat := 118140960795 + 820590 * 2 ^ 59
def prefixEnd_820590 : Nat := 4983230072969 + 3 ^ 40 * 820590 * 2
def baseEnd_820590 : Nat := 280904726848699781034121

theorem tailTrace_820590 : CollatzResearch.WordTrace tailWord_820590 prefixEnd_820590 280904726848699781034121 := by
  unfold tailWord_820590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3741172012143756307443403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19952917398100033639698149 3741172012143756307443403)
  ·
    refine ⟨5611758018215634461165105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3741172012143756307443403 5611758018215634461165105)
    ·
      refine ⟨4208818513661725845873829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5611758018215634461165105 4208818513661725845873829)
      ·
        refine ⟨789153471311573596101343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4208818513661725845873829 789153471311573596101343)
        ·
          refine ⟨1183730206967360394152015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789153471311573596101343 1183730206967360394152015)
          ·
            refine ⟨1775595310451040591228023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183730206967360394152015 1775595310451040591228023)
            ·
              refine ⟨2663392965676560886842035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775595310451040591228023 2663392965676560886842035)
              ·
                refine ⟨3995089448514841330263053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2663392965676560886842035 3995089448514841330263053)
                ·
                  refine ⟨1498158543193065498848645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3995089448514841330263053 1498158543193065498848645)
                  ·
                    refine ⟨280904726848699781034121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1498158543193065498848645 280904726848699781034121)
                    ·
                      rfl

theorem cell22_820590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_820590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820590 prefixEnd_820590 := by exact prefixLift 820590
  have htrace : WordTrace (prefixWord ++ tailWord_820590) baseStart_820590 baseEnd_820590 := by
    simpa [prefixWord, tailWord_820590, baseEnd_820590] using wordTrace_append hprefix tailTrace_820590
  have hstable : (prefixWord ++ tailWord_820590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820590).length < 2 ^ (prefixWord ++ tailWord_820590).sum := by decide
  have hdescent : baseEnd_820590 < baseStart_820590 := by decide
  rcases family_descends (prefixWord ++ tailWord_820590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820599 : List Nat := [1, 1, 3, 1, 1, 2, 3, 10]
def baseStart_820599 : Nat := 118140960795 + 820599 * 2 ^ 59
def prefixEnd_820599 : Nat := 4983230072969 + 3 ^ 40 * 820599 * 2
def baseEnd_820599 : Nat := 31211978636958528617677

theorem tailTrace_820599 : CollatzResearch.WordTrace tailWord_820599 prefixEnd_820599 31211978636958528617677 := by
  unfold tailWord_820599
  simp only [CollatzResearch.WordTrace]
  refine ⟨29929704354117444996624851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19953136236078296664416567 29929704354117444996624851)
  ·
    refine ⟨44894556531176167494937277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29929704354117444996624851 44894556531176167494937277)
    ·
      refine ⟨16835458699191062810601479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44894556531176167494937277 16835458699191062810601479)
      ·
        refine ⟨25253188048786594215902219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16835458699191062810601479 25253188048786594215902219)
        ·
          refine ⟨37879782073179891323853329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25253188048786594215902219 37879782073179891323853329)
          ·
            refine ⟨28409836554884918492889997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37879782073179891323853329 28409836554884918492889997)
            ·
              refine ⟨10653688708081844434833749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28409836554884918492889997 10653688708081844434833749)
              ·
                refine ⟨31211978636958528617677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10653688708081844434833749 31211978636958528617677)
                ·
                  rfl

theorem cell22_820599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 10].length) (baseStart_820599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820599 prefixEnd_820599 := by exact prefixLift 820599
  have htrace : WordTrace (prefixWord ++ tailWord_820599) baseStart_820599 baseEnd_820599 := by
    simpa [prefixWord, tailWord_820599, baseEnd_820599] using wordTrace_append hprefix tailTrace_820599
  have hstable : (prefixWord ++ tailWord_820599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820599).length < 2 ^ (prefixWord ++ tailWord_820599).sum := by decide
  have hdescent : baseEnd_820599 < baseStart_820599 := by decide
  rcases family_descends (prefixWord ++ tailWord_820599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820601 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 2, 4]
def baseStart_820601 : Nat := 118140960795 + 820601 * 2 ^ 59
def prefixEnd_820601 : Nat := 4983230072969 + 3 ^ 40 * 820601 * 2
def baseEnd_820601 : Nat := 280908492373499419009087

theorem tailTrace_820601 : CollatzResearch.WordTrace tailWord_820601 prefixEnd_820601 280908492373499419009087 := by
  unfold tailWord_820601
  simp only [CollatzResearch.WordTrace]
  refine ⟨29929777300110199338197657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19953184866740132892131771 29929777300110199338197657)
  ·
    refine ⟨22447332975082649503648243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29929777300110199338197657 22447332975082649503648243)
    ·
      refine ⟨33670999462623974255472365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22447332975082649503648243 33670999462623974255472365)
      ·
        refine ⟨12626624798483990345802137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33670999462623974255472365 12626624798483990345802137)
        ·
          refine ⟨9469968598862992759351603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12626624798483990345802137 9469968598862992759351603)
          ·
            refine ⟨14204952898294489139027405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9469968598862992759351603 14204952898294489139027405)
            ·
              refine ⟨5326857336860433427135277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14204952898294489139027405 5326857336860433427135277)
              ·
                refine ⟨1997571501322662535175729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5326857336860433427135277 1997571501322662535175729)
                ·
                  refine ⟨1498178625991996901381797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1997571501322662535175729 1498178625991996901381797)
                  ·
                    refine ⟨280908492373499419009087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1498178625991996901381797 280908492373499419009087)
                    ·
                      rfl

theorem cell22_820601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_820601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820601 prefixEnd_820601 := by exact prefixLift 820601
  have htrace : WordTrace (prefixWord ++ tailWord_820601) baseStart_820601 baseEnd_820601 := by
    simpa [prefixWord, tailWord_820601, baseEnd_820601] using wordTrace_append hprefix tailTrace_820601
  have hstable : (prefixWord ++ tailWord_820601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820601).length < 2 ^ (prefixWord ++ tailWord_820601).sum := by decide
  have hdescent : baseEnd_820601 < baseStart_820601 := by decide
  rcases family_descends (prefixWord ++ tailWord_820601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820723 : List Nat := [1, 1, 1, 2, 2, 2, 2, 7, 4]
def baseStart_820723 : Nat := 118140960795 + 820723 * 2 ^ 59
def prefixEnd_820723 : Nat := 4983230072969 + 3 ^ 40 * 820723 * 2
def baseEnd_820723 : Nat := 93650085155577255819571

theorem tailTrace_820723 : CollatzResearch.WordTrace tailWord_820723 prefixEnd_820723 93650085155577255819571 := by
  unfold tailWord_820723
  simp only [CollatzResearch.WordTrace]
  refine ⟨29934227005668214174138823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19956151337112142782759215 29934227005668214174138823)
  ·
    refine ⟨44901340508502321261208235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29934227005668214174138823 44901340508502321261208235)
    ·
      refine ⟨67352010762753481891812353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44901340508502321261208235 67352010762753481891812353)
      ·
        refine ⟨50514008072065111418859265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67352010762753481891812353 50514008072065111418859265)
        ·
          refine ⟨37885506054048833564144449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50514008072065111418859265 37885506054048833564144449)
          ·
            refine ⟨28414129540536625173108337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37885506054048833564144449 28414129540536625173108337)
            ·
              refine ⟨21310597155402468879831253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28414129540536625173108337 21310597155402468879831253)
              ·
                refine ⟨499467120829745364371045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21310597155402468879831253 499467120829745364371045)
                ·
                  refine ⟨93650085155577255819571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 499467120829745364371045 93650085155577255819571)
                  ·
                    rfl

theorem cell22_820723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 4].length) (baseStart_820723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820723 prefixEnd_820723 := by exact prefixLift 820723
  have htrace : WordTrace (prefixWord ++ tailWord_820723) baseStart_820723 baseEnd_820723 := by
    simpa [prefixWord, tailWord_820723, baseEnd_820723] using wordTrace_append hprefix tailTrace_820723
  have hstable : (prefixWord ++ tailWord_820723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820723).length < 2 ^ (prefixWord ++ tailWord_820723).sum := by decide
  have hdescent : baseEnd_820723 < baseStart_820723 := by decide
  rcases family_descends (prefixWord ++ tailWord_820723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820755 : List Nat := [1, 1, 1, 2, 1, 7, 1, 3, 2, 3]
def baseStart_820755 : Nat := 118140960795 + 820755 * 2 ^ 59
def prefixEnd_820755 : Nat := 4983230072969 + 3 ^ 40 * 820755 * 2
def baseEnd_820755 : Nat := 280961209720694350658615

theorem tailTrace_820755 : CollatzResearch.WordTrace tailWord_820755 prefixEnd_820755 280961209720694350658615 := by
  unfold tailWord_820755
  simp only [CollatzResearch.WordTrace]
  refine ⟨29935394141552283639303719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19956929427701522426202479 29935394141552283639303719)
  ·
    refine ⟨44903091212328425458955579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29935394141552283639303719 44903091212328425458955579)
    ·
      refine ⟨67354636818492638188433369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44903091212328425458955579 67354636818492638188433369)
      ·
        refine ⟨50515977613869478641325027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67354636818492638188433369 50515977613869478641325027)
        ·
          refine ⟨75773966420804217961987541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50515977613869478641325027 75773966420804217961987541)
          ·
            refine ⟨1775952337987598858484083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 75773966420804217961987541 1775952337987598858484083)
            ·
              refine ⟨2663928506981398287726125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775952337987598858484083 2663928506981398287726125)
              ·
                refine ⟨998973190118024357897297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2663928506981398287726125 998973190118024357897297)
                ·
                  refine ⟨749229892588518268422973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 998973190118024357897297 749229892588518268422973)
                  ·
                    refine ⟨280961209720694350658615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 749229892588518268422973 280961209720694350658615)
                    ·
                      rfl

theorem cell22_820755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 3].length) (baseStart_820755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820755 prefixEnd_820755 := by exact prefixLift 820755
  have htrace : WordTrace (prefixWord ++ tailWord_820755) baseStart_820755 baseEnd_820755 := by
    simpa [prefixWord, tailWord_820755, baseEnd_820755] using wordTrace_append hprefix tailTrace_820755
  have hstable : (prefixWord ++ tailWord_820755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820755).length < 2 ^ (prefixWord ++ tailWord_820755).sum := by decide
  have hdescent : baseEnd_820755 < baseStart_820755 := by decide
  rcases family_descends (prefixWord ++ tailWord_820755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820768 : List Nat := [2, 1, 1, 6, 1, 1, 2, 8]
def baseStart_820768 : Nat := 118140960795 + 820768 * 2 ^ 59
def prefixEnd_820768 : Nat := 4983230072969 + 3 ^ 40 * 820768 * 2
def baseEnd_820768 : Nat := 31218406654040738898175

theorem tailTrace_820768 : CollatzResearch.WordTrace tailWord_820768 prefixEnd_820768 31218406654040738898175 := by
  unfold tailWord_820768
  simp only [CollatzResearch.WordTrace]
  refine ⟨14967934145252593429763479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19957245527003457906351305 14967934145252593429763479)
  ·
    refine ⟨22451901217878890144645219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14967934145252593429763479 22451901217878890144645219)
    ·
      refine ⟨33677851826818335216967829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22451901217878890144645219 33677851826818335216967829)
      ·
        refine ⟨1578649304382109463295367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33677851826818335216967829 1578649304382109463295367)
        ·
          refine ⟨2367973956573164194943051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578649304382109463295367 2367973956573164194943051)
          ·
            refine ⟨3551960934859746292414577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367973956573164194943051 3551960934859746292414577)
            ·
              refine ⟨2663970701144809719310933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3551960934859746292414577 2663970701144809719310933)
              ·
                refine ⟨31218406654040738898175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2663970701144809719310933 31218406654040738898175)
                ·
                  rfl

theorem cell22_820768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 8].length) (baseStart_820768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820768 prefixEnd_820768 := by exact prefixLift 820768
  have htrace : WordTrace (prefixWord ++ tailWord_820768) baseStart_820768 baseEnd_820768 := by
    simpa [prefixWord, tailWord_820768, baseEnd_820768] using wordTrace_append hprefix tailTrace_820768
  have hstable : (prefixWord ++ tailWord_820768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820768).length < 2 ^ (prefixWord ++ tailWord_820768).sum := by decide
  have hdescent : baseEnd_820768 < baseStart_820768 := by decide
  rcases family_descends (prefixWord ++ tailWord_820768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820909 : List Nat := [1, 5, 2, 1, 1, 1, 5, 2, 4]
def baseStart_820909 : Nat := 118140960795 + 820909 * 2 ^ 59
def prefixEnd_820909 : Nat := 4983230072969 + 3 ^ 40 * 820909 * 2
def baseEnd_820909 : Nat := 93671309022629760769381

theorem tailTrace_820909 : CollatzResearch.WordTrace tailWord_820909 prefixEnd_820909 93671309022629760769381 := by
  unfold tailWord_820909
  simp only [CollatzResearch.WordTrace]
  refine ⟨29941010982994367940409781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19960673988662911960273187 29941010982994367940409781)
  ·
    refine ⟨2806969779655721994413417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29941010982994367940409781 2806969779655721994413417)
    ·
      refine ⟨2105227334741791495810063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2806969779655721994413417 2105227334741791495810063)
      ·
        refine ⟨3157841002112687243715095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2105227334741791495810063 3157841002112687243715095)
        ·
          refine ⟨4736761503169030865572643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157841002112687243715095 4736761503169030865572643)
          ·
            refine ⟨7105142254753546298358965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4736761503169030865572643 7105142254753546298358965)
            ·
              refine ⟨666107086383144965471153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7105142254753546298358965 666107086383144965471153)
              ·
                refine ⟨499580314787358724103365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666107086383144965471153 499580314787358724103365)
                ·
                  refine ⟨93671309022629760769381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 499580314787358724103365 93671309022629760769381)
                  ·
                    rfl

theorem cell22_820909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_820909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820909 prefixEnd_820909 := by exact prefixLift 820909
  have htrace : WordTrace (prefixWord ++ tailWord_820909) baseStart_820909 baseEnd_820909 := by
    simpa [prefixWord, tailWord_820909, baseEnd_820909] using wordTrace_append hprefix tailTrace_820909
  have hstable : (prefixWord ++ tailWord_820909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820909).length < 2 ^ (prefixWord ++ tailWord_820909).sum := by decide
  have hdescent : baseEnd_820909 < baseStart_820909 := by decide
  rcases family_descends (prefixWord ++ tailWord_820909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820924 : List Nat := [2, 2, 2, 3, 1, 2, 4, 1, 2, 3]
def baseStart_820924 : Nat := 118140960795 + 820924 * 2 ^ 59
def prefixEnd_820924 : Nat := 4983230072969 + 3 ^ 40 * 820924 * 2
def baseEnd_820924 : Nat := 281019061874434243183097

theorem tailTrace_820924 : CollatzResearch.WordTrace tailWord_820924 prefixEnd_820924 281019061874434243183097 := by
  unfold tailWord_820924
  simp only [CollatzResearch.WordTrace]
  refine ⟨14970779038970012751102913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19961038718626683668137217 14970779038970012751102913)
  ·
    refine ⟨11228084279227509563327185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14970779038970012751102913 11228084279227509563327185)
    ·
      refine ⟨8421063209420632172495389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11228084279227509563327185 8421063209420632172495389)
      ·
        refine ⟨3157898703532737064685771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8421063209420632172495389 3157898703532737064685771)
        ·
          refine ⟨4736848055299105597028657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157898703532737064685771 4736848055299105597028657)
          ·
            refine ⟨3552636041474329197771493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4736848055299105597028657 3552636041474329197771493)
            ·
              refine ⟨666119257776436724582155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3552636041474329197771493 666119257776436724582155)
              ·
                refine ⟨999178886664655086873233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666119257776436724582155 999178886664655086873233)
                ·
                  refine ⟨749384164998491315154925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 999178886664655086873233 749384164998491315154925)
                  ·
                    refine ⟨281019061874434243183097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 749384164998491315154925 281019061874434243183097)
                    ·
                      rfl

theorem cell22_820924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_820924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820924 prefixEnd_820924 := by exact prefixLift 820924
  have htrace : WordTrace (prefixWord ++ tailWord_820924) baseStart_820924 baseEnd_820924 := by
    simpa [prefixWord, tailWord_820924, baseEnd_820924] using wordTrace_append hprefix tailTrace_820924
  have hstable : (prefixWord ++ tailWord_820924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820924).length < 2 ^ (prefixWord ++ tailWord_820924).sum := by decide
  have hdescent : baseEnd_820924 < baseStart_820924 := by decide
  rcases family_descends (prefixWord ++ tailWord_820924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820933 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_820933 : Nat := 118140960795 + 820933 * 2 ^ 59
def prefixEnd_820933 : Nat := 4983230072969 + 3 ^ 40 * 820933 * 2
def baseEnd_820933 : Nat := 281022142758361219708069

theorem tailTrace_820933 : CollatzResearch.WordTrace tailWord_820933 prefixEnd_820933 281022142758361219708069 := by
  unfold tailWord_820933
  simp only [CollatzResearch.WordTrace]
  refine ⟨29941886334907420039283453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19961257556604946692855635 29941886334907420039283453)
  ·
    refine ⟨11228207375590282514731295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29941886334907420039283453 11228207375590282514731295)
    ·
      refine ⟨16842311063385423772096943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11228207375590282514731295 16842311063385423772096943)
      ·
        refine ⟨25263466595078135658145415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16842311063385423772096943 25263466595078135658145415)
        ·
          refine ⟨37895199892617203487218123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25263466595078135658145415 37895199892617203487218123)
          ·
            refine ⟨56842799838925805230827185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37895199892617203487218123 56842799838925805230827185)
            ·
              refine ⟨42632099879194353923120389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56842799838925805230827185 42632099879194353923120389)
              ·
                refine ⟨7993518727348941360585073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42632099879194353923120389 7993518727348941360585073)
                ·
                  refine ⟨5995139045511706020438805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7993518727348941360585073 5995139045511706020438805)
                  ·
                    refine ⟨281022142758361219708069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5995139045511706020438805 281022142758361219708069)
                    ·
                      rfl

theorem cell22_820933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_820933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820933 prefixEnd_820933 := by exact prefixLift 820933
  have htrace : WordTrace (prefixWord ++ tailWord_820933) baseStart_820933 baseEnd_820933 := by
    simpa [prefixWord, tailWord_820933, baseEnd_820933] using wordTrace_append hprefix tailTrace_820933
  have hstable : (prefixWord ++ tailWord_820933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820933).length < 2 ^ (prefixWord ++ tailWord_820933).sum := by decide
  have hdescent : baseEnd_820933 < baseStart_820933 := by decide
  rcases family_descends (prefixWord ++ tailWord_820933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820935 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 5, 3]
def baseStart_820935 : Nat := 118140960795 + 820935 * 2 ^ 59
def prefixEnd_820935 : Nat := 4983230072969 + 3 ^ 40 * 820935 * 2
def baseEnd_820935 : Nat := 281022827399233881158063

theorem tailTrace_820935 : CollatzResearch.WordTrace tailWord_820935 prefixEnd_820935 281022827399233881158063 := by
  unfold tailWord_820935
  simp only [CollatzResearch.WordTrace]
  refine ⟨29941959280900174380856259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19961306187266782920570839 29941959280900174380856259)
  ·
    refine ⟨44912938921350261571284389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29941959280900174380856259 44912938921350261571284389)
    ·
      refine ⟨8421176047753174044615823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44912938921350261571284389 8421176047753174044615823)
      ·
        refine ⟨12631764071629761066923735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8421176047753174044615823 12631764071629761066923735)
        ·
          refine ⟨18947646107444641600385603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12631764071629761066923735 18947646107444641600385603)
          ·
            refine ⟨28421469161166962400578405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18947646107444641600385603 28421469161166962400578405)
            ·
              refine ⟨5329025467718805450108451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28421469161166962400578405 5329025467718805450108451)
              ·
                refine ⟨7993538201578208175162677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5329025467718805450108451 7993538201578208175162677)
                ·
                  refine ⟨749394206397957016421501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7993538201578208175162677 749394206397957016421501)
                  ·
                    refine ⟨281022827399233881158063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 749394206397957016421501 281022827399233881158063)
                    ·
                      rfl

theorem cell22_820935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_820935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820935 prefixEnd_820935 := by exact prefixLift 820935
  have htrace : WordTrace (prefixWord ++ tailWord_820935) baseStart_820935 baseEnd_820935 := by
    simpa [prefixWord, tailWord_820935, baseEnd_820935] using wordTrace_append hprefix tailTrace_820935
  have hstable : (prefixWord ++ tailWord_820935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820935).length < 2 ^ (prefixWord ++ tailWord_820935).sum := by decide
  have hdescent : baseEnd_820935 < baseStart_820935 := by decide
  rcases family_descends (prefixWord ++ tailWord_820935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820982 : List Nat := [5, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_820982 : Nat := 118140960795 + 820982 * 2 ^ 59
def prefixEnd_820982 : Nat := 4983230072969 + 3 ^ 40 * 820982 * 2
def baseEnd_820982 : Nat := 93679638819913808410973

theorem tailTrace_820982 : CollatzResearch.WordTrace tailWord_820982 prefixEnd_820982 93679638819913808410973 := by
  unfold tailWord_820982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871479594483118837988575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19962449007819934271878133 1871479594483118837988575)
  ·
    refine ⟨2807219391724678256982863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1871479594483118837988575 2807219391724678256982863)
    ·
      refine ⟨4210829087587017385474295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2807219391724678256982863 4210829087587017385474295)
      ·
        refine ⟨6316243631380526078211443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4210829087587017385474295 6316243631380526078211443)
        ·
          refine ⟨9474365447070789117317165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6316243631380526078211443 9474365447070789117317165)
          ·
            refine ⟨3552887042651545918993937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9474365447070789117317165 3552887042651545918993937)
            ·
              refine ⟨2664665281988659439245453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3552887042651545918993937 2664665281988659439245453)
              ·
                refine ⟨999249480745747289717045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2664665281988659439245453 999249480745747289717045)
                ·
                  refine ⟨93679638819913808410973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 999249480745747289717045 93679638819913808410973)
                  ·
                    rfl

theorem cell22_820982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_820982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820982 prefixEnd_820982 := by exact prefixLift 820982
  have htrace : WordTrace (prefixWord ++ tailWord_820982) baseStart_820982 baseEnd_820982 := by
    simpa [prefixWord, tailWord_820982, baseEnd_820982] using wordTrace_append hprefix tailTrace_820982
  have hstable : (prefixWord ++ tailWord_820982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820982).length < 2 ^ (prefixWord ++ tailWord_820982).sum := by decide
  have hdescent : baseEnd_820982 < baseStart_820982 := by decide
  rcases family_descends (prefixWord ++ tailWord_820982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820995 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 3, 4]
def baseStart_820995 : Nat := 118140960795 + 820995 * 2 ^ 59
def prefixEnd_820995 : Nat := 4983230072969 + 3 ^ 40 * 820995 * 2
def baseEnd_820995 : Nat := 281043366625413724657879

theorem tailTrace_820995 : CollatzResearch.WordTrace tailWord_820995 prefixEnd_820995 281043366625413724657879 := by
  unfold tailWord_820995
  simp only [CollatzResearch.WordTrace]
  refine ⟨29944147660682804628040439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19962765107121869752026959 29944147660682804628040439)
  ·
    refine ⟨44916221491024206942060659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29944147660682804628040439 44916221491024206942060659)
    ·
      refine ⟨67374332236536310413090989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44916221491024206942060659 67374332236536310413090989)
      ·
        refine ⟨25265374588701116404909121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67374332236536310413090989 25265374588701116404909121)
        ·
          refine ⟨18949030941525837303681841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25265374588701116404909121 18949030941525837303681841)
          ·
            refine ⟨14211773206144377977761381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18949030941525837303681841 14211773206144377977761381)
            ·
              refine ⟨2664707476152070870830259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14211773206144377977761381 2664707476152070870830259)
              ·
                refine ⟨3997061214228106306245389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2664707476152070870830259 3997061214228106306245389)
                ·
                  refine ⟨1498897955335539864842021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3997061214228106306245389 1498897955335539864842021)
                  ·
                    refine ⟨281043366625413724657879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1498897955335539864842021 281043366625413724657879)
                    ·
                      rfl

theorem cell22_820995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 4].length) (baseStart_820995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_820995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_820995 prefixEnd_820995 := by exact prefixLift 820995
  have htrace : WordTrace (prefixWord ++ tailWord_820995) baseStart_820995 baseEnd_820995 := by
    simpa [prefixWord, tailWord_820995, baseEnd_820995] using wordTrace_append hprefix tailTrace_820995
  have hstable : (prefixWord ++ tailWord_820995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820995).length < 2 ^ (prefixWord ++ tailWord_820995).sum := by decide
  have hdescent : baseEnd_820995 < baseStart_820995 := by decide
  rcases family_descends (prefixWord ++ tailWord_820995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821027 : List Nat := [1, 1, 1, 4, 2, 1, 4, 4, 4]
def baseStart_821027 : Nat := 118140960795 + 821027 * 2 ^ 59
def prefixEnd_821027 : Nat := 4983230072969 + 3 ^ 40 * 821027 * 2
def baseEnd_821027 : Nat := 93684773626458769285927

theorem tailTrace_821027 : CollatzResearch.WordTrace tailWord_821027 prefixEnd_821027 93684773626458769285927 := by
  unfold tailWord_821027
  simp only [CollatzResearch.WordTrace]
  refine ⟨29945314796566874093205335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19963543197711249395470223 29945314796566874093205335)
  ·
    refine ⟨44917972194850311139808003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29945314796566874093205335 44917972194850311139808003)
    ·
      refine ⟨67376958292275466709712005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44917972194850311139808003 67376958292275466709712005)
      ·
        refine ⟨12633179679801650008071001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67376958292275466709712005 12633179679801650008071001)
        ·
          refine ⟨9474884759851237506053251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12633179679801650008071001 9474884759851237506053251)
          ·
            refine ⟨14212327139776856259079877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9474884759851237506053251 14212327139776856259079877)
            ·
              refine ⟨2664811338708160548577477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14212327139776856259079877 2664811338708160548577477)
              ·
                refine ⟨499652126007780102858277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2664811338708160548577477 499652126007780102858277)
                ·
                  refine ⟨93684773626458769285927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 499652126007780102858277 93684773626458769285927)
                  ·
                    rfl

theorem cell22_821027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 4].length) (baseStart_821027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821027 prefixEnd_821027 := by exact prefixLift 821027
  have htrace : WordTrace (prefixWord ++ tailWord_821027) baseStart_821027 baseEnd_821027 := by
    simpa [prefixWord, tailWord_821027, baseEnd_821027] using wordTrace_append hprefix tailTrace_821027
  have hstable : (prefixWord ++ tailWord_821027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821027).length < 2 ^ (prefixWord ++ tailWord_821027).sum := by decide
  have hdescent : baseEnd_821027 < baseStart_821027 := by decide
  rcases family_descends (prefixWord ++ tailWord_821027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821042 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_821042 : Nat := 118140960795 + 821042 * 2 ^ 59
def prefixEnd_821042 : Nat := 4983230072969 + 3 ^ 40 * 821042 * 2
def baseEnd_821042 : Nat := 281059455685921268732735

theorem tailTrace_821042 : CollatzResearch.WordTrace tailWord_821042 prefixEnd_821042 281059455685921268732735 := by
  unfold tailWord_821042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7486465472878132913750345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19963907927675021103334253 7486465472878132913750345)
  ·
    refine ⟨5614849104658599685312759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7486465472878132913750345 5614849104658599685312759)
    ·
      refine ⟨8422273656987899527969139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5614849104658599685312759 8422273656987899527969139)
      ·
        refine ⟨12633410485481849291953709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8422273656987899527969139 12633410485481849291953709)
        ·
          refine ⟨4737528932055693484482641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12633410485481849291953709 4737528932055693484482641)
          ·
            refine ⟨3553146699041770113361981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4737528932055693484482641 3553146699041770113361981)
            ·
              refine ⟨1332430012140663792510743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3553146699041770113361981 1332430012140663792510743)
              ·
                refine ⟨1998645018210995688766115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332430012140663792510743 1998645018210995688766115)
                ·
                  refine ⟨2997967527316493533149173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998645018210995688766115 2997967527316493533149173)
                  ·
                    refine ⟨281059455685921268732735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2997967527316493533149173 281059455685921268732735)
                    ·
                      rfl

theorem cell22_821042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_821042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821042 prefixEnd_821042 := by exact prefixLift 821042
  have htrace : WordTrace (prefixWord ++ tailWord_821042) baseStart_821042 baseEnd_821042 := by
    simpa [prefixWord, tailWord_821042, baseEnd_821042] using wordTrace_append hprefix tailTrace_821042
  have hstable : (prefixWord ++ tailWord_821042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821042).length < 2 ^ (prefixWord ++ tailWord_821042).sum := by decide
  have hdescent : baseEnd_821042 < baseStart_821042 := by decide
  rcases family_descends (prefixWord ++ tailWord_821042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821046 : List Nat := [5, 1, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_821046 : Nat := 118140960795 + 821046 * 2 ^ 59
def prefixEnd_821046 : Nat := 4983230072969 + 3 ^ 40 * 821046 * 2
def baseEnd_821046 : Nat := 281060824967666591632723

theorem tailTrace_821046 : CollatzResearch.WordTrace tailWord_821046 prefixEnd_821046 281060824967666591632723 := by
  unfold tailWord_821046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871625486468627521134187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19964005188998693558764661 1871625486468627521134187)
  ·
    refine ⟨2807438229702941281701281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1871625486468627521134187 2807438229702941281701281)
    ·
      refine ⟨2105578672277205961275961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2807438229702941281701281 2105578672277205961275961)
      ·
        refine ⟨1579184004207904470956971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2105578672277205961275961 1579184004207904470956971)
        ·
          refine ⟨2368776006311856706435457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579184004207904470956971 2368776006311856706435457)
          ·
            refine ⟨1776582004733892529826593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2368776006311856706435457 1776582004733892529826593)
            ·
              refine ⟨1332436503550419397369945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776582004733892529826593 1332436503550419397369945)
              ·
                refine ⟨999327377662814548027459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332436503550419397369945 999327377662814548027459)
                ·
                  refine ⟨1498991066494221822041189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 999327377662814548027459 1498991066494221822041189)
                  ·
                    refine ⟨281060824967666591632723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1498991066494221822041189 281060824967666591632723)
                    ·
                      rfl

theorem cell22_821046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_821046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821046 prefixEnd_821046 := by exact prefixLift 821046
  have htrace : WordTrace (prefixWord ++ tailWord_821046) baseStart_821046 baseEnd_821046 := by
    simpa [prefixWord, tailWord_821046, baseEnd_821046] using wordTrace_append hprefix tailTrace_821046
  have hstable : (prefixWord ++ tailWord_821046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821046).length < 2 ^ (prefixWord ++ tailWord_821046).sum := by decide
  have hdescent : baseEnd_821046 < baseStart_821046 := by decide
  rcases family_descends (prefixWord ++ tailWord_821046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821115 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 4, 5]
def baseStart_821115 : Nat := 118140960795 + 821115 * 2 ^ 59
def prefixEnd_821115 : Nat := 4983230072969 + 3 ^ 40 * 821115 * 2
def baseEnd_821115 : Nat := 281084445077773411657511

theorem tailTrace_821115 : CollatzResearch.WordTrace tailWord_821115 prefixEnd_821115 281084445077773411657511 := by
  unfold tailWord_821115
  simp only [CollatzResearch.WordTrace]
  refine ⟨29948524420248065122408799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19965682946832043414939199 29948524420248065122408799)
  ·
    refine ⟨44922786630372097683613199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29948524420248065122408799 44922786630372097683613199)
    ·
      refine ⟨67384179945558146525419799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44922786630372097683613199 67384179945558146525419799)
      ·
        refine ⟨101076269918337219788129699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67384179945558146525419799 101076269918337219788129699)
        ·
          refine ⟨151614404877505829682194549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101076269918337219788129699 151614404877505829682194549)
          ·
            refine ⟨14213850457266171532705739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151614404877505829682194549 14213850457266171532705739)
            ·
              refine ⟨21320775685899257299058609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14213850457266171532705739 21320775685899257299058609)
              ·
                refine ⟨15990581764424442974293957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21320775685899257299058609 15990581764424442974293957)
                ·
                  refine ⟨2998234080829583057680117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15990581764424442974293957 2998234080829583057680117)
                  ·
                    refine ⟨281084445077773411657511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2998234080829583057680117 281084445077773411657511)
                    ·
                      rfl

theorem cell22_821115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 5].length) (baseStart_821115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821115 prefixEnd_821115 := by exact prefixLift 821115
  have htrace : WordTrace (prefixWord ++ tailWord_821115) baseStart_821115 baseEnd_821115 := by
    simpa [prefixWord, tailWord_821115, baseEnd_821115] using wordTrace_append hprefix tailTrace_821115
  have hstable : (prefixWord ++ tailWord_821115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821115).length < 2 ^ (prefixWord ++ tailWord_821115).sum := by decide
  have hdescent : baseEnd_821115 < baseStart_821115 := by decide
  rcases family_descends (prefixWord ++ tailWord_821115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821138 : List Nat := [3, 2, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_821138 : Nat := 118140960795 + 821138 * 2 ^ 59
def prefixEnd_821138 : Nat := 4983230072969 + 3 ^ 40 * 821138 * 2
def baseEnd_821138 : Nat := 281092318447809018332441

theorem tailTrace_821138 : CollatzResearch.WordTrace tailWord_821138 prefixEnd_821138 281092318447809018332441 := by
  unfold tailWord_821138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7487340824791185012624017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19966242199443160033664045 7487340824791185012624017)
  ·
    refine ⟨5615505618593388759468013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7487340824791185012624017 5615505618593388759468013)
    ·
      refine ⟨2105814606972520784800505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5615505618593388759468013 2105814606972520784800505)
      ·
        refine ⟨1579360955229390588600379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2105814606972520784800505 1579360955229390588600379)
        ·
          refine ⟨2369041432844085882900569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579360955229390588600379 2369041432844085882900569)
          ·
            refine ⟨1776781074633064412175427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2369041432844085882900569 1776781074633064412175427)
            ·
              refine ⟨2665171611949596618263141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1776781074633064412175427 2665171611949596618263141)
              ·
                refine ⟨499719677240549365924339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2665171611949596618263141 499719677240549365924339)
                ·
                  refine ⟨749579515860824048886509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 499719677240549365924339 749579515860824048886509)
                  ·
                    refine ⟨281092318447809018332441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 749579515860824048886509 281092318447809018332441)
                    ·
                      rfl

theorem cell22_821138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_821138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821138 prefixEnd_821138 := by exact prefixLift 821138
  have htrace : WordTrace (prefixWord ++ tailWord_821138) baseStart_821138 baseEnd_821138 := by
    simpa [prefixWord, tailWord_821138, baseEnd_821138] using wordTrace_append hprefix tailTrace_821138
  have hstable : (prefixWord ++ tailWord_821138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821138).length < 2 ^ (prefixWord ++ tailWord_821138).sum := by decide
  have hdescent : baseEnd_821138 < baseStart_821138 := by decide
  rcases family_descends (prefixWord ++ tailWord_821138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821177 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 1, 5]
def baseStart_821177 : Nat := 118140960795 + 821177 * 2 ^ 59
def prefixEnd_821177 : Nat := 4983230072969 + 3 ^ 40 * 821177 * 2
def baseEnd_821177 : Nat := 281105668944825916607321

theorem tailTrace_821177 : CollatzResearch.WordTrace tailWord_821177 prefixEnd_821177 281105668944825916607321 := by
  unfold tailWord_821177
  simp only [CollatzResearch.WordTrace]
  refine ⟨29950785746023449711165785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19967190497348966474110523 29950785746023449711165785)
  ·
    refine ⟨22463089309517587283374339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29950785746023449711165785 22463089309517587283374339)
    ·
      refine ⟨33694633964276380925061509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22463089309517587283374339 33694633964276380925061509)
      ·
        refine ⟨6317743868301821423449033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33694633964276380925061509 6317743868301821423449033)
        ·
          refine ⟨4738307901226366067586775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6317743868301821423449033 4738307901226366067586775)
          ·
            refine ⟨7107461851839549101380163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4738307901226366067586775 7107461851839549101380163)
            ·
              refine ⟨10661192777759323652070245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7107461851839549101380163 10661192777759323652070245)
              ·
                refine ⟨1998973645829873184763171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10661192777759323652070245 1998973645829873184763171)
                ·
                  refine ⟨2998460468744809777144757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998973645829873184763171 2998460468744809777144757)
                  ·
                    refine ⟨281105668944825916607321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2998460468744809777144757 281105668944825916607321)
                    ·
                      rfl

theorem cell22_821177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_821177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821177 prefixEnd_821177 := by exact prefixLift 821177
  have htrace : WordTrace (prefixWord ++ tailWord_821177) baseStart_821177 baseEnd_821177 := by
    simpa [prefixWord, tailWord_821177, baseEnd_821177] using wordTrace_append hprefix tailTrace_821177
  have hstable : (prefixWord ++ tailWord_821177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821177).length < 2 ^ (prefixWord ++ tailWord_821177).sum := by decide
  have hdescent : baseEnd_821177 < baseStart_821177 := by decide
  rcases family_descends (prefixWord ++ tailWord_821177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821181 : List Nat := [1, 4, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_821181 : Nat := 118140960795 + 821181 * 2 ^ 59
def prefixEnd_821181 : Nat := 4983230072969 + 3 ^ 40 * 821181 * 2
def baseEnd_821181 : Nat := 281107038226571239507309

theorem tailTrace_821181 : CollatzResearch.WordTrace tailWord_821181 prefixEnd_821181 281107038226571239507309 := by
  unfold tailWord_821181
  simp only [CollatzResearch.WordTrace]
  refine ⟨29950931638008958394311397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19967287758672638929540931 29950931638008958394311397)
  ·
    refine ⟨5615799682126679698933387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29950931638008958394311397 5615799682126679698933387)
    ·
      refine ⟨8423699523190019548400081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5615799682126679698933387 8423699523190019548400081)
      ·
        refine ⟨6317774642392514661300061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8423699523190019548400081 6317774642392514661300061)
        ·
          refine ⟨2369165490897192997987523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6317774642392514661300061 2369165490897192997987523)
          ·
            refine ⟨3553748236345789496981285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369165490897192997987523 3553748236345789496981285)
            ·
              refine ⟨666327794314835530683991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3553748236345789496981285 666327794314835530683991)
              ·
                refine ⟨999491691472253296025987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666327794314835530683991 999491691472253296025987)
                ·
                  refine ⟨1499237537208379944038981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 999491691472253296025987 1499237537208379944038981)
                  ·
                    refine ⟨281107038226571239507309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1499237537208379944038981 281107038226571239507309)
                    ·
                      rfl

theorem cell22_821181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_821181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821181 prefixEnd_821181 := by exact prefixLift 821181
  have htrace : WordTrace (prefixWord ++ tailWord_821181) baseStart_821181 baseEnd_821181 := by
    simpa [prefixWord, tailWord_821181, baseEnd_821181] using wordTrace_append hprefix tailTrace_821181
  have hstable : (prefixWord ++ tailWord_821181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821181).length < 2 ^ (prefixWord ++ tailWord_821181).sum := by decide
  have hdescent : baseEnd_821181 < baseStart_821181 := by decide
  rcases family_descends (prefixWord ++ tailWord_821181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821267 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 2, 5]
def baseStart_821267 : Nat := 118140960795 + 821267 * 2 ^ 59
def prefixEnd_821267 : Nat := 4983230072969 + 3 ^ 40 * 821267 * 2
def baseEnd_821267 : Nat := 281136477784095681857045

theorem tailTrace_821267 : CollatzResearch.WordTrace tailWord_821267 prefixEnd_821267 281136477784095681857045 := by
  unfold tailWord_821267
  simp only [CollatzResearch.WordTrace]
  refine ⟨29954068315697395081942055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19969378877131596721294703 29954068315697395081942055)
  ·
    refine ⟨44931102473546092622913083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29954068315697395081942055 44931102473546092622913083)
    ·
      refine ⟨67396653710319138934369625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44931102473546092622913083 67396653710319138934369625)
      ·
        refine ⟨50547490282739354200777219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67396653710319138934369625 50547490282739354200777219)
        ·
          refine ⟨75821235424109031301165829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50547490282739354200777219 75821235424109031301165829)
          ·
            refine ⟨14216481642020443368968593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75821235424109031301165829 14216481642020443368968593)
            ·
              refine ⟨10662361231515332526726445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14216481642020443368968593 10662361231515332526726445)
              ·
                refine ⟨3998385461818249697522417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10662361231515332526726445 3998385461818249697522417)
                ·
                  refine ⟨2998789096363687273141813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3998385461818249697522417 2998789096363687273141813)
                  ·
                    refine ⟨281136477784095681857045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2998789096363687273141813 281136477784095681857045)
                    ·
                      rfl

theorem cell22_821267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 5].length) (baseStart_821267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821267 prefixEnd_821267 := by exact prefixLift 821267
  have htrace : WordTrace (prefixWord ++ tailWord_821267) baseStart_821267 baseEnd_821267 := by
    simpa [prefixWord, tailWord_821267, baseEnd_821267] using wordTrace_append hprefix tailTrace_821267
  have hstable : (prefixWord ++ tailWord_821267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821267).length < 2 ^ (prefixWord ++ tailWord_821267).sum := by decide
  have hdescent : baseEnd_821267 < baseStart_821267 := by decide
  rcases family_descends (prefixWord ++ tailWord_821267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821299 : List Nat := [1, 1, 1, 2, 4, 1, 2, 5, 1, 4]
def baseStart_821299 : Nat := 118140960795 + 821299 * 2 ^ 59
def prefixEnd_821299 : Nat := 4983230072969 + 3 ^ 40 * 821299 * 2
def baseEnd_821299 : Nat := 281147432038058265056947

theorem tailTrace_821299 : CollatzResearch.WordTrace tailWord_821299 prefixEnd_821299 281147432038058265056947 := by
  unfold tailWord_821299
  simp only [CollatzResearch.WordTrace]
  refine ⟨29955235451581464547106951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19970156967720976364737967 29955235451581464547106951)
  ·
    refine ⟨44932853177372196820660427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29955235451581464547106951 44932853177372196820660427)
    ·
      refine ⟨67399279766058295230990641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44932853177372196820660427 67399279766058295230990641)
      ·
        refine ⟨50549459824543721423242981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67399279766058295230990641 50549459824543721423242981)
        ·
          refine ⟨9478023717101947766858059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50549459824543721423242981 9478023717101947766858059)
          ·
            refine ⟨14217035575652921650287089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9478023717101947766858059 14217035575652921650287089)
            ·
              refine ⟨10662776681739691237715317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14217035575652921650287089 10662776681739691237715317)
              ·
                refine ⟨999635313913096053535811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10662776681739691237715317 999635313913096053535811)
                ·
                  refine ⟨1499452970869644080303717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 999635313913096053535811 1499452970869644080303717)
                  ·
                    refine ⟨281147432038058265056947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1499452970869644080303717 281147432038058265056947)
                    ·
                      rfl

theorem cell22_821299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 4].length) (baseStart_821299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821299 prefixEnd_821299 := by exact prefixLift 821299
  have htrace : WordTrace (prefixWord ++ tailWord_821299) baseStart_821299 baseEnd_821299 := by
    simpa [prefixWord, tailWord_821299, baseEnd_821299] using wordTrace_append hprefix tailTrace_821299
  have hstable : (prefixWord ++ tailWord_821299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821299).length < 2 ^ (prefixWord ++ tailWord_821299).sum := by decide
  have hdescent : baseEnd_821299 < baseStart_821299 := by decide
  rcases family_descends (prefixWord ++ tailWord_821299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821327 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 3, 6]
def baseStart_821327 : Nat := 118140960795 + 821327 * 2 ^ 59
def prefixEnd_821327 : Nat := 4983230072969 + 3 ^ 40 * 821327 * 2
def baseEnd_821327 : Nat := 281157017010275525356861

theorem tailTrace_821327 : CollatzResearch.WordTrace tailWord_821327 prefixEnd_821327 281157017010275525356861 := by
  unfold tailWord_821327
  simp only [CollatzResearch.WordTrace]
  refine ⟨29956256695480025329126235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19970837796986683552750823 29956256695480025329126235)
  ·
    refine ⟨44934385043220037993689353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29956256695480025329126235 44934385043220037993689353)
    ·
      refine ⟨33700788782415028495267015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44934385043220037993689353 33700788782415028495267015)
      ·
        refine ⟨50551183173622542742900523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33700788782415028495267015 50551183173622542742900523)
        ·
          refine ⟨75826774760433814114350785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50551183173622542742900523 75826774760433814114350785)
          ·
            refine ⟨56870081070325360585763089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75826774760433814114350785 56870081070325360585763089)
            ·
              refine ⟨42652560802744020439322317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56870081070325360585763089 42652560802744020439322317)
              ·
                refine ⟨15994710301029007664745869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42652560802744020439322317 15994710301029007664745869)
                ·
                  refine ⟨5998016362885877874279701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15994710301029007664745869 5998016362885877874279701)
                  ·
                    refine ⟨281157017010275525356861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5998016362885877874279701 281157017010275525356861)
                    ·
                      rfl

theorem cell22_821327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_821327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821327 prefixEnd_821327 := by exact prefixLift 821327
  have htrace : WordTrace (prefixWord ++ tailWord_821327) baseStart_821327 baseEnd_821327 := by
    simpa [prefixWord, tailWord_821327, baseEnd_821327] using wordTrace_append hprefix tailTrace_821327
  have hstable : (prefixWord ++ tailWord_821327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821327).length < 2 ^ (prefixWord ++ tailWord_821327).sum := by decide
  have hdescent : baseEnd_821327 < baseStart_821327 := by decide
  rcases family_descends (prefixWord ++ tailWord_821327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821329 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 6, 3]
def baseStart_821329 : Nat := 118140960795 + 821329 * 2 ^ 59
def prefixEnd_821329 : Nat := 4983230072969 + 3 ^ 40 * 821329 * 2
def baseEnd_821329 : Nat := 281157701651148186806855

theorem tailTrace_821329 : CollatzResearch.WordTrace tailWord_821329 prefixEnd_821329 281157701651148186806855 := by
  unfold tailWord_821329
  simp only [CollatzResearch.WordTrace]
  refine ⟨29956329641472779670699041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19970886427648519780466027 29956329641472779670699041)
  ·
    refine ⟨22467247231104584753024281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29956329641472779670699041 22467247231104584753024281)
    ·
      refine ⟨16850435423328438564768211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22467247231104584753024281 16850435423328438564768211)
      ·
        refine ⟨25275653134992657847152317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16850435423328438564768211 25275653134992657847152317)
        ·
          refine ⟨9478369925622246692682119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25275653134992657847152317 9478369925622246692682119)
          ·
            refine ⟨14217554888433370039023179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9478369925622246692682119 14217554888433370039023179)
            ·
              refine ⟨21326332332650055058534769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14217554888433370039023179 21326332332650055058534769)
              ·
                refine ⟨15994749249487541293901077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21326332332650055058534769 15994749249487541293901077)
                ·
                  refine ⟨749753871069728498151613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15994749249487541293901077 749753871069728498151613)
                  ·
                    refine ⟨281157701651148186806855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 749753871069728498151613 281157701651148186806855)
                    ·
                      rfl

theorem cell22_821329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_821329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821329 prefixEnd_821329 := by exact prefixLift 821329
  have htrace : WordTrace (prefixWord ++ tailWord_821329) baseStart_821329 baseEnd_821329 := by
    simpa [prefixWord, tailWord_821329, baseEnd_821329] using wordTrace_append hprefix tailTrace_821329
  have hstable : (prefixWord ++ tailWord_821329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821329).length < 2 ^ (prefixWord ++ tailWord_821329).sum := by decide
  have hdescent : baseEnd_821329 < baseStart_821329 := by decide
  rcases family_descends (prefixWord ++ tailWord_821329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821344 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 1, 6]
def baseStart_821344 : Nat := 118140960795 + 821344 * 2 ^ 59
def prefixEnd_821344 : Nat := 4983230072969 + 3 ^ 40 * 821344 * 2
def baseEnd_821344 : Nat := 281162836457693147681809

theorem tailTrace_821344 : CollatzResearch.WordTrace tailWord_821344 prefixEnd_821344 281162836457693147681809 := by
  unfold tailWord_821344
  simp only [CollatzResearch.WordTrace]
  refine ⟨14978438368209218616247543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19971251157612291488330057 14978438368209218616247543)
  ·
    refine ⟨22467657552313827924371315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14978438368209218616247543 22467657552313827924371315)
    ·
      refine ⟨33701486328470741886556973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22467657552313827924371315 33701486328470741886556973)
      ·
        refine ⟨12638057373176528207458865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33701486328470741886556973 12638057373176528207458865)
        ·
          refine ⟨9478543029882396155594149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12638057373176528207458865 9478543029882396155594149)
          ·
            refine ⟨1777226818102949279173903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9478543029882396155594149 1777226818102949279173903)
            ·
              refine ⟨2665840227154423918760855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777226818102949279173903 2665840227154423918760855)
              ·
                refine ⟨3998760340731635878141283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2665840227154423918760855 3998760340731635878141283)
                ·
                  refine ⟨5998140511097453817211925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998760340731635878141283 5998140511097453817211925)
                  ·
                    refine ⟨281162836457693147681809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5998140511097453817211925 281162836457693147681809)
                    ·
                      rfl

theorem cell22_821344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_821344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821344 prefixEnd_821344 := by exact prefixLift 821344
  have htrace : WordTrace (prefixWord ++ tailWord_821344) baseStart_821344 baseEnd_821344 := by
    simpa [prefixWord, tailWord_821344, baseEnd_821344] using wordTrace_append hprefix tailTrace_821344
  have hstable : (prefixWord ++ tailWord_821344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821344).length < 2 ^ (prefixWord ++ tailWord_821344).sum := by decide
  have hdescent : baseEnd_821344 < baseStart_821344 := by decide
  rcases family_descends (prefixWord ++ tailWord_821344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821404 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 9]
def baseStart_821404 : Nat := 118140960795 + 821404 * 2 ^ 59
def prefixEnd_821404 : Nat := 4983230072969 + 3 ^ 40 * 821404 * 2
def baseEnd_821404 : Nat := 93727791894624330393875

theorem tailTrace_821404 : CollatzResearch.WordTrace tailWord_821404 prefixEnd_821404 93727791894624330393875 := by
  unfold tailWord_821404
  simp only [CollatzResearch.WordTrace]
  refine ⟨14979532558100533739839633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19972710077467378319786177 14979532558100533739839633)
  ·
    refine ⟨11234649418575400304879725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14979532558100533739839633 11234649418575400304879725)
    ·
      refine ⟨4212993531965775114329897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11234649418575400304879725 4212993531965775114329897)
      ·
        refine ⟨3159745148974331335747423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4212993531965775114329897 3159745148974331335747423)
        ·
          refine ⟨4739617723461497003621135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3159745148974331335747423 4739617723461497003621135)
          ·
            refine ⟨7109426585192245505431703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4739617723461497003621135 7109426585192245505431703)
            ·
              refine ⟨10664139877788368258147555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7109426585192245505431703 10664139877788368258147555)
              ·
                refine ⟨15996209816682552387221333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10664139877788368258147555 15996209816682552387221333)
                ·
                  refine ⟨93727791894624330393875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15996209816682552387221333 93727791894624330393875)
                  ·
                    rfl

theorem cell22_821404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_821404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821404 prefixEnd_821404 := by exact prefixLift 821404
  have htrace : WordTrace (prefixWord ++ tailWord_821404) baseStart_821404 baseEnd_821404 := by
    simpa [prefixWord, tailWord_821404, baseEnd_821404] using wordTrace_append hprefix tailTrace_821404
  have hstable : (prefixWord ++ tailWord_821404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821404).length < 2 ^ (prefixWord ++ tailWord_821404).sum := by decide
  have hdescent : baseEnd_821404 < baseStart_821404 := by decide
  rcases family_descends (prefixWord ++ tailWord_821404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821421 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 7]
def baseStart_821421 : Nat := 118140960795 + 821421 * 2 ^ 59
def prefixEnd_821421 : Nat := 4983230072969 + 3 ^ 40 * 821421 * 2
def baseEnd_821421 : Nat := 93729731710430204502191

theorem tailTrace_821421 : CollatzResearch.WordTrace tailWord_821421 prefixEnd_821421 93729731710430204502191 := by
  unfold tailWord_821421
  simp only [CollatzResearch.WordTrace]
  refine ⟨29959685157139479383048117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19973123438092986255365411 29959685157139479383048117)
  ·
    refine ⟨2808720483481826192160761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29959685157139479383048117 2808720483481826192160761)
    ·
      refine ⟨2106540362611369644120571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2808720483481826192160761 2106540362611369644120571)
      ·
        refine ⟨3159810543917054466180857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2106540362611369644120571 3159810543917054466180857)
        ·
          refine ⟨2369857907937790849635643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3159810543917054466180857 2369857907937790849635643)
          ·
            refine ⟨3554786861906686274453465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369857907937790849635643 3554786861906686274453465)
            ·
              refine ⟨2666090146430014705840099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3554786861906686274453465 2666090146430014705840099)
              ·
                refine ⟨3999135219645022058760149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666090146430014705840099 3999135219645022058760149)
                ·
                  refine ⟨93729731710430204502191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3999135219645022058760149 93729731710430204502191)
                  ·
                    rfl

theorem cell22_821421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_821421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821421 prefixEnd_821421 := by exact prefixLift 821421
  have htrace : WordTrace (prefixWord ++ tailWord_821421) baseStart_821421 baseEnd_821421 := by
    simpa [prefixWord, tailWord_821421, baseEnd_821421] using wordTrace_append hprefix tailTrace_821421
  have hstable : (prefixWord ++ tailWord_821421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821421).length < 2 ^ (prefixWord ++ tailWord_821421).sum := by decide
  have hdescent : baseEnd_821421 < baseStart_821421 := by decide
  rcases family_descends (prefixWord ++ tailWord_821421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821425 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 3, 3]
def baseStart_821425 : Nat := 118140960795 + 821425 * 2 ^ 59
def prefixEnd_821425 : Nat := 4983230072969 + 3 ^ 40 * 821425 * 2
def baseEnd_821425 : Nat := 281190564413035936406561

theorem tailTrace_821425 : CollatzResearch.WordTrace tailWord_821425 prefixEnd_821425 281190564413035936406561 := by
  unfold tailWord_821425
  simp only [CollatzResearch.WordTrace]
  refine ⟨29959831049124988066193729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19973220699416658710795819 29959831049124988066193729)
  ·
    refine ⟨22469873286843741049645297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29959831049124988066193729 22469873286843741049645297)
    ·
      refine ⟨16852404965132805787233973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22469873286843741049645297 16852404965132805787233973)
      ·
        refine ⟨1579912965481200542553185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16852404965132805787233973 1579912965481200542553185)
        ·
          refine ⟨1184934724110900406914889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1579912965481200542553185 1184934724110900406914889)
          ·
            refine ⟨888701043083175305186167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1184934724110900406914889 888701043083175305186167)
            ·
              refine ⟨1333051564624762957779251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888701043083175305186167 1333051564624762957779251)
              ·
                refine ⟨1999577346937144436668877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333051564624762957779251 1999577346937144436668877)
                ·
                  refine ⟨749841505101429163750829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1999577346937144436668877 749841505101429163750829)
                  ·
                    refine ⟨281190564413035936406561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 749841505101429163750829 281190564413035936406561)
                    ·
                      rfl

theorem cell22_821425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_821425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821425 prefixEnd_821425 := by exact prefixLift 821425
  have htrace : WordTrace (prefixWord ++ tailWord_821425) baseStart_821425 baseEnd_821425 := by
    simpa [prefixWord, tailWord_821425, baseEnd_821425] using wordTrace_append hprefix tailTrace_821425
  have hstable : (prefixWord ++ tailWord_821425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821425).length < 2 ^ (prefixWord ++ tailWord_821425).sum := by decide
  have hdescent : baseEnd_821425 < baseStart_821425 := by decide
  rcases family_descends (prefixWord ++ tailWord_821425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821438 : List Nat := [4, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_821438 : Nat := 118140960795 + 821438 * 2 ^ 59
def prefixEnd_821438 : Nat := 4983230072969 + 3 ^ 40 * 821438 * 2
def baseEnd_821438 : Nat := 93731671526236078610507

theorem tailTrace_821438 : CollatzResearch.WordTrace tailWord_821438 prefixEnd_821438 93731671526236078610507 := by
  unfold tailWord_821438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745038149759736410802121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19973536798718594190944645 3745038149759736410802121)
  ·
    refine ⟨2808778612319802308101591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3745038149759736410802121 2808778612319802308101591)
    ·
      refine ⟨4213167918479703462152387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2808778612319802308101591 4213167918479703462152387)
      ·
        refine ⟨6319751877719555193228581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4213167918479703462152387 6319751877719555193228581)
        ·
          refine ⟨1184953477072416598730359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6319751877719555193228581 1184953477072416598730359)
          ·
            refine ⟨1777430215608624898095539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184953477072416598730359 1777430215608624898095539)
            ·
              refine ⟨2666145323412937347143309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777430215608624898095539 2666145323412937347143309)
              ·
                refine ⟨999804496279851505178741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2666145323412937347143309 999804496279851505178741)
                ·
                  refine ⟨93731671526236078610507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 999804496279851505178741 93731671526236078610507)
                  ·
                    rfl

theorem cell22_821438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_821438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821438 prefixEnd_821438 := by exact prefixLift 821438
  have htrace : WordTrace (prefixWord ++ tailWord_821438) baseStart_821438 baseEnd_821438 := by
    simpa [prefixWord, tailWord_821438, baseEnd_821438] using wordTrace_append hprefix tailTrace_821438
  have hstable : (prefixWord ++ tailWord_821438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821438).length < 2 ^ (prefixWord ++ tailWord_821438).sum := by decide
  have hdescent : baseEnd_821438 < baseStart_821438 := by decide
  rcases family_descends (prefixWord ++ tailWord_821438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821498 : List Nat := [3, 1, 1, 1, 1, 5, 2, 3, 2, 3]
def baseStart_821498 : Nat := 118140960795 + 821498 * 2 ^ 59
def prefixEnd_821498 : Nat := 4983230072969 + 3 ^ 40 * 821498 * 2
def baseEnd_821498 : Nat := 281215553804888079331337

theorem tailTrace_821498 : CollatzResearch.WordTrace tailWord_821498 prefixEnd_821498 281215553804888079331337 := by
  unfold tailWord_821498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490623394465130383400287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19974995718573681022400765 7490623394465130383400287)
  ·
    refine ⟨11235935091697695575100431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7490623394465130383400287 11235935091697695575100431)
    ·
      refine ⟨16853902637546543362650647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11235935091697695575100431 16853902637546543362650647)
      ·
        refine ⟨25280853956319815043975971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16853902637546543362650647 25280853956319815043975971)
        ·
          refine ⟨37921280934479722565963957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25280853956319815043975971 37921280934479722565963957)
          ·
            refine ⟨3555120087607473990559121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37921280934479722565963957 3555120087607473990559121)
            ·
              refine ⟨2666340065705605492919341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3555120087607473990559121 2666340065705605492919341)
              ·
                refine ⟨999877524639602059844753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2666340065705605492919341 999877524639602059844753)
                ·
                  refine ⟨749908143479701544883565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 999877524639602059844753 749908143479701544883565)
                  ·
                    refine ⟨281215553804888079331337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 749908143479701544883565 281215553804888079331337)
                    ·
                      rfl

theorem cell22_821498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_821498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821498 prefixEnd_821498 := by exact prefixLift 821498
  have htrace : WordTrace (prefixWord ++ tailWord_821498) baseStart_821498 baseEnd_821498 := by
    simpa [prefixWord, tailWord_821498, baseEnd_821498] using wordTrace_append hprefix tailTrace_821498
  have hstable : (prefixWord ++ tailWord_821498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821498).length < 2 ^ (prefixWord ++ tailWord_821498).sum := by decide
  have hdescent : baseEnd_821498 < baseStart_821498 := by decide
  rcases family_descends (prefixWord ++ tailWord_821498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821509 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_821509 : Nat := 118140960795 + 821509 * 2 ^ 59
def prefixEnd_821509 : Nat := 4983230072969 + 3 ^ 40 * 821509 * 2
def baseEnd_821509 : Nat := 281219319329687717306303

theorem tailTrace_821509 : CollatzResearch.WordTrace tailWord_821509 prefixEnd_821509 281219319329687717306303 := by
  unfold tailWord_821509
  simp only [CollatzResearch.WordTrace]
  refine ⟨29962894780820670412251581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19975263187213780274834387 29962894780820670412251581)
  ·
    refine ⟨11236085542807751404594343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29962894780820670412251581 11236085542807751404594343)
    ·
      refine ⟨16854128314211627106891515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11236085542807751404594343 16854128314211627106891515)
      ·
        refine ⟨25281192471317440660337273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16854128314211627106891515 25281192471317440660337273)
        ·
          refine ⟨18960894353488080495252955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25281192471317440660337273 18960894353488080495252955)
          ·
            refine ⟨28441341530232120742879433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18960894353488080495252955 28441341530232120742879433)
            ·
              refine ⟨21331006147674090557159575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28441341530232120742879433 21331006147674090557159575)
              ·
                refine ⟨31996509221511135835739363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21331006147674090557159575 31996509221511135835739363)
                ·
                  refine ⟨47994763832266703753609045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31996509221511135835739363 47994763832266703753609045)
                  ·
                    refine ⟨281219319329687717306303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 47994763832266703753609045 281219319329687717306303)
                    ·
                      rfl

theorem cell22_821509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_821509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821509 prefixEnd_821509 := by exact prefixLift 821509
  have htrace : WordTrace (prefixWord ++ tailWord_821509) baseStart_821509 baseEnd_821509 := by
    simpa [prefixWord, tailWord_821509, baseEnd_821509] using wordTrace_append hprefix tailTrace_821509
  have hstable : (prefixWord ++ tailWord_821509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821509).length < 2 ^ (prefixWord ++ tailWord_821509).sum := by decide
  have hdescent : baseEnd_821509 < baseStart_821509 := by decide
  rcases family_descends (prefixWord ++ tailWord_821509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821513 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 2, 4]
def baseStart_821513 : Nat := 118140960795 + 821513 * 2 ^ 59
def prefixEnd_821513 : Nat := 4983230072969 + 3 ^ 40 * 821513 * 2
def baseEnd_821513 : Nat := 281220688611433040206291

theorem tailTrace_821513 : CollatzResearch.WordTrace tailWord_821513 prefixEnd_821513 281220688611433040206291 := by
  unfold tailWord_821513
  simp only [CollatzResearch.WordTrace]
  refine ⟨29963040672806179095397193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19975360448537452730264795 29963040672806179095397193)
  ·
    refine ⟨22472280504604634321547895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29963040672806179095397193 22472280504604634321547895)
    ·
      refine ⟨33708420756906951482321843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22472280504604634321547895 33708420756906951482321843)
      ·
        refine ⟨50562631135360427223482765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33708420756906951482321843 50562631135360427223482765)
        ·
          refine ⟨18960986675760160208806037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50562631135360427223482765 18960986675760160208806037)
          ·
            refine ⟨888796250426257509787783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18960986675760160208806037 888796250426257509787783)
            ·
              refine ⟨1333194375639386264681675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888796250426257509787783 1333194375639386264681675)
              ·
                refine ⟨1999791563459079397022513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333194375639386264681675 1999791563459079397022513)
                ·
                  refine ⟨1499843672594309547766885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1999791563459079397022513 1499843672594309547766885)
                  ·
                    refine ⟨281220688611433040206291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1499843672594309547766885 281220688611433040206291)
                    ·
                      rfl

theorem cell22_821513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 4].length) (baseStart_821513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821513 prefixEnd_821513 := by exact prefixLift 821513
  have htrace : WordTrace (prefixWord ++ tailWord_821513) baseStart_821513 baseEnd_821513 := by
    simpa [prefixWord, tailWord_821513, baseEnd_821513] using wordTrace_append hprefix tailTrace_821513
  have hstable : (prefixWord ++ tailWord_821513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821513).length < 2 ^ (prefixWord ++ tailWord_821513).sum := by decide
  have hdescent : baseEnd_821513 < baseStart_821513 := by decide
  rcases family_descends (prefixWord ++ tailWord_821513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821549 : List Nat := [1, 5, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_821549 : Nat := 118140960795 + 821549 * 2 ^ 59
def prefixEnd_821549 : Nat := 4983230072969 + 3 ^ 40 * 821549 * 2
def baseEnd_821549 : Nat := 281233012147140946306181

theorem tailTrace_821549 : CollatzResearch.WordTrace tailWord_821549 prefixEnd_821549 281233012147140946306181 := by
  unfold tailWord_821549
  simp only [CollatzResearch.WordTrace]
  refine ⟨29964353700675757243707701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19976235800450504829138467 29964353700675757243707701)
  ·
    refine ⟨2809158159438352241597597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29964353700675757243707701 2809158159438352241597597)
    ·
      refine ⟨1053434309789382090599099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2809158159438352241597597 1053434309789382090599099)
      ·
        refine ⟨1580151464684073135898649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053434309789382090599099 1580151464684073135898649)
        ·
          refine ⟨1185113598513054851923987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1580151464684073135898649 1185113598513054851923987)
          ·
            refine ⟨1777670397769582277885981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185113598513054851923987 1777670397769582277885981)
            ·
              refine ⟨666626399163593354207243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1777670397769582277885981 666626399163593354207243)
              ·
                refine ⟨999939598745390031310865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666626399163593354207243 999939598745390031310865)
                ·
                  refine ⟨749954699059042523483149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 999939598745390031310865 749954699059042523483149)
                  ·
                    refine ⟨281233012147140946306181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 749954699059042523483149 281233012147140946306181)
                    ·
                      rfl

theorem cell22_821549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_821549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821549 prefixEnd_821549 := by exact prefixLift 821549
  have htrace : WordTrace (prefixWord ++ tailWord_821549) baseStart_821549 baseEnd_821549 := by
    simpa [prefixWord, tailWord_821549, baseEnd_821549] using wordTrace_append hprefix tailTrace_821549
  have hstable : (prefixWord ++ tailWord_821549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821549).length < 2 ^ (prefixWord ++ tailWord_821549).sum := by decide
  have hdescent : baseEnd_821549 < baseStart_821549 := by decide
  rcases family_descends (prefixWord ++ tailWord_821549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821631 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 6, 4]
def baseStart_821631 : Nat := 118140960795 + 821631 * 2 ^ 59
def prefixEnd_821631 : Nat := 4983230072969 + 3 ^ 40 * 821631 * 2
def baseEnd_821631 : Nat := 281261082422920065755929

theorem tailTrace_821631 : CollatzResearch.WordTrace tailWord_821631 prefixEnd_821631 281261082422920065755929 := by
  unfold tailWord_821631
  simp only [CollatzResearch.WordTrace]
  refine ⟨29967344486378685248192747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19978229657585790165461831 29967344486378685248192747)
  ·
    refine ⟨44951016729568027872289121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29967344486378685248192747 44951016729568027872289121)
    ·
      refine ⟨33713262547176020904216841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44951016729568027872289121 33713262547176020904216841)
      ·
        refine ⟨25284946910382015678162631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33713262547176020904216841 25284946910382015678162631)
        ·
          refine ⟨37927420365573023517243947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25284946910382015678162631 37927420365573023517243947)
          ·
            refine ⟨56891130548359535275865921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37927420365573023517243947 56891130548359535275865921)
            ·
              refine ⟨42668347911269651456899441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56891130548359535275865921 42668347911269651456899441)
              ·
                refine ⟨32001260933452238592674581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42668347911269651456899441 32001260933452238592674581)
                ·
                  refine ⟨1500059106255573684031621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32001260933452238592674581 1500059106255573684031621)
                  ·
                    refine ⟨281261082422920065755929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1500059106255573684031621 281261082422920065755929)
                    ·
                      rfl

theorem cell22_821631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_821631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821631 prefixEnd_821631 := by exact prefixLift 821631
  have htrace : WordTrace (prefixWord ++ tailWord_821631) baseStart_821631 baseEnd_821631 := by
    simpa [prefixWord, tailWord_821631, baseEnd_821631] using wordTrace_append hprefix tailTrace_821631
  have hstable : (prefixWord ++ tailWord_821631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821631).length < 2 ^ (prefixWord ++ tailWord_821631).sum := by decide
  have hdescent : baseEnd_821631 < baseStart_821631 := by decide
  rcases family_descends (prefixWord ++ tailWord_821631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821633 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 3, 5]
def baseStart_821633 : Nat := 118140960795 + 821633 * 2 ^ 59
def prefixEnd_821633 : Nat := 4983230072969 + 3 ^ 40 * 821633 * 2
def baseEnd_821633 : Nat := 281261767063792727205923

theorem tailTrace_821633 : CollatzResearch.WordTrace tailWord_821633 prefixEnd_821633 281261767063792727205923 := by
  unfold tailWord_821633
  simp only [CollatzResearch.WordTrace]
  refine ⟨29967417432371439589765553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19978278288247626393177035 29967417432371439589765553)
  ·
    refine ⟨22475563074278579692324165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29967417432371439589765553 22475563074278579692324165)
    ·
      refine ⟨4214168076427233692310781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22475563074278579692324165 4214168076427233692310781)
      ·
        refine ⟨1580313028660212634616543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4214168076427233692310781 1580313028660212634616543)
        ·
          refine ⟨2370469542990318951924815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580313028660212634616543 2370469542990318951924815)
          ·
            refine ⟨3555704314485478427887223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370469542990318951924815 3555704314485478427887223)
            ·
              refine ⟨5333556471728217641830835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3555704314485478427887223 5333556471728217641830835)
              ·
                refine ⟨8000334707592326462746253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5333556471728217641830835 8000334707592326462746253)
                ·
                  refine ⟨3000125515347122423529845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8000334707592326462746253 3000125515347122423529845)
                  ·
                    refine ⟨281261767063792727205923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3000125515347122423529845 281261767063792727205923)
                    ·
                      rfl

theorem cell22_821633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_821633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821633 prefixEnd_821633 := by exact prefixLift 821633
  have htrace : WordTrace (prefixWord ++ tailWord_821633) baseStart_821633 baseEnd_821633 := by
    simpa [prefixWord, tailWord_821633, baseEnd_821633] using wordTrace_append hprefix tailTrace_821633
  have hstable : (prefixWord ++ tailWord_821633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821633).length < 2 ^ (prefixWord ++ tailWord_821633).sum := by decide
  have hdescent : baseEnd_821633 < baseStart_821633 := by decide
  rcases family_descends (prefixWord ++ tailWord_821633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821652 : List Nat := [2, 4, 2, 1, 3, 1, 1, 4, 4]
def baseStart_821652 : Nat := 118140960795 + 821652 * 2 ^ 59
def prefixEnd_821652 : Nat := 4983230072969 + 3 ^ 40 * 821652 * 2
def baseEnd_821652 : Nat := 93756090384027670326955

theorem tailTrace_821652 : CollatzResearch.WordTrace tailWord_821652 prefixEnd_821652 93756090384027670326955 := by
  unfold tailWord_821652
  simp only [CollatzResearch.WordTrace]
  refine ⟨14984055209651302917353605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19978740279535070556471473 14984055209651302917353605)
  ·
    refine ⟨2809510351809619297003801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14984055209651302917353605 2809510351809619297003801)
    ·
      refine ⟨2107132763857214472752851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2809510351809619297003801 2107132763857214472752851)
      ·
        refine ⟨3160699145785821709129277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2107132763857214472752851 3160699145785821709129277)
        ·
          refine ⟨1185262179669683140923479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3160699145785821709129277 1185262179669683140923479)
          ·
            refine ⟨1777893269504524711385219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185262179669683140923479 1777893269504524711385219)
            ·
              refine ⟨2666839904256787067077829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777893269504524711385219 2666839904256787067077829)
              ·
                refine ⟨500032482048147575077093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2666839904256787067077829 500032482048147575077093)
                ·
                  refine ⟨93756090384027670326955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 500032482048147575077093 93756090384027670326955)
                  ·
                    rfl

theorem cell22_821652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_821652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821652 prefixEnd_821652 := by exact prefixLift 821652
  have htrace : WordTrace (prefixWord ++ tailWord_821652) baseStart_821652 baseEnd_821652 := by
    simpa [prefixWord, tailWord_821652, baseEnd_821652] using wordTrace_append hprefix tailTrace_821652
  have hstable : (prefixWord ++ tailWord_821652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821652).length < 2 ^ (prefixWord ++ tailWord_821652).sum := by decide
  have hdescent : baseEnd_821652 < baseStart_821652 := by decide
  rcases family_descends (prefixWord ++ tailWord_821652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821676 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_821676 : Nat := 118140960795 + 821676 * 2 ^ 59
def prefixEnd_821676 : Nat := 4983230072969 + 3 ^ 40 * 821676 * 2
def baseEnd_821676 : Nat := 281276486842554948380791

theorem tailTrace_821676 : CollatzResearch.WordTrace tailWord_821676 prefixEnd_821676 281276486842554948380791 := by
  unfold tailWord_821676
  simp only [CollatzResearch.WordTrace]
  refine ⟨14984492885607828966790441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19979323847477105289053921 14984492885607828966790441)
  ·
    refine ⟨11238369664205871725092831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14984492885607828966790441 11238369664205871725092831)
    ·
      refine ⟨16857554496308807587639247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11238369664205871725092831 16857554496308807587639247)
      ·
        refine ⟨25286331744463211381458871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16857554496308807587639247 25286331744463211381458871)
        ·
          refine ⟨37929497616694817072188307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25286331744463211381458871 37929497616694817072188307)
          ·
            refine ⟨56894246425042225608282461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37929497616694817072188307 56894246425042225608282461)
            ·
              refine ⟨21335342409390834603105923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56894246425042225608282461 21335342409390834603105923)
              ·
                refine ⟨32003013614086251904658885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21335342409390834603105923 32003013614086251904658885)
                ·
                  refine ⟨6000565052641172232123541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32003013614086251904658885 6000565052641172232123541)
                  ·
                    refine ⟨281276486842554948380791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6000565052641172232123541 281276486842554948380791)
                    ·
                      rfl

theorem cell22_821676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_821676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821676 prefixEnd_821676 := by exact prefixLift 821676
  have htrace : WordTrace (prefixWord ++ tailWord_821676) baseStart_821676 baseEnd_821676 := by
    simpa [prefixWord, tailWord_821676, baseEnd_821676] using wordTrace_append hprefix tailTrace_821676
  have hstable : (prefixWord ++ tailWord_821676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821676).length < 2 ^ (prefixWord ++ tailWord_821676).sum := by decide
  have hdescent : baseEnd_821676 < baseStart_821676 := by decide
  rcases family_descends (prefixWord ++ tailWord_821676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821697 : List Nat := [1, 2, 7, 1, 1, 1, 9]
def baseStart_821697 : Nat := 118140960795 + 821697 * 2 ^ 59
def prefixEnd_821697 : Nat := 4983230072969 + 3 ^ 40 * 821697 * 2
def baseEnd_821697 : Nat := 10417913910063625689101

theorem tailTrace_821697 : CollatzResearch.WordTrace tailWord_821697 prefixEnd_821697 10417913910063625689101 := by
  unfold tailWord_821697
  simp only [CollatzResearch.WordTrace]
  refine ⟨29969751704139578520095345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19979834469426385680063563 29969751704139578520095345)
  ·
    refine ⟨22477313778104683890071509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29969751704139578520095345 22477313778104683890071509)
    ·
      refine ⟨526812041674328528673551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 22477313778104683890071509 526812041674328528673551)
      ·
        refine ⟨790218062511492793010327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526812041674328528673551 790218062511492793010327)
        ·
          refine ⟨1185327093767239189515491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790218062511492793010327 1185327093767239189515491)
          ·
            refine ⟨1777990640650858784273237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185327093767239189515491 1777990640650858784273237)
            ·
              refine ⟨10417913910063625689101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1777990640650858784273237 10417913910063625689101)
              ·
                rfl

theorem cell22_821697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 9].length) (baseStart_821697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821697 prefixEnd_821697 := by exact prefixLift 821697
  have htrace : WordTrace (prefixWord ++ tailWord_821697) baseStart_821697 baseEnd_821697 := by
    simpa [prefixWord, tailWord_821697, baseEnd_821697] using wordTrace_append hprefix tailTrace_821697
  have hstable : (prefixWord ++ tailWord_821697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821697).length < 2 ^ (prefixWord ++ tailWord_821697).sum := by decide
  have hdescent : baseEnd_821697 < baseStart_821697 := by decide
  rcases family_descends (prefixWord ++ tailWord_821697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821746 : List Nat := [3, 2, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_821746 : Nat := 118140960795 + 821746 * 2 ^ 59
def prefixEnd_821746 : Nat := 4983230072969 + 3 ^ 40 * 821746 * 2
def baseEnd_821746 : Nat := 281300449273098099130577

theorem tailTrace_821746 : CollatzResearch.WordTrace tailWord_821746 prefixEnd_821746 281300449273098099130577 := by
  unfold tailWord_821746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7492884720240514972157273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19981025920641373259086061 7492884720240514972157273)
  ·
    refine ⟨5619663540180386229117955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7492884720240514972157273 5619663540180386229117955)
    ·
      refine ⟨8429495310270579343676933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5619663540180386229117955 8429495310270579343676933)
      ·
        refine ⟨1580530370675733626939425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8429495310270579343676933 1580530370675733626939425)
        ·
          refine ⟨1185397778006800220204569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1580530370675733626939425 1185397778006800220204569)
          ·
            refine ⟨889048333505100165153427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1185397778006800220204569 889048333505100165153427)
            ·
              refine ⟨1333572500257650247730141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889048333505100165153427 1333572500257650247730141)
              ·
                refine ⟨500089687596618842898803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1333572500257650247730141 500089687596618842898803)
                ·
                  refine ⟨750134531394928264348205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500089687596618842898803 750134531394928264348205)
                  ·
                    refine ⟨281300449273098099130577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 750134531394928264348205 281300449273098099130577)
                    ·
                      rfl

theorem cell22_821746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_821746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821746 prefixEnd_821746 := by exact prefixLift 821746
  have htrace : WordTrace (prefixWord ++ tailWord_821746) baseStart_821746 baseEnd_821746 := by
    simpa [prefixWord, tailWord_821746, baseEnd_821746] using wordTrace_append hprefix tailTrace_821746
  have hstable : (prefixWord ++ tailWord_821746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821746).length < 2 ^ (prefixWord ++ tailWord_821746).sum := by decide
  have hdescent : baseEnd_821746 < baseStart_821746 := by decide
  rcases family_descends (prefixWord ++ tailWord_821746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821785 : List Nat := [1, 2, 1, 2, 1, 1, 2, 7, 2, 3]
def baseStart_821785 : Nat := 118140960795 + 821785 * 2 ^ 59
def prefixEnd_821785 : Nat := 4983230072969 + 3 ^ 40 * 821785 * 2
def baseEnd_821785 : Nat := 281313799770114997405457

theorem tailTrace_821785 : CollatzResearch.WordTrace tailWord_821785 prefixEnd_821785 281313799770114997405457 := by
  unfold tailWord_821785
  simp only [CollatzResearch.WordTrace]
  refine ⟨29972961327820769549298809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19981974218547179699532539 29972961327820769549298809)
  ·
    refine ⟨22479720995865577161974107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29972961327820769549298809 22479720995865577161974107)
    ·
      refine ⟨33719581493798365742961161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22479720995865577161974107 33719581493798365742961161)
      ·
        refine ⟨25289686120348774307220871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33719581493798365742961161 25289686120348774307220871)
        ·
          refine ⟨37934529180523161460831307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25289686120348774307220871 37934529180523161460831307)
          ·
            refine ⟨56901793770784742191246961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37934529180523161460831307 56901793770784742191246961)
            ·
              refine ⟨42676345328088556643435221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56901793770784742191246961 42676345328088556643435221)
              ·
                refine ⟨1000226843627075546330513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42676345328088556643435221 1000226843627075546330513)
                ·
                  refine ⟨750170132720306659747885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1000226843627075546330513 750170132720306659747885)
                  ·
                    refine ⟨281313799770114997405457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 750170132720306659747885 281313799770114997405457)
                    ·
                      rfl

theorem cell22_821785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 3].length) (baseStart_821785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821785 prefixEnd_821785 := by exact prefixLift 821785
  have htrace : WordTrace (prefixWord ++ tailWord_821785) baseStart_821785 baseEnd_821785 := by
    simpa [prefixWord, tailWord_821785, baseEnd_821785] using wordTrace_append hprefix tailTrace_821785
  have hstable : (prefixWord ++ tailWord_821785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821785).length < 2 ^ (prefixWord ++ tailWord_821785).sum := by decide
  have hdescent : baseEnd_821785 < baseStart_821785 := by decide
  rcases family_descends (prefixWord ++ tailWord_821785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821877 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 7]
def baseStart_821877 : Nat := 118140960795 + 821877 * 2 ^ 59
def prefixEnd_821877 : Nat := 4983230072969 + 3 ^ 40 * 821877 * 2
def baseEnd_821877 : Nat := 93781764416752474701725

theorem tailTrace_821877 : CollatzResearch.WordTrace tailWord_821877 prefixEnd_821877 93781764416752474701725 := by
  unfold tailWord_821877
  simp only [CollatzResearch.WordTrace]
  refine ⟨29976316843487469261647885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19984211228991646174431923 29976316843487469261647885)
  ·
    refine ⟨11241118816307800973117957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29976316843487469261647885 11241118816307800973117957)
    ·
      refine ⟨2107709778057712682459617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11241118816307800973117957 2107709778057712682459617)
      ·
        refine ⟨1580782333543284511844713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2107709778057712682459617 1580782333543284511844713)
        ·
          refine ⟨1185586750157463383883535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1580782333543284511844713 1185586750157463383883535)
          ·
            refine ⟨1778380125236195075825303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185586750157463383883535 1778380125236195075825303)
            ·
              refine ⟨2667570187854292613737955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778380125236195075825303 2667570187854292613737955)
              ·
                refine ⟨4001355281781438920606933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667570187854292613737955 4001355281781438920606933)
                ·
                  refine ⟨93781764416752474701725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4001355281781438920606933 93781764416752474701725)
                  ·
                    rfl

theorem cell22_821877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_821877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821877 prefixEnd_821877 := by exact prefixLift 821877
  have htrace : WordTrace (prefixWord ++ tailWord_821877) baseStart_821877 baseEnd_821877 := by
    simpa [prefixWord, tailWord_821877, baseEnd_821877] using wordTrace_append hprefix tailTrace_821877
  have hstable : (prefixWord ++ tailWord_821877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821877).length < 2 ^ (prefixWord ++ tailWord_821877).sum := by decide
  have hdescent : baseEnd_821877 < baseStart_821877 := by decide
  rcases family_descends (prefixWord ++ tailWord_821877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821935 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 4, 4]
def baseStart_821935 : Nat := 118140960795 + 821935 * 2 ^ 59
def prefixEnd_821935 : Nat := 4983230072969 + 3 ^ 40 * 821935 * 2
def baseEnd_821935 : Nat := 281365147835564606154997

theorem tailTrace_821935 : CollatzResearch.WordTrace tailWord_821935 prefixEnd_821935 281365147835564606154997 := by
  unfold tailWord_821935
  simp only [CollatzResearch.WordTrace]
  refine ⟨29978432277277345167259259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19985621518184896778172839 29978432277277345167259259)
  ·
    refine ⟨44967648415916017750888889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29978432277277345167259259 44967648415916017750888889)
    ·
      refine ⟨33725736311937013313166667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44967648415916017750888889 33725736311937013313166667)
      ·
        refine ⟨50588604467905519969750001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33725736311937013313166667 50588604467905519969750001)
        ·
          refine ⟨37941453350929139977312501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50588604467905519969750001 37941453350929139977312501)
          ·
            refine ⟨3557011251649606872873047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37941453350929139977312501 3557011251649606872873047)
            ·
              refine ⟨5335516877474410309309571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3557011251649606872873047 5335516877474410309309571)
              ·
                refine ⟨8003275316211615463964357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335516877474410309309571 8003275316211615463964357)
                ·
                  refine ⟨1500614121789677899493317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8003275316211615463964357 1500614121789677899493317)
                  ·
                    refine ⟨281365147835564606154997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1500614121789677899493317 281365147835564606154997)
                    ·
                      rfl

theorem cell22_821935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_821935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821935 prefixEnd_821935 := by exact prefixLift 821935
  have htrace : WordTrace (prefixWord ++ tailWord_821935) baseStart_821935 baseEnd_821935 := by
    simpa [prefixWord, tailWord_821935, baseEnd_821935] using wordTrace_append hprefix tailTrace_821935
  have hstable : (prefixWord ++ tailWord_821935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821935).length < 2 ^ (prefixWord ++ tailWord_821935).sum := by decide
  have hdescent : baseEnd_821935 < baseStart_821935 := by decide
  rcases family_descends (prefixWord ++ tailWord_821935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821939 : List Nat := [1, 1, 1, 2, 3, 5, 3, 2, 4]
def baseStart_821939 : Nat := 118140960795 + 821939 * 2 ^ 59
def prefixEnd_821939 : Nat := 4983230072969 + 3 ^ 40 * 821939 * 2
def baseEnd_821939 : Nat := 93788839039103309684995

theorem tailTrace_821939 : CollatzResearch.WordTrace tailWord_821939 prefixEnd_821939 93788839039103309684995 := by
  unfold tailWord_821939
  simp only [CollatzResearch.WordTrace]
  refine ⟨29978578169262853850404871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19985718779508569233603247 29978578169262853850404871)
  ·
    refine ⟨44967867253894280775607307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29978578169262853850404871 44967867253894280775607307)
    ·
      refine ⟨67451800880841421163410961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44967867253894280775607307 67451800880841421163410961)
      ·
        refine ⟨50588850660631065872558221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67451800880841421163410961 50588850660631065872558221)
        ·
          refine ⟨18970818997736649702209333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50588850660631065872558221 18970818997736649702209333)
          ·
            refine ⟨1778514281037810909582125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18970818997736649702209333 1778514281037810909582125)
            ·
              refine ⟨666942855389179091093297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1778514281037810909582125 666942855389179091093297)
              ·
                refine ⟨500207141541884318319973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666942855389179091093297 500207141541884318319973)
                ·
                  refine ⟨93788839039103309684995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 500207141541884318319973 93788839039103309684995)
                  ·
                    rfl

theorem cell22_821939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 4].length) (baseStart_821939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_821939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_821939 prefixEnd_821939 := by exact prefixLift 821939
  have htrace : WordTrace (prefixWord ++ tailWord_821939) baseStart_821939 baseEnd_821939 := by
    simpa [prefixWord, tailWord_821939, baseEnd_821939] using wordTrace_append hprefix tailTrace_821939
  have hstable : (prefixWord ++ tailWord_821939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821939).length < 2 ^ (prefixWord ++ tailWord_821939).sum := by decide
  have hdescent : baseEnd_821939 < baseStart_821939 := by decide
  rcases family_descends (prefixWord ++ tailWord_821939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822010 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_822010 : Nat := 118140960795 + 822010 * 2 ^ 59
def prefixEnd_822010 : Nat := 4983230072969 + 3 ^ 40 * 822010 * 2
def baseEnd_822010 : Nat := 281390821868289410529767

theorem tailTrace_822010 : CollatzResearch.WordTrace tailWord_822010 prefixEnd_822010 281390821868289410529767 := by
  unfold tailWord_822010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7495291938001408244059871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19987445168003755317492989 7495291938001408244059871)
  ·
    refine ⟨11242937907002112366089807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7495291938001408244059871 11242937907002112366089807)
    ·
      refine ⟨16864406860503168549134711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11242937907002112366089807 16864406860503168549134711)
      ·
        refine ⟨25296610290754752823702067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16864406860503168549134711 25296610290754752823702067)
        ·
          refine ⟨37944915436132129235553101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25296610290754752823702067 37944915436132129235553101)
          ·
            refine ⟨14229343288549548463332413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37944915436132129235553101 14229343288549548463332413)
            ·
              refine ⟨5336003733206080673749655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14229343288549548463332413 5336003733206080673749655)
              ·
                refine ⟨8004005599809121010624483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5336003733206080673749655 8004005599809121010624483)
                ·
                  refine ⟨12006008399713681515936725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8004005599809121010624483 12006008399713681515936725)
                  ·
                    refine ⟨281390821868289410529767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12006008399713681515936725 281390821868289410529767)
                    ·
                      rfl

theorem cell22_822010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_822010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822010 prefixEnd_822010 := by exact prefixLift 822010
  have htrace : WordTrace (prefixWord ++ tailWord_822010) baseStart_822010 baseEnd_822010 := by
    simpa [prefixWord, tailWord_822010, baseEnd_822010] using wordTrace_append hprefix tailTrace_822010
  have hstable : (prefixWord ++ tailWord_822010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822010).length < 2 ^ (prefixWord ++ tailWord_822010).sum := by decide
  have hdescent : baseEnd_822010 < baseStart_822010 := by decide
  rcases family_descends (prefixWord ++ tailWord_822010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822012 : List Nat := [2, 2, 2, 1, 3, 2, 2, 3, 5]
def baseStart_822012 : Nat := 118140960795 + 822012 * 2 ^ 59
def prefixEnd_822012 : Nat := 4983230072969 + 3 ^ 40 * 822012 * 2
def baseEnd_822012 : Nat := 93797168836387357326587

theorem tailTrace_822012 : CollatzResearch.WordTrace tailWord_822012 prefixEnd_822012 93797168836387357326587 := by
  unfold tailWord_822012
  simp only [CollatzResearch.WordTrace]
  refine ⟨14990620348999193658906145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19987493798665591545208193 14990620348999193658906145)
  ·
    refine ⟨11242965261749395244179609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14990620348999193658906145 11242965261749395244179609)
    ·
      refine ⟨8432223946312046433134707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11242965261749395244179609 8432223946312046433134707)
      ·
        refine ⟨12648335919468069649702061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8432223946312046433134707 12648335919468069649702061)
        ·
          refine ⟨4743125969800526118638273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12648335919468069649702061 4743125969800526118638273)
          ·
            refine ⟨3557344477350394588978705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4743125969800526118638273 3557344477350394588978705)
            ·
              refine ⟨2668008358012795941734029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3557344477350394588978705 2668008358012795941734029)
              ·
                refine ⟨1000503134254798478150261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2668008358012795941734029 1000503134254798478150261)
                ·
                  refine ⟨93797168836387357326587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1000503134254798478150261 93797168836387357326587)
                  ·
                    rfl

theorem cell22_822012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_822012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822012 prefixEnd_822012 := by exact prefixLift 822012
  have htrace : WordTrace (prefixWord ++ tailWord_822012) baseStart_822012 baseEnd_822012 := by
    simpa [prefixWord, tailWord_822012, baseEnd_822012] using wordTrace_append hprefix tailTrace_822012
  have hstable : (prefixWord ++ tailWord_822012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822012).length < 2 ^ (prefixWord ++ tailWord_822012).sum := by decide
  have hdescent : baseEnd_822012 < baseStart_822012 := by decide
  rcases family_descends (prefixWord ++ tailWord_822012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822040 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 10]
def baseStart_822040 : Nat := 118140960795 + 822040 * 2 ^ 59
def prefixEnd_822040 : Nat := 4983230072969 + 3 ^ 40 * 822040 * 2
def baseEnd_822040 : Nat := 93800363827126444093225

theorem tailTrace_822040 : CollatzResearch.WordTrace tailWord_822040 prefixEnd_822040 93800363827126444093225 := by
  unfold tailWord_822040
  simp only [CollatzResearch.WordTrace]
  refine ⟨14991130970948474049915787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19988174627931298733221049 14991130970948474049915787)
  ·
    refine ⟨22486696456422711074873681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14991130970948474049915787 22486696456422711074873681)
    ·
      refine ⟨16865022342317033306155261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22486696456422711074873681 16865022342317033306155261)
      ·
        refine ⟨6324383378368887489808223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16865022342317033306155261 6324383378368887489808223)
        ·
          refine ⟨9486575067553331234712335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6324383378368887489808223 9486575067553331234712335)
          ·
            refine ⟨14229862601329996852068503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9486575067553331234712335 14229862601329996852068503)
            ·
              refine ⟨21344793901994995278102755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14229862601329996852068503 21344793901994995278102755)
              ·
                refine ⟨32017190852992492917154133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21344793901994995278102755 32017190852992492917154133)
                ·
                  refine ⟨93800363827126444093225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 32017190852992492917154133 93800363827126444093225)
                  ·
                    rfl

theorem cell22_822040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_822040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822040 prefixEnd_822040 := by exact prefixLift 822040
  have htrace : WordTrace (prefixWord ++ tailWord_822040) baseStart_822040 baseEnd_822040 := by
    simpa [prefixWord, tailWord_822040, baseEnd_822040] using wordTrace_append hprefix tailTrace_822040
  have hstable : (prefixWord ++ tailWord_822040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822040).length < 2 ^ (prefixWord ++ tailWord_822040).sum := by decide
  have hdescent : baseEnd_822040 < baseStart_822040 := by decide
  rcases family_descends (prefixWord ++ tailWord_822040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822087 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 2, 4]
def baseStart_822087 : Nat := 118140960795 + 822087 * 2 ^ 59
def prefixEnd_822087 : Nat := 4983230072969 + 3 ^ 40 * 822087 * 2
def baseEnd_822087 : Nat := 281417180541886876354531

theorem tailTrace_822087 : CollatzResearch.WordTrace tailWord_822087 prefixEnd_822087 281417180541886876354531 := by
  unfold tailWord_822087
  simp only [CollatzResearch.WordTrace]
  refine ⟨29983976172726675126792515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19989317448484450084528343 29983976172726675126792515)
  ·
    refine ⟨44975964259090012690188773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29983976172726675126792515 44975964259090012690188773)
    ·
      refine ⟨8432993298579377379410395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44975964259090012690188773 8432993298579377379410395)
      ·
        refine ⟨12649489947869066069115593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8432993298579377379410395 12649489947869066069115593)
        ·
          refine ⟨9487117460901799551836695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12649489947869066069115593 9487117460901799551836695)
          ·
            refine ⟨14230676191352699327755043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9487117460901799551836695 14230676191352699327755043)
            ·
              refine ⟨21346014287029048991632565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14230676191352699327755043 21346014287029048991632565)
              ·
                refine ⟨2001188839408973342965553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21346014287029048991632565 2001188839408973342965553)
                ·
                  refine ⟨1500891629556730007224165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2001188839408973342965553 1500891629556730007224165)
                  ·
                    refine ⟨281417180541886876354531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1500891629556730007224165 281417180541886876354531)
                    ·
                      rfl

theorem cell22_822087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_822087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822087 prefixEnd_822087 := by exact prefixLift 822087
  have htrace : WordTrace (prefixWord ++ tailWord_822087) baseStart_822087 baseEnd_822087 := by
    simpa [prefixWord, tailWord_822087, baseEnd_822087] using wordTrace_append hprefix tailTrace_822087
  have hstable : (prefixWord ++ tailWord_822087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822087).length < 2 ^ (prefixWord ++ tailWord_822087).sum := by decide
  have hdescent : baseEnd_822087 < baseStart_822087 := by decide
  rcases family_descends (prefixWord ++ tailWord_822087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822108 : List Nat := [2, 2, 4, 2, 1, 2, 3, 2, 4]
def baseStart_822108 : Nat := 118140960795 + 822108 * 2 ^ 59
def prefixEnd_822108 : Nat := 4983230072969 + 3 ^ 40 * 822108 * 2
def baseEnd_822108 : Nat := 93808123090349940526489

theorem tailTrace_822108 : CollatzResearch.WordTrace tailWord_822108 prefixEnd_822108 93808123090349940526489 := by
  unfold tailWord_822108
  simp only [CollatzResearch.WordTrace]
  refine ⟨14992371052825297856653489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19989828070433730475537985 14992371052825297856653489)
  ·
    refine ⟨11244278289618973392490117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14992371052825297856653489 11244278289618973392490117)
    ·
      refine ⟨2108302179303557511091897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11244278289618973392490117 2108302179303557511091897)
      ·
        refine ⟨1581226634477668133318923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2108302179303557511091897 1581226634477668133318923)
        ·
          refine ⟨2371839951716502199978385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581226634477668133318923 2371839951716502199978385)
          ·
            refine ⟨1778879963787376649983789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2371839951716502199978385 1778879963787376649983789)
            ·
              refine ⟨667079986420266243743921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1778879963787376649983789 667079986420266243743921)
              ·
                refine ⟨500309989815199682807941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667079986420266243743921 500309989815199682807941)
                ·
                  refine ⟨93808123090349940526489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 500309989815199682807941 93808123090349940526489)
                  ·
                    rfl

theorem cell22_822108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_822108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822108 prefixEnd_822108 := by exact prefixLift 822108
  have htrace : WordTrace (prefixWord ++ tailWord_822108) baseStart_822108 baseEnd_822108 := by
    simpa [prefixWord, tailWord_822108, baseEnd_822108] using wordTrace_append hprefix tailTrace_822108
  have hstable : (prefixWord ++ tailWord_822108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822108).length < 2 ^ (prefixWord ++ tailWord_822108).sum := by decide
  have hdescent : baseEnd_822108 < baseStart_822108 := by decide
  rcases family_descends (prefixWord ++ tailWord_822108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822207 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 3, 5]
def baseStart_822207 : Nat := 118140960795 + 822207 * 2 ^ 59
def prefixEnd_822207 : Nat := 4983230072969 + 3 ^ 40 * 822207 * 2
def baseEnd_822207 : Nat := 281458258994246563354163

theorem tailTrace_822207 : CollatzResearch.WordTrace tailWord_822207 prefixEnd_822207 281458258994246563354163 := by
  unfold tailWord_822207
  simp only [CollatzResearch.WordTrace]
  refine ⟨29988352932291935621160875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19992235288194623747440583 29988352932291935621160875)
  ·
    refine ⟨44982529398437903431741313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29988352932291935621160875 44982529398437903431741313)
    ·
      refine ⟨33736897048828427573805985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44982529398437903431741313 33736897048828427573805985)
      ·
        refine ⟨25302672786621320680354489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33736897048828427573805985 25302672786621320680354489)
        ·
          refine ⟨18977004589965990510265867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25302672786621320680354489 18977004589965990510265867)
          ·
            refine ⟨28465506884948985765398801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18977004589965990510265867 28465506884948985765398801)
            ·
              refine ⟨21349130163711739324049101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28465506884948985765398801 21349130163711739324049101)
              ·
                refine ⟨8005923811391902246518413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21349130163711739324049101 8005923811391902246518413)
                ·
                  refine ⟨3002221429271963342444405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8005923811391902246518413 3002221429271963342444405)
                  ·
                    refine ⟨281458258994246563354163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3002221429271963342444405 281458258994246563354163)
                    ·
                      rfl

theorem cell22_822207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_822207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822207 prefixEnd_822207 := by exact prefixLift 822207
  have htrace : WordTrace (prefixWord ++ tailWord_822207) baseStart_822207 baseEnd_822207 := by
    simpa [prefixWord, tailWord_822207, baseEnd_822207] using wordTrace_append hprefix tailTrace_822207
  have hstable : (prefixWord ++ tailWord_822207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822207).length < 2 ^ (prefixWord ++ tailWord_822207).sum := by decide
  have hdescent : baseEnd_822207 < baseStart_822207 := by decide
  rcases family_descends (prefixWord ++ tailWord_822207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822226 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 6]
def baseStart_822226 : Nat := 118140960795 + 822226 * 2 ^ 59
def prefixEnd_822226 : Nat := 4983230072969 + 3 ^ 40 * 822226 * 2
def baseEnd_822226 : Nat := 93821587694178949043035

theorem tailTrace_822226 : CollatzResearch.WordTrace tailWord_822226 prefixEnd_822226 93821587694178949043035 := by
  unfold tailWord_822226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7497261479805775466525633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19992697279482067910735021 7497261479805775466525633)
  ·
    refine ⟨5622946109854331599894225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7497261479805775466525633 5622946109854331599894225)
    ·
      refine ⟨4217209582390748699920669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5622946109854331599894225 4217209582390748699920669)
      ·
        refine ⟨1581453593396530762470251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4217209582390748699920669 1581453593396530762470251)
        ·
          refine ⟨2372180390094796143705377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581453593396530762470251 2372180390094796143705377)
          ·
            refine ⟨1779135292571097107779033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2372180390094796143705377 1779135292571097107779033)
            ·
              refine ⟨1334351469428322830834275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1779135292571097107779033 1334351469428322830834275)
              ·
                refine ⟨2001527204142484246251413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334351469428322830834275 2001527204142484246251413)
                ·
                  refine ⟨93821587694178949043035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2001527204142484246251413 93821587694178949043035)
                  ·
                    rfl

theorem cell22_822226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_822226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822226 prefixEnd_822226 := by exact prefixLift 822226
  have htrace : WordTrace (prefixWord ++ tailWord_822226) baseStart_822226 baseEnd_822226 := by
    simpa [prefixWord, tailWord_822226, baseEnd_822226] using wordTrace_append hprefix tailTrace_822226
  have hstable : (prefixWord ++ tailWord_822226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822226).length < 2 ^ (prefixWord ++ tailWord_822226).sum := by decide
  have hdescent : baseEnd_822226 < baseStart_822226 := by decide
  rcases family_descends (prefixWord ++ tailWord_822226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822267 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 1, 8]
def baseStart_822267 : Nat := 118140960795 + 822267 * 2 ^ 59
def prefixEnd_822267 : Nat := 4983230072969 + 3 ^ 40 * 822267 * 2
def baseEnd_822267 : Nat := 281478798220426406853979

theorem tailTrace_822267 : CollatzResearch.WordTrace tailWord_822267 prefixEnd_822267 281478798220426406853979 := by
  unfold tailWord_822267
  simp only [CollatzResearch.WordTrace]
  refine ⟨29990541312074565868345055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19993694208049710578896703 29990541312074565868345055)
  ·
    refine ⟨44985811968111848802517583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29990541312074565868345055 44985811968111848802517583)
    ·
      refine ⟨67478717952167773203776375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44985811968111848802517583 67478717952167773203776375)
      ·
        refine ⟨101218076928251659805664563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67478717952167773203776375 101218076928251659805664563)
        ·
          refine ⟨151827115392377489708496845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101218076928251659805664563 151827115392377489708496845)
          ·
            refine ⟨56935168272141558640686317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151827115392377489708496845 56935168272141558640686317)
            ·
              refine ⟨21350688102053084490257369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56935168272141558640686317 21350688102053084490257369)
              ·
                refine ⟨16013016076539813367693027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21350688102053084490257369 16013016076539813367693027)
                ·
                  refine ⟨24019524114809720051539541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16013016076539813367693027 24019524114809720051539541)
                  ·
                    refine ⟨281478798220426406853979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24019524114809720051539541 281478798220426406853979)
                    ·
                      rfl

theorem cell22_822267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_822267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822267 prefixEnd_822267 := by exact prefixLift 822267
  have htrace : WordTrace (prefixWord ++ tailWord_822267) baseStart_822267 baseEnd_822267 := by
    simpa [prefixWord, tailWord_822267, baseEnd_822267] using wordTrace_append hprefix tailTrace_822267
  have hstable : (prefixWord ++ tailWord_822267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822267).length < 2 ^ (prefixWord ++ tailWord_822267).sum := by decide
  have hdescent : baseEnd_822267 < baseStart_822267 := by decide
  rcases family_descends (prefixWord ++ tailWord_822267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822344 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 6]
def baseStart_822344 : Nat := 118140960795 + 822344 * 2 ^ 59
def prefixEnd_822344 : Nat := 4983230072969 + 3 ^ 40 * 822344 * 2
def baseEnd_822344 : Nat := 93835052298007957559581

theorem tailTrace_822344 : CollatzResearch.WordTrace tailWord_822344 prefixEnd_822344 93835052298007957559581 := by
  unfold tailWord_822344
  simp only [CollatzResearch.WordTrace]
  refine ⟨14996674866397804009449043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19995566488530405345932057 14996674866397804009449043)
  ·
    refine ⟨22495012299596706014173565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14996674866397804009449043 22495012299596706014173565)
    ·
      refine ⟨8435629612348764755315087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22495012299596706014173565 8435629612348764755315087)
      ·
        refine ⟨12653444418523147132972631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8435629612348764755315087 12653444418523147132972631)
        ·
          refine ⟨18980166627784720699458947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12653444418523147132972631 18980166627784720699458947)
          ·
            refine ⟨28470249941677081049188421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18980166627784720699458947 28470249941677081049188421)
            ·
              refine ⟨5338171864064452696722829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28470249941677081049188421 5338171864064452696722829)
              ·
                refine ⟨2001814449024169761271061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5338171864064452696722829 2001814449024169761271061)
                ·
                  refine ⟨93835052298007957559581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2001814449024169761271061 93835052298007957559581)
                  ·
                    rfl

theorem cell22_822344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_822344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822344 prefixEnd_822344 := by exact prefixLift 822344
  have htrace : WordTrace (prefixWord ++ tailWord_822344) baseStart_822344 baseEnd_822344 := by
    simpa [prefixWord, tailWord_822344, baseEnd_822344] using wordTrace_append hprefix tailTrace_822344
  have hstable : (prefixWord ++ tailWord_822344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822344).length < 2 ^ (prefixWord ++ tailWord_822344).sum := by decide
  have hdescent : baseEnd_822344 < baseStart_822344 := by decide
  rcases family_descends (prefixWord ++ tailWord_822344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822378 : List Nat := [3, 1, 3, 2, 2, 1, 1, 5, 4]
def baseStart_822378 : Nat := 118140960795 + 822378 * 2 ^ 59
def prefixEnd_822378 : Nat := 4983230072969 + 3 ^ 40 * 822378 * 2
def baseEnd_822378 : Nat := 93838931929619705776213

theorem tailTrace_822378 : CollatzResearch.WordTrace tailWord_822378 prefixEnd_822378 93838931929619705776213 := by
  unfold tailWord_822378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7498647453668107956408947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19996393209781621217090525 7498647453668107956408947)
  ·
    refine ⟨11247971180502161934613421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7498647453668107956408947 11247971180502161934613421)
    ·
      refine ⟨4217989192688310725480033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11247971180502161934613421 4217989192688310725480033)
      ·
        refine ⟨3163491894516233044110025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4217989192688310725480033 3163491894516233044110025)
        ·
          refine ⟨2372618920887174783082519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3163491894516233044110025 2372618920887174783082519)
          ·
            refine ⟨3558928381330762174623779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372618920887174783082519 3558928381330762174623779)
            ·
              refine ⟨5338392571996143261935669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3558928381330762174623779 5338392571996143261935669)
              ·
                refine ⟨500474303624638430806469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5338392571996143261935669 500474303624638430806469)
                ·
                  refine ⟨93838931929619705776213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 500474303624638430806469 93838931929619705776213)
                  ·
                    rfl

theorem cell22_822378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_822378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822378 prefixEnd_822378 := by exact prefixLift 822378
  have htrace : WordTrace (prefixWord ++ tailWord_822378) baseStart_822378 baseEnd_822378 := by
    simpa [prefixWord, tailWord_822378, baseEnd_822378] using wordTrace_append hprefix tailTrace_822378
  have hstable : (prefixWord ++ tailWord_822378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822378).length < 2 ^ (prefixWord ++ tailWord_822378).sum := by decide
  have hdescent : baseEnd_822378 < baseStart_822378 := by decide
  rcases family_descends (prefixWord ++ tailWord_822378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822393 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 4, 3]
def baseStart_822393 : Nat := 118140960795 + 822393 * 2 ^ 59
def prefixEnd_822393 : Nat := 4983230072969 + 3 ^ 40 * 822393 * 2
def baseEnd_822393 : Nat := 281521930595404078203593

theorem tailTrace_822393 : CollatzResearch.WordTrace tailWord_822393 prefixEnd_822393 281521930595404078203593 := by
  unfold tailWord_822393
  simp only [CollatzResearch.WordTrace]
  refine ⟨29995136909618089387431833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19996757939745392924954555 29995136909618089387431833)
  ·
    refine ⟨22496352682213567040573875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29995136909618089387431833 22496352682213567040573875)
    ·
      refine ⟨33744529023320350560860813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22496352682213567040573875 33744529023320350560860813)
      ·
        refine ⟨12654198383745131460322805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33744529023320350560860813 12654198383745131460322805)
        ·
          refine ⟨1186331098476106074405263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12654198383745131460322805 1186331098476106074405263)
          ·
            refine ⟨1779496647714159111607895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186331098476106074405263 1779496647714159111607895)
            ·
              refine ⟨2669244971571238667411843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779496647714159111607895 2669244971571238667411843)
              ·
                refine ⟨4003867457356858001117765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2669244971571238667411843 4003867457356858001117765)
                ·
                  refine ⟨750725148254410875209581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4003867457356858001117765 750725148254410875209581)
                  ·
                    refine ⟨281521930595404078203593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 750725148254410875209581 281521930595404078203593)
                    ·
                      rfl

theorem cell22_822393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 3].length) (baseStart_822393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822393 prefixEnd_822393 := by exact prefixLift 822393
  have htrace : WordTrace (prefixWord ++ tailWord_822393) baseStart_822393 baseEnd_822393 := by
    simpa [prefixWord, tailWord_822393, baseEnd_822393] using wordTrace_append hprefix tailTrace_822393
  have hstable : (prefixWord ++ tailWord_822393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822393).length < 2 ^ (prefixWord ++ tailWord_822393).sum := by decide
  have hdescent : baseEnd_822393 < baseStart_822393 := by decide
  rcases family_descends (prefixWord ++ tailWord_822393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822410 : List Nat := [3, 1, 2, 3, 1, 1, 5, 1, 2, 3]
def baseStart_822410 : Nat := 118140960795 + 822410 * 2 ^ 59
def prefixEnd_822410 : Nat := 4983230072969 + 3 ^ 40 * 822410 * 2
def baseEnd_822410 : Nat := 281527750042821700528541

theorem tailTrace_822410 : CollatzResearch.WordTrace tailWord_822410 prefixEnd_822410 281527750042821700528541 := by
  unfold tailWord_822410
  simp only [CollatzResearch.WordTrace]
  refine ⟨7498939237639125322700171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19997171300371000860533789 7498939237639125322700171)
  ·
    refine ⟨11248408856458687984050257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7498939237639125322700171 11248408856458687984050257)
    ·
      refine ⟨8436306642344015988037693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11248408856458687984050257 8436306642344015988037693)
      ·
        refine ⟨3163614990879005995514135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8436306642344015988037693 3163614990879005995514135)
        ·
          refine ⟨4745422486318508993271203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3163614990879005995514135 4745422486318508993271203)
          ·
            refine ⟨7118133729477763489906805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4745422486318508993271203 7118133729477763489906805)
            ·
              refine ⟨667325037138540327178763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7118133729477763489906805 667325037138540327178763)
              ·
                refine ⟨1000987555707810490768145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667325037138540327178763 1000987555707810490768145)
                ·
                  refine ⟨750740666780857868076109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1000987555707810490768145 750740666780857868076109)
                  ·
                    refine ⟨281527750042821700528541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 750740666780857868076109 281527750042821700528541)
                    ·
                      rfl

theorem cell22_822410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_822410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822410 prefixEnd_822410 := by exact prefixLift 822410
  have htrace : WordTrace (prefixWord ++ tailWord_822410) baseStart_822410 baseEnd_822410 := by
    simpa [prefixWord, tailWord_822410, baseEnd_822410] using wordTrace_append hprefix tailTrace_822410
  have hstable : (prefixWord ++ tailWord_822410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822410).length < 2 ^ (prefixWord ++ tailWord_822410).sum := by decide
  have hdescent : baseEnd_822410 < baseStart_822410 := by decide
  rcases family_descends (prefixWord ++ tailWord_822410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822419 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 2, 6]
def baseStart_822419 : Nat := 118140960795 + 822419 * 2 ^ 59
def prefixEnd_822419 : Nat := 4983230072969 + 3 ^ 40 * 822419 * 2
def baseEnd_822419 : Nat := 281530830926748677053513

theorem tailTrace_822419 : CollatzResearch.WordTrace tailWord_822419 prefixEnd_822419 281530830926748677053513 := by
  unfold tailWord_822419
  simp only [CollatzResearch.WordTrace]
  refine ⟨29996085207523895827878311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19997390138349263885252207 29996085207523895827878311)
  ·
    refine ⟨44994127811285843741817467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29996085207523895827878311 44994127811285843741817467)
    ·
      refine ⟨67491191716928765612726201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44994127811285843741817467 67491191716928765612726201)
      ·
        refine ⟨50618393787696574209544651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67491191716928765612726201 50618393787696574209544651)
        ·
          refine ⟨75927590681544861314316977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50618393787696574209544651 75927590681544861314316977)
          ·
            refine ⟨56945693011158645985737733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75927590681544861314316977 56945693011158645985737733)
            ·
              refine ⟨10677317439592246122325825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56945693011158645985737733 10677317439592246122325825)
              ·
                refine ⟨8007988079694184591744369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10677317439592246122325825 8007988079694184591744369)
                ·
                  refine ⟨6005991059770638443808277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8007988079694184591744369 6005991059770638443808277)
                  ·
                    refine ⟨281530830926748677053513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6005991059770638443808277 281530830926748677053513)
                    ·
                      rfl

theorem cell22_822419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_822419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822419 prefixEnd_822419 := by exact prefixLift 822419
  have htrace : WordTrace (prefixWord ++ tailWord_822419) baseStart_822419 baseEnd_822419 := by
    simpa [prefixWord, tailWord_822419, baseEnd_822419] using wordTrace_append hprefix tailTrace_822419
  have hstable : (prefixWord ++ tailWord_822419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822419).length < 2 ^ (prefixWord ++ tailWord_822419).sum := by decide
  have hdescent : baseEnd_822419 < baseStart_822419 := by decide
  rcases family_descends (prefixWord ++ tailWord_822419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822421 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 5, 3]
def baseStart_822421 : Nat := 118140960795 + 822421 * 2 ^ 59
def prefixEnd_822421 : Nat := 4983230072969 + 3 ^ 40 * 822421 * 2
def baseEnd_822421 : Nat := 281531515567621338503507

theorem tailTrace_822421 : CollatzResearch.WordTrace tailWord_822421 prefixEnd_822421 281531515567621338503507 := by
  unfold tailWord_822421
  simp only [CollatzResearch.WordTrace]
  refine ⟨29996158153516650169451117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19997438769011100112967411 29996158153516650169451117)
  ·
    refine ⟨11248559307568743813544169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29996158153516650169451117 11248559307568743813544169)
    ·
      refine ⟨8436419480676557860158127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11248559307568743813544169 8436419480676557860158127)
      ·
        refine ⟨12654629221014836790237191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8436419480676557860158127 12654629221014836790237191)
        ·
          refine ⟨18981943831522255185355787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12654629221014836790237191 18981943831522255185355787)
          ·
            refine ⟨28472915747283382778033681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18981943831522255185355787 28472915747283382778033681)
            ·
              refine ⟨21354686810462537083525261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28472915747283382778033681 21354686810462537083525261)
              ·
                refine ⟨8008007553923451406321973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21354686810462537083525261 8008007553923451406321973)
                ·
                  refine ⟨750750708180323569342685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8008007553923451406321973 750750708180323569342685)
                  ·
                    refine ⟨281531515567621338503507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 750750708180323569342685 281531515567621338503507)
                    ·
                      rfl

theorem cell22_822421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_822421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822421 prefixEnd_822421 := by exact prefixLift 822421
  have htrace : WordTrace (prefixWord ++ tailWord_822421) baseStart_822421 baseEnd_822421 := by
    simpa [prefixWord, tailWord_822421, baseEnd_822421] using wordTrace_append hprefix tailTrace_822421
  have hstable : (prefixWord ++ tailWord_822421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822421).length < 2 ^ (prefixWord ++ tailWord_822421).sum := by decide
  have hdescent : baseEnd_822421 < baseStart_822421 := by decide
  rcases family_descends (prefixWord ++ tailWord_822421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822423 : List Nat := [1, 1, 3, 3, 3, 3, 2, 6]
def baseStart_822423 : Nat := 118140960795 + 822423 * 2 ^ 59
def prefixEnd_822423 : Nat := 4983230072969 + 3 ^ 40 * 822423 * 2
def baseEnd_822423 : Nat := 31281355578721555550389

theorem tailTrace_822423 : CollatzResearch.WordTrace tailWord_822423 prefixEnd_822423 31281355578721555550389 := by
  unfold tailWord_822423
  simp only [CollatzResearch.WordTrace]
  refine ⟨29996231099509404511023923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19997487399672936340682615 29996231099509404511023923)
  ·
    refine ⟨44994346649264106766535885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29996231099509404511023923 44994346649264106766535885)
    ·
      refine ⟨16872879993474040037450957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44994346649264106766535885 16872879993474040037450957)
      ·
        refine ⟨6327329997552765014044109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16872879993474040037450957 6327329997552765014044109)
        ·
          refine ⟨2372748749082286880266541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6327329997552765014044109 2372748749082286880266541)
          ·
            refine ⟨889780780905857580099953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2372748749082286880266541 889780780905857580099953)
            ·
              refine ⟨667335585679393185074965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889780780905857580099953 667335585679393185074965)
              ·
                refine ⟨31281355578721555550389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 667335585679393185074965 31281355578721555550389)
                ·
                  rfl

theorem cell22_822423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 6].length) (baseStart_822423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822423 prefixEnd_822423 := by exact prefixLift 822423
  have htrace : WordTrace (prefixWord ++ tailWord_822423) baseStart_822423 baseEnd_822423 := by
    simpa [prefixWord, tailWord_822423, baseEnd_822423] using wordTrace_append hprefix tailTrace_822423
  have hstable : (prefixWord ++ tailWord_822423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822423).length < 2 ^ (prefixWord ++ tailWord_822423).sum := by decide
  have hdescent : baseEnd_822423 < baseStart_822423 := by decide
  rcases family_descends (prefixWord ++ tailWord_822423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822530 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 6]
def baseStart_822530 : Nat := 118140960795 + 822530 * 2 ^ 59
def prefixEnd_822530 : Nat := 4983230072969 + 3 ^ 40 * 822530 * 2
def baseEnd_822530 : Nat := 93856276165060462509391

theorem tailTrace_822530 : CollatzResearch.WordTrace tailWord_822530 prefixEnd_822530 93856276165060462509391 := by
  unfold tailWord_822530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500033427530440446292261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20000089140081174523446029 7500033427530440446292261)
  ·
    refine ⟨1406256267661957583679799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7500033427530440446292261 1406256267661957583679799)
    ·
      refine ⟨2109384401492936375519699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1406256267661957583679799 2109384401492936375519699)
      ·
        refine ⟨3164076602239404563279549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2109384401492936375519699 3164076602239404563279549)
        ·
          refine ⟨1186528725839776711229831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3164076602239404563279549 1186528725839776711229831)
          ·
            refine ⟨1779793088759665066844747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186528725839776711229831 1779793088759665066844747)
            ·
              refine ⟨2669689633139497600267121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779793088759665066844747 2669689633139497600267121)
              ·
                refine ⟨2002267224854623200200341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669689633139497600267121 2002267224854623200200341)
                ·
                  refine ⟨93856276165060462509391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2002267224854623200200341 93856276165060462509391)
                  ·
                    rfl

theorem cell22_822530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_822530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822530 prefixEnd_822530 := by exact prefixLift 822530
  have htrace : WordTrace (prefixWord ++ tailWord_822530) baseStart_822530 baseEnd_822530 := by
    simpa [prefixWord, tailWord_822530, baseEnd_822530] using wordTrace_append hprefix tailTrace_822530
  have hstable : (prefixWord ++ tailWord_822530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822530).length < 2 ^ (prefixWord ++ tailWord_822530).sum := by decide
  have hdescent : baseEnd_822530 < baseStart_822530 := by decide
  rcases family_descends (prefixWord ++ tailWord_822530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822590 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_822590 : Nat := 118140960795 + 822590 * 2 ^ 59
def prefixEnd_822590 : Nat := 4983230072969 + 3 ^ 40 * 822590 * 2
def baseEnd_822590 : Nat := 281589367721361231027989

theorem tailTrace_822590 : CollatzResearch.WordTrace tailWord_822590 prefixEnd_822590 281589367721361231027989 := by
  unfold tailWord_822590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3750290261238049004044153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20001548059936261354902149 3750290261238049004044153)
  ·
    refine ⟨2812717695928536753033115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3750290261238049004044153 2812717695928536753033115)
    ·
      refine ⟨4219076543892805129549673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2812717695928536753033115 4219076543892805129549673)
      ·
        refine ⟨3164307407919603847162255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4219076543892805129549673 3164307407919603847162255)
        ·
          refine ⟨4746461111879405770743383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164307407919603847162255 4746461111879405770743383)
          ·
            refine ⟨7119691667819108656115075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746461111879405770743383 7119691667819108656115075)
            ·
              refine ⟨10679537501728662984172613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7119691667819108656115075 10679537501728662984172613)
              ·
                refine ⟨2002413281574124309532365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10679537501728662984172613 2002413281574124309532365)
                ·
                  refine ⟨750904980590296616074637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2002413281574124309532365 750904980590296616074637)
                  ·
                    refine ⟨281589367721361231027989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 750904980590296616074637 281589367721361231027989)
                    ·
                      rfl

theorem cell22_822590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_822590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822590 prefixEnd_822590 := by exact prefixLift 822590
  have htrace : WordTrace (prefixWord ++ tailWord_822590) baseStart_822590 baseEnd_822590 := by
    simpa [prefixWord, tailWord_822590, baseEnd_822590] using wordTrace_append hprefix tailTrace_822590
  have hstable : (prefixWord ++ tailWord_822590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822590).length < 2 ^ (prefixWord ++ tailWord_822590).sum := by decide
  have hdescent : baseEnd_822590 < baseStart_822590 := by decide
  rcases family_descends (prefixWord ++ tailWord_822590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822598 : List Nat := [6, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_822598 : Nat := 118140960795 + 822598 * 2 ^ 59
def prefixEnd_822598 : Nat := 4983230072969 + 3 ^ 40 * 822598 * 2
def baseEnd_822598 : Nat := 93864035428283958942655

theorem tailTrace_822598 : CollatzResearch.WordTrace tailWord_822598 prefixEnd_822598 93864035428283958942655 := by
  unfold tailWord_822598
  simp only [CollatzResearch.WordTrace]
  refine ⟨937581683558606543707639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20001742582583606265762965 937581683558606543707639)
  ·
    refine ⟨1406372525337909815561459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 937581683558606543707639 1406372525337909815561459)
    ·
      refine ⟨2109558788006864723342189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1406372525337909815561459 2109558788006864723342189)
      ·
        refine ⟨791084545502574271253321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2109558788006864723342189 791084545502574271253321)
        ·
          refine ⟨593313409126930703439991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791084545502574271253321 593313409126930703439991)
          ·
            refine ⟨889970113690396055159987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593313409126930703439991 889970113690396055159987)
            ·
              refine ⟨1334955170535594082739981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889970113690396055159987 1334955170535594082739981)
              ·
                refine ⟨500608188950847781027493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1334955170535594082739981 500608188950847781027493)
                ·
                  refine ⟨93864035428283958942655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 500608188950847781027493 93864035428283958942655)
                  ·
                    rfl

theorem cell22_822598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_822598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822598 prefixEnd_822598 := by exact prefixLift 822598
  have htrace : WordTrace (prefixWord ++ tailWord_822598) baseStart_822598 baseEnd_822598 := by
    simpa [prefixWord, tailWord_822598, baseEnd_822598] using wordTrace_append hprefix tailTrace_822598
  have hstable : (prefixWord ++ tailWord_822598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822598).length < 2 ^ (prefixWord ++ tailWord_822598).sum := by decide
  have hdescent : baseEnd_822598 < baseStart_822598 := by decide
  rcases family_descends (prefixWord ++ tailWord_822598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822601 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 1, 7]
def baseStart_822601 : Nat := 118140960795 + 822601 * 2 ^ 59
def prefixEnd_822601 : Nat := 4983230072969 + 3 ^ 40 * 822601 * 2
def baseEnd_822601 : Nat := 281593133246160869002955

theorem tailTrace_822601 : CollatzResearch.WordTrace tailWord_822601 prefixEnd_822601 281593133246160869002955 := by
  unfold tailWord_822601
  simp only [CollatzResearch.WordTrace]
  refine ⟨30002723292864540911003657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20001815528576360607335771 30002723292864540911003657)
  ·
    refine ⟨22502042469648405683252743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30002723292864540911003657 22502042469648405683252743)
    ·
      refine ⟨33753063704472608524879115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22502042469648405683252743 33753063704472608524879115)
      ·
        refine ⟨50629595556708912787318673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33753063704472608524879115 50629595556708912787318673)
        ·
          refine ⟨37972196667531684590489005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50629595556708912787318673 37972196667531684590489005)
          ·
            refine ⟨14239573750324381721433377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37972196667531684590489005 14239573750324381721433377)
            ·
              refine ⟨10679680312743286291075033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14239573750324381721433377 10679680312743286291075033)
              ·
                refine ⟨8009760234557464718306275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10679680312743286291075033 8009760234557464718306275)
                ·
                  refine ⟨12014640351836197077459413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8009760234557464718306275 12014640351836197077459413)
                  ·
                    refine ⟨281593133246160869002955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12014640351836197077459413 281593133246160869002955)
                    ·
                      rfl

theorem cell22_822601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_822601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822601 prefixEnd_822601 := by exact prefixLift 822601
  have htrace : WordTrace (prefixWord ++ tailWord_822601) baseStart_822601 baseEnd_822601 := by
    simpa [prefixWord, tailWord_822601, baseEnd_822601] using wordTrace_append hprefix tailTrace_822601
  have hstable : (prefixWord ++ tailWord_822601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822601).length < 2 ^ (prefixWord ++ tailWord_822601).sum := by decide
  have hdescent : baseEnd_822601 < baseStart_822601 := by decide
  rcases family_descends (prefixWord ++ tailWord_822601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822624 : List Nat := [2, 1, 1, 3, 4, 2, 3, 2, 1, 3]
def baseStart_822624 : Nat := 118140960795 + 822624 * 2 ^ 59
def prefixEnd_822624 : Nat := 4983230072969 + 3 ^ 40 * 822624 * 2
def baseEnd_822624 : Nat := 281601006616196475677885

theorem tailTrace_822624 : CollatzResearch.WordTrace tailWord_822624 prefixEnd_822624 281601006616196475677885 := by
  unfold tailWord_822624
  simp only [CollatzResearch.WordTrace]
  refine ⟨15001781085890607919545463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20002374781187477226060617 15001781085890607919545463)
  ·
    refine ⟨22502671628835911879318195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15001781085890607919545463 22502671628835911879318195)
    ·
      refine ⟨33754007443253867818977293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22502671628835911879318195 33754007443253867818977293)
      ·
        refine ⟨12657752791220200432116485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33754007443253867818977293 12657752791220200432116485)
        ·
          refine ⟨2373328648353787581021841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12657752791220200432116485 2373328648353787581021841)
          ·
            refine ⟨1779996486265340685766381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2373328648353787581021841 1779996486265340685766381)
            ·
              refine ⟨667498682349502757162393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1779996486265340685766381 667498682349502757162393)
              ·
                refine ⟨500624011762127067871795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667498682349502757162393 500624011762127067871795)
                ·
                  refine ⟨750936017643190601807693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500624011762127067871795 750936017643190601807693)
                  ·
                    refine ⟨281601006616196475677885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 750936017643190601807693 281601006616196475677885)
                    ·
                      rfl

theorem cell22_822624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 1, 3].length) (baseStart_822624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822624 prefixEnd_822624 := by exact prefixLift 822624
  have htrace : WordTrace (prefixWord ++ tailWord_822624) baseStart_822624 baseEnd_822624 := by
    simpa [prefixWord, tailWord_822624, baseEnd_822624] using wordTrace_append hprefix tailTrace_822624
  have hstable : (prefixWord ++ tailWord_822624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822624).length < 2 ^ (prefixWord ++ tailWord_822624).sum := by decide
  have hdescent : baseEnd_822624 < baseStart_822624 := by decide
  rcases family_descends (prefixWord ++ tailWord_822624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822637 : List Nat := [1, 5, 1, 1, 1, 5, 2, 1, 5]
def baseStart_822637 : Nat := 118140960795 + 822637 * 2 ^ 59
def prefixEnd_822637 : Nat := 4983230072969 + 3 ^ 40 * 822637 * 2
def baseEnd_822637 : Nat := 93868485593956258367615

theorem tailTrace_822637 : CollatzResearch.WordTrace tailWord_822637 prefixEnd_822637 93868485593956258367615 := by
  unfold tailWord_822637
  simp only [CollatzResearch.WordTrace]
  refine ⟨30004036320734119059314165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20002690880489412706209443 30004036320734119059314165)
  ·
    refine ⟨2812878405068823661810703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30004036320734119059314165 2812878405068823661810703)
    ·
      refine ⟨4219317607603235492716055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2812878405068823661810703 4219317607603235492716055)
      ·
        refine ⟨6328976411404853239074083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4219317607603235492716055 6328976411404853239074083)
        ·
          refine ⟨9493464617107279858611125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6328976411404853239074083 9493464617107279858611125)
          ·
            refine ⟨890012307853807486744793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9493464617107279858611125 890012307853807486744793)
            ·
              refine ⟨667509230890355615058595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890012307853807486744793 667509230890355615058595)
              ·
                refine ⟨1001263846335533422587893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667509230890355615058595 1001263846335533422587893)
                ·
                  refine ⟨93868485593956258367615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1001263846335533422587893 93868485593956258367615)
                  ·
                    rfl

theorem cell22_822637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_822637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822637 prefixEnd_822637 := by exact prefixLift 822637
  have htrace : WordTrace (prefixWord ++ tailWord_822637) baseStart_822637 baseEnd_822637 := by
    simpa [prefixWord, tailWord_822637, baseEnd_822637] using wordTrace_append hprefix tailTrace_822637
  have hstable : (prefixWord ++ tailWord_822637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822637).length < 2 ^ (prefixWord ++ tailWord_822637).sum := by decide
  have hdescent : baseEnd_822637 < baseStart_822637 := by decide
  rcases family_descends (prefixWord ++ tailWord_822637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822663 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 3, 5]
def baseStart_822663 : Nat := 118140960795 + 822663 * 2 ^ 59
def prefixEnd_822663 : Nat := 4983230072969 + 3 ^ 40 * 822663 * 2
def baseEnd_822663 : Nat := 281614357113213373952765

theorem tailTrace_822663 : CollatzResearch.WordTrace tailWord_822663 prefixEnd_822663 281614357113213373952765 := by
  unfold tailWord_822663
  simp only [CollatzResearch.WordTrace]
  refine ⟨30004984618639925499760643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20003323079093283666507095 30004984618639925499760643)
  ·
    refine ⟨45007476927959888249640965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30004984618639925499760643 45007476927959888249640965)
    ·
      refine ⟨8438901923992479046807681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45007476927959888249640965 8438901923992479046807681)
      ·
        refine ⟨6329176442994359285105761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8438901923992479046807681 6329176442994359285105761)
        ·
          refine ⟨4746882332245769463829321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6329176442994359285105761 4746882332245769463829321)
          ·
            refine ⟨3560161749184327097871991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4746882332245769463829321 3560161749184327097871991)
            ·
              refine ⟨5340242623776490646807987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3560161749184327097871991 5340242623776490646807987)
              ·
                refine ⟨8010363935664735970211981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5340242623776490646807987 8010363935664735970211981)
                ·
                  refine ⟨3003886475874275988829493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8010363935664735970211981 3003886475874275988829493)
                  ·
                    refine ⟨281614357113213373952765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3003886475874275988829493 281614357113213373952765)
                    ·
                      rfl

theorem cell22_822663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_822663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822663 prefixEnd_822663 := by exact prefixLift 822663
  have htrace : WordTrace (prefixWord ++ tailWord_822663) baseStart_822663 baseEnd_822663 := by
    simpa [prefixWord, tailWord_822663, baseEnd_822663] using wordTrace_append hprefix tailTrace_822663
  have hstable : (prefixWord ++ tailWord_822663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822663).length < 2 ^ (prefixWord ++ tailWord_822663).sum := by decide
  have hdescent : baseEnd_822663 < baseStart_822663 := by decide
  rcases family_descends (prefixWord ++ tailWord_822663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822819 : List Nat := [1, 1, 1, 4, 5, 2, 1, 2, 1, 4]
def baseStart_822819 : Nat := 118140960795 + 822819 * 2 ^ 59
def prefixEnd_822819 : Nat := 4983230072969 + 3 ^ 40 * 822819 * 2
def baseEnd_822819 : Nat := 281667759101280967052287

theorem tailTrace_822819 : CollatzResearch.WordTrace tailWord_822819 prefixEnd_822819 281667759101280967052287 := by
  unfold tailWord_822819
  simp only [CollatzResearch.WordTrace]
  refine ⟨30010674406074764142439511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20007116270716509428293007 30010674406074764142439511)
  ·
    refine ⟨45016011609112146213659267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30010674406074764142439511 45016011609112146213659267)
    ·
      refine ⟨67524017413668219320488901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45016011609112146213659267 67524017413668219320488901)
      ·
        refine ⟨12660753265062791122591669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67524017413668219320488901 12660753265062791122591669)
        ·
          refine ⟨1186945618599636667742969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12660753265062791122591669 1186945618599636667742969)
          ·
            refine ⟨890209213949727500807227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1186945618599636667742969 890209213949727500807227)
            ·
              refine ⟨1335313820924591251210841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890209213949727500807227 1335313820924591251210841)
              ·
                refine ⟨1001485365693443438408131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335313820924591251210841 1001485365693443438408131)
                ·
                  refine ⟨1502228048540165157612197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001485365693443438408131 1502228048540165157612197)
                  ·
                    refine ⟨281667759101280967052287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1502228048540165157612197 281667759101280967052287)
                    ·
                      rfl

theorem cell22_822819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 4].length) (baseStart_822819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822819 prefixEnd_822819 := by exact prefixLift 822819
  have htrace : WordTrace (prefixWord ++ tailWord_822819) baseStart_822819 baseEnd_822819 := by
    simpa [prefixWord, tailWord_822819, baseEnd_822819] using wordTrace_append hprefix tailTrace_822819
  have hstable : (prefixWord ++ tailWord_822819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822819).length < 2 ^ (prefixWord ++ tailWord_822819).sum := by decide
  have hdescent : baseEnd_822819 < baseStart_822819 := by decide
  rcases family_descends (prefixWord ++ tailWord_822819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822845 : List Nat := [1, 4, 1, 3, 3, 10]
def baseStart_822845 : Nat := 118140960795 + 822845 * 2 ^ 59
def prefixEnd_822845 : Nat := 4983230072969 + 3 ^ 40 * 822845 * 2
def baseEnd_822845 : Nat := 3477489622625006986447

theorem tailTrace_822845 : CollatzResearch.WordTrace tailWord_822845 prefixEnd_822845 3477489622625006986447 := by
  unfold tailWord_822845
  simp only [CollatzResearch.WordTrace]
  refine ⟨30011622703980570582885989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20007748469320380388590659 30011622703980570582885989)
  ·
    refine ⟨5627179256996356984291123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30011622703980570582885989 5627179256996356984291123)
    ·
      refine ⟨8440768885494535476436685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5627179256996356984291123 8440768885494535476436685)
      ·
        refine ⟨3165288332060450803663757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8440768885494535476436685 3165288332060450803663757)
        ·
          refine ⟨1186983124522669051373909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3165288332060450803663757 1186983124522669051373909)
          ·
            refine ⟨3477489622625006986447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1186983124522669051373909 3477489622625006986447)
            ·
              rfl

theorem cell22_822845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 10].length) (baseStart_822845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822845 prefixEnd_822845 := by exact prefixLift 822845
  have htrace : WordTrace (prefixWord ++ tailWord_822845) baseStart_822845 baseEnd_822845 := by
    simpa [prefixWord, tailWord_822845, baseEnd_822845] using wordTrace_append hprefix tailTrace_822845
  have hstable : (prefixWord ++ tailWord_822845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822845).length < 2 ^ (prefixWord ++ tailWord_822845).sum := by decide
  have hdescent : baseEnd_822845 < baseStart_822845 := by decide
  rcases family_descends (prefixWord ++ tailWord_822845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822849 : List Nat := [1, 2, 5, 1, 1, 1, 4, 2, 2, 3]
def baseStart_822849 : Nat := 118140960795 + 822849 * 2 ^ 59
def prefixEnd_822849 : Nat := 4983230072969 + 3 ^ 40 * 822849 * 2
def baseEnd_822849 : Nat := 281678028714370888802195

theorem tailTrace_822849 : CollatzResearch.WordTrace tailWord_822849 prefixEnd_822849 281678028714370888802195 := by
  unfold tailWord_822849
  simp only [CollatzResearch.WordTrace]
  refine ⟨30011768595966079266031601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20007845730644052844021067 30011768595966079266031601)
  ·
    refine ⟨22508826446974559449523701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30011768595966079266031601 22508826446974559449523701)
    ·
      refine ⟨2110202479403864948392847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22508826446974559449523701 2110202479403864948392847)
      ·
        refine ⟨3165303719105797422589271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2110202479403864948392847 3165303719105797422589271)
        ·
          refine ⟨4747955578658696133883907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165303719105797422589271 4747955578658696133883907)
          ·
            refine ⟨7121933367988044200825861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747955578658696133883907 7121933367988044200825861)
            ·
              refine ⟨1335362506497758287654849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7121933367988044200825861 1335362506497758287654849)
              ·
                refine ⟨1001521879873318715741137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335362506497758287654849 1001521879873318715741137)
                ·
                  refine ⟨751141409904989036805853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1001521879873318715741137 751141409904989036805853)
                  ·
                    refine ⟨281678028714370888802195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 751141409904989036805853 281678028714370888802195)
                    ·
                      rfl

theorem cell22_822849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_822849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822849 prefixEnd_822849 := by exact prefixLift 822849
  have htrace : WordTrace (prefixWord ++ tailWord_822849) baseStart_822849 baseEnd_822849 := by
    simpa [prefixWord, tailWord_822849, baseEnd_822849] using wordTrace_append hprefix tailTrace_822849
  have hstable : (prefixWord ++ tailWord_822849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822849).length < 2 ^ (prefixWord ++ tailWord_822849).sum := by decide
  have hdescent : baseEnd_822849 < baseStart_822849 := by decide
  rcases family_descends (prefixWord ++ tailWord_822849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822905 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 4, 5]
def baseStart_822905 : Nat := 118140960795 + 822905 * 2 ^ 59
def prefixEnd_822905 : Nat := 4983230072969 + 3 ^ 40 * 822905 * 2
def baseEnd_822905 : Nat := 281697198658805409402023

theorem tailTrace_822905 : CollatzResearch.WordTrace tailWord_822905 prefixEnd_822905 281697198658805409402023 := by
  unfold tailWord_822905
  simp only [CollatzResearch.WordTrace]
  refine ⟨30013811083763200830070169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20009207389175467220046779 30013811083763200830070169)
  ·
    refine ⟨22510358312822400622552627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30013811083763200830070169 22510358312822400622552627)
    ·
      refine ⟨33765537469233600933828941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22510358312822400622552627 33765537469233600933828941)
      ·
        refine ⟨12662076550962600350185853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33765537469233600933828941 12662076550962600350185853)
        ·
          refine ⟨4748278706610975131319695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12662076550962600350185853 4748278706610975131319695)
          ·
            refine ⟨7122418059916462696979543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4748278706610975131319695 7122418059916462696979543)
            ·
              refine ⟨10683627089874694045469315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7122418059916462696979543 10683627089874694045469315)
              ·
                refine ⟨16025440634812041068203973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10683627089874694045469315 16025440634812041068203973)
                ·
                  refine ⟨3004770119027257700288245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16025440634812041068203973 3004770119027257700288245)
                  ·
                    refine ⟨281697198658805409402023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3004770119027257700288245 281697198658805409402023)
                    ·
                      rfl

theorem cell22_822905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_822905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822905 prefixEnd_822905 := by exact prefixLift 822905
  have htrace : WordTrace (prefixWord ++ tailWord_822905) baseStart_822905 baseEnd_822905 := by
    simpa [prefixWord, tailWord_822905, baseEnd_822905] using wordTrace_append hprefix tailTrace_822905
  have hstable : (prefixWord ++ tailWord_822905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822905).length < 2 ^ (prefixWord ++ tailWord_822905).sum := by decide
  have hdescent : baseEnd_822905 < baseStart_822905 := by decide
  rcases family_descends (prefixWord ++ tailWord_822905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822922 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_822922 : Nat := 118140960795 + 822922 * 2 ^ 59
def prefixEnd_822922 : Nat := 4983230072969 + 3 ^ 40 * 822922 * 2
def baseEnd_822922 : Nat := 281703018106223031726971

theorem tailTrace_822922 : CollatzResearch.WordTrace tailWord_822922 prefixEnd_822922 281703018106223031726971 := by
  unfold tailWord_822922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7503607781175403183359755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20009620749801075155626013 7503607781175403183359755)
  ·
    refine ⟨11255411671763104775039633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7503607781175403183359755 11255411671763104775039633)
    ·
      refine ⟨8441558753822328581279725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11255411671763104775039633 8441558753822328581279725)
      ·
        refine ⟨3165584532683373217979897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8441558753822328581279725 3165584532683373217979897)
        ·
          refine ⟨2374188399512529913484923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3165584532683373217979897 2374188399512529913484923)
          ·
            refine ⟨3561282599268794870227385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374188399512529913484923 3561282599268794870227385)
            ·
              refine ⟨2670961949451596152670539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3561282599268794870227385 2670961949451596152670539)
              ·
                refine ⟨4006442924177394229005809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670961949451596152670539 4006442924177394229005809)
                ·
                  refine ⟨3004832193133045671754357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4006442924177394229005809 3004832193133045671754357)
                  ·
                    refine ⟨281703018106223031726971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3004832193133045671754357 281703018106223031726971)
                    ·
                      rfl

theorem cell22_822922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_822922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822922 prefixEnd_822922 := by exact prefixLift 822922
  have htrace : WordTrace (prefixWord ++ tailWord_822922) baseStart_822922 baseEnd_822922 := by
    simpa [prefixWord, tailWord_822922, baseEnd_822922] using wordTrace_append hprefix tailTrace_822922
  have hstable : (prefixWord ++ tailWord_822922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822922).length < 2 ^ (prefixWord ++ tailWord_822922).sum := by decide
  have hdescent : baseEnd_822922 < baseStart_822922 := by decide
  rcases family_descends (prefixWord ++ tailWord_822922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822984 : List Nat := [2, 1, 3, 1, 2, 2, 3, 3, 2, 3]
def baseStart_822984 : Nat := 118140960795 + 822984 * 2 ^ 59
def prefixEnd_822984 : Nat := 4983230072969 + 3 ^ 40 * 822984 * 2
def baseEnd_822984 : Nat := 281724241973275536676781

theorem tailTrace_822984 : CollatzResearch.WordTrace tailWord_822984 prefixEnd_822984 281724241973275536676781 := by
  unfold tailWord_822984
  simp only [CollatzResearch.WordTrace]
  refine ⟨15008346225238498661098003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20011128300317998214797337 15008346225238498661098003)
  ·
    refine ⟨22512519337857747991647005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15008346225238498661098003 22512519337857747991647005)
    ·
      refine ⟨8442194751696655496867627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22512519337857747991647005 8442194751696655496867627)
      ·
        refine ⟨12663292127544983245301441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8442194751696655496867627 12663292127544983245301441)
        ·
          refine ⟨9497469095658737433976081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12663292127544983245301441 9497469095658737433976081)
          ·
            refine ⟨7123101821744053075482061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9497469095658737433976081 7123101821744053075482061)
            ·
              refine ⟨2671163183154019903305773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7123101821744053075482061 2671163183154019903305773)
              ·
                refine ⟨1001686193682757463739665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2671163183154019903305773 1001686193682757463739665)
                ·
                  refine ⟨751264645262068097804749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1001686193682757463739665 751264645262068097804749)
                  ·
                    refine ⟨281724241973275536676781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 751264645262068097804749 281724241973275536676781)
                    ·
                      rfl

theorem cell22_822984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_822984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822984 prefixEnd_822984 := by exact prefixLift 822984
  have htrace : WordTrace (prefixWord ++ tailWord_822984) baseStart_822984 baseEnd_822984 := by
    simpa [prefixWord, tailWord_822984, baseEnd_822984] using wordTrace_append hprefix tailTrace_822984
  have hstable : (prefixWord ++ tailWord_822984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822984).length < 2 ^ (prefixWord ++ tailWord_822984).sum := by decide
  have hdescent : baseEnd_822984 < baseStart_822984 := by decide
  rcases family_descends (prefixWord ++ tailWord_822984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822988 : List Nat := [2, 2, 1, 5, 3, 1, 1, 2, 1, 4]
def baseStart_822988 : Nat := 118140960795 + 822988 * 2 ^ 59
def prefixEnd_822988 : Nat := 4983230072969 + 3 ^ 40 * 822988 * 2
def baseEnd_822988 : Nat := 281725611255020859576769

theorem tailTrace_822988 : CollatzResearch.WordTrace tailWord_822988 prefixEnd_822988 281725611255020859576769 := by
  unfold tailWord_822988
  simp only [CollatzResearch.WordTrace]
  refine ⟨15008419171231253002670809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20011225561641670670227745 15008419171231253002670809)
  ·
    refine ⟨11256314378423439752003107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15008419171231253002670809 11256314378423439752003107)
    ·
      refine ⟨16884471567635159628004661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11256314378423439752003107 16884471567635159628004661)
      ·
        refine ⟨1582919209465796215125437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16884471567635159628004661 1582919209465796215125437)
        ·
          refine ⟨593594703549673580672039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1582919209465796215125437 593594703549673580672039)
          ·
            refine ⟨890392055324510371008059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593594703549673580672039 890392055324510371008059)
            ·
              refine ⟨1335588082986765556512089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890392055324510371008059 1335588082986765556512089)
              ·
                refine ⟨1001691062240074167384067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335588082986765556512089 1001691062240074167384067)
                ·
                  refine ⟨1502536593360111251076101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001691062240074167384067 1502536593360111251076101)
                  ·
                    refine ⟨281725611255020859576769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1502536593360111251076101 281725611255020859576769)
                    ·
                      rfl

theorem cell22_822988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_822988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_822988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_822988 prefixEnd_822988 := by exact prefixLift 822988
  have htrace : WordTrace (prefixWord ++ tailWord_822988) baseStart_822988 baseEnd_822988 := by
    simpa [prefixWord, tailWord_822988, baseEnd_822988] using wordTrace_append hprefix tailTrace_822988
  have hstable : (prefixWord ++ tailWord_822988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822988).length < 2 ^ (prefixWord ++ tailWord_822988).sum := by decide
  have hdescent : baseEnd_822988 < baseStart_822988 := by decide
  rcases family_descends (prefixWord ++ tailWord_822988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823063 : List Nat := [1, 1, 3, 4, 2, 2, 2, 3, 1, 3]
def baseStart_823063 : Nat := 118140960795 + 823063 * 2 ^ 59
def prefixEnd_823063 : Nat := 4983230072969 + 3 ^ 40 * 823063 * 2
def baseEnd_823063 : Nat := 281751285287745663951539

theorem tailTrace_823063 : CollatzResearch.WordTrace tailWord_823063 prefixEnd_823063 281751285287745663951539 := by
  unfold tailWord_823063
  simp only [CollatzResearch.WordTrace]
  refine ⟨30019573817190793814321843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20013049211460529209547895 30019573817190793814321843)
  ·
    refine ⟨45029360725786190721482765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30019573817190793814321843 45029360725786190721482765)
    ·
      refine ⟨16886010272169821520556037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45029360725786190721482765 16886010272169821520556037)
      ·
        refine ⟨3166126926031841535104257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16886010272169821520556037 3166126926031841535104257)
        ·
          refine ⟨2374595194523881151328193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3166126926031841535104257 2374595194523881151328193)
          ·
            refine ⟨1780946395892910863496145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2374595194523881151328193 1780946395892910863496145)
            ·
              refine ⟨1335709796919683147622109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780946395892910863496145 1335709796919683147622109)
              ·
                refine ⟨500891173844881180358291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1335709796919683147622109 500891173844881180358291)
                ·
                  refine ⟨751336760767321770537437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500891173844881180358291 751336760767321770537437)
                  ·
                    refine ⟨281751285287745663951539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 751336760767321770537437 281751285287745663951539)
                    ·
                      rfl

theorem cell22_823063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_823063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823063 prefixEnd_823063 := by exact prefixLift 823063
  have htrace : WordTrace (prefixWord ++ tailWord_823063) baseStart_823063 baseEnd_823063 := by
    simpa [prefixWord, tailWord_823063, baseEnd_823063] using wordTrace_append hprefix tailTrace_823063
  have hstable : (prefixWord ++ tailWord_823063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823063).length < 2 ^ (prefixWord ++ tailWord_823063).sum := by decide
  have hdescent : baseEnd_823063 < baseStart_823063 := by decide
  rcases family_descends (prefixWord ++ tailWord_823063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823076 : List Nat := [2, 3, 1, 3, 2, 3, 1, 2, 5]
def baseStart_823076 : Nat := 118140960795 + 823076 * 2 ^ 59
def prefixEnd_823076 : Nat := 4983230072969 + 3 ^ 40 * 823076 * 2
def baseEnd_823076 : Nat := 93918578484472654458833

theorem tailTrace_823076 : CollatzResearch.WordTrace tailWord_823076 prefixEnd_823076 93918578484472654458833 := by
  unfold tailWord_823076
  simp only [CollatzResearch.WordTrace]
  refine ⟨15010023983071848517272541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20013365310762464689696721 15010023983071848517272541)
  ·
    refine ⟨5628758993651943193977203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15010023983071848517272541 5628758993651943193977203)
    ·
      refine ⟨8443138490477914790965805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5628758993651943193977203 8443138490477914790965805)
      ·
        refine ⟨3166176933929218046612177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8443138490477914790965805 3166176933929218046612177)
        ·
          refine ⟨2374632700446913534959133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3166176933929218046612177 2374632700446913534959133)
          ·
            refine ⟨890487262667592575609675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2374632700446913534959133 890487262667592575609675)
            ·
              refine ⟨1335730894001388863414513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890487262667592575609675 1335730894001388863414513)
              ·
                refine ⟨1001798170501041647560885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335730894001388863414513 1001798170501041647560885)
                ·
                  refine ⟨93918578484472654458833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1001798170501041647560885 93918578484472654458833)
                  ·
                    rfl

theorem cell22_823076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_823076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823076 prefixEnd_823076 := by exact prefixLift 823076
  have htrace : WordTrace (prefixWord ++ tailWord_823076) baseStart_823076 baseEnd_823076 := by
    simpa [prefixWord, tailWord_823076, baseEnd_823076] using wordTrace_append hprefix tailTrace_823076
  have hstable : (prefixWord ++ tailWord_823076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823076).length < 2 ^ (prefixWord ++ tailWord_823076).sum := by decide
  have hdescent : baseEnd_823076 < baseStart_823076 := by decide
  rcases family_descends (prefixWord ++ tailWord_823076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823121 : List Nat := [1, 2, 2, 1, 5, 1, 3, 3, 4]
def baseStart_823121 : Nat := 118140960795 + 823121 * 2 ^ 59
def prefixEnd_823121 : Nat := 4983230072969 + 3 ^ 40 * 823121 * 2
def baseEnd_823121 : Nat := 93923713291017615333787

theorem tailTrace_823121 : CollatzResearch.WordTrace tailWord_823121 prefixEnd_823121 93923713291017615333787 := by
  unfold tailWord_823121
  simp only [CollatzResearch.WordTrace]
  refine ⟨30021689250980669719933217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20014459500653779813288811 30021689250980669719933217)
  ·
    refine ⟨22516266938235502289949913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30021689250980669719933217 22516266938235502289949913)
    ·
      refine ⟨16887200203676626717462435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22516266938235502289949913 16887200203676626717462435)
      ·
        refine ⟨25330800305514940076193653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16887200203676626717462435 25330800305514940076193653)
        ·
          refine ⟨2374762528642025632143155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25330800305514940076193653 2374762528642025632143155)
          ·
            refine ⟨3562143792963038448214733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374762528642025632143155 3562143792963038448214733)
            ·
              refine ⟨1335803922361139418080525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3562143792963038448214733 1335803922361139418080525)
              ·
                refine ⟨500926470885427281780197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1335803922361139418080525 500926470885427281780197)
                ·
                  refine ⟨93923713291017615333787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 500926470885427281780197 93923713291017615333787)
                  ·
                    rfl

theorem cell22_823121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 4].length) (baseStart_823121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823121 prefixEnd_823121 := by exact prefixLift 823121
  have htrace : WordTrace (prefixWord ++ tailWord_823121) baseStart_823121 baseEnd_823121 := by
    simpa [prefixWord, tailWord_823121, baseEnd_823121] using wordTrace_append hprefix tailTrace_823121
  have hstable : (prefixWord ++ tailWord_823121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823121).length < 2 ^ (prefixWord ++ tailWord_823121).sum := by decide
  have hdescent : baseEnd_823121 < baseStart_823121 := by decide
  rcases family_descends (prefixWord ++ tailWord_823121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823166 : List Nat := [4, 2, 3, 1, 1, 1, 2, 8]
def baseStart_823166 : Nat := 118140960795 + 823166 * 2 ^ 59
def prefixEnd_823166 : Nat := 4983230072969 + 3 ^ 40 * 823166 * 2
def baseEnd_823166 : Nat := 31309616032520858736247

theorem tailTrace_823166 : CollatzResearch.WordTrace tailWord_823166 prefixEnd_823166 31309616032520858736247 := by
  unfold tailWord_823166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3752916316977205300665169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20015553690545094936880901 3752916316977205300665169)
  ·
    refine ⟨2814687237732903975498877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3752916316977205300665169 2814687237732903975498877)
    ·
      refine ⟨1055507714149838990812079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2814687237732903975498877 1055507714149838990812079)
      ·
        refine ⟨1583261571224758486218119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055507714149838990812079 1583261571224758486218119)
        ·
          refine ⟨2374892356837137729327179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583261571224758486218119 2374892356837137729327179)
          ·
            refine ⟨3562338535255706593990769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374892356837137729327179 3562338535255706593990769)
            ·
              refine ⟨2671753901441779945493077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3562338535255706593990769 2671753901441779945493077)
              ·
                refine ⟨31309616032520858736247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2671753901441779945493077 31309616032520858736247)
                ·
                  rfl

theorem cell22_823166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_823166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823166 prefixEnd_823166 := by exact prefixLift 823166
  have htrace : WordTrace (prefixWord ++ tailWord_823166) baseStart_823166 baseEnd_823166 := by
    simpa [prefixWord, tailWord_823166, baseEnd_823166] using wordTrace_append hprefix tailTrace_823166
  have hstable : (prefixWord ++ tailWord_823166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823166).length < 2 ^ (prefixWord ++ tailWord_823166).sum := by decide
  have hdescent : baseEnd_823166 < baseStart_823166 := by decide
  rcases family_descends (prefixWord ++ tailWord_823166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823224 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 3, 4]
def baseStart_823224 : Nat := 118140960795 + 823224 * 2 ^ 59
def prefixEnd_823224 : Nat := 4983230072969 + 3 ^ 40 * 823224 * 2
def baseEnd_823224 : Nat := 281806398877994910676045

theorem tailTrace_823224 : CollatzResearch.WordTrace tailWord_823224 prefixEnd_823224 281806398877994910676045 := by
  unfold tailWord_823224
  simp only [CollatzResearch.WordTrace]
  refine ⟨15012722984803759155466363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20016963979738345540621817 15012722984803759155466363)
  ·
    refine ⟨22519084477205638733199545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15012722984803759155466363 22519084477205638733199545)
    ·
      refine ⟨16889313357904229049899659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22519084477205638733199545 16889313357904229049899659)
      ·
        refine ⟨25333970036856343574849489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16889313357904229049899659 25333970036856343574849489)
        ·
          refine ⟨19000477527642257681137117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25333970036856343574849489 19000477527642257681137117)
          ·
            refine ⟨7125179072865846630426419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19000477527642257681137117 7125179072865846630426419)
            ·
              refine ⟨10687768609298769945639629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7125179072865846630426419 10687768609298769945639629)
              ·
                refine ⟨4007913228487038729614861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10687768609298769945639629 4007913228487038729614861)
                ·
                  refine ⟨1502967460682639523605573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4007913228487038729614861 1502967460682639523605573)
                  ·
                    refine ⟨281806398877994910676045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1502967460682639523605573 281806398877994910676045)
                    ·
                      rfl

theorem cell22_823224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_823224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823224 prefixEnd_823224 := by exact prefixLift 823224
  have htrace : WordTrace (prefixWord ++ tailWord_823224) baseStart_823224 baseEnd_823224 := by
    simpa [prefixWord, tailWord_823224, baseEnd_823224] using wordTrace_append hprefix tailTrace_823224
  have hstable : (prefixWord ++ tailWord_823224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823224).length < 2 ^ (prefixWord ++ tailWord_823224).sum := by decide
  have hdescent : baseEnd_823224 < baseStart_823224 := by decide
  rcases family_descends (prefixWord ++ tailWord_823224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823256 : List Nat := [2, 1, 2, 2, 2, 2, 1, 6, 4]
def baseStart_823256 : Nat := 118140960795 + 823256 * 2 ^ 59
def prefixEnd_823256 : Nat := 4983230072969 + 3 ^ 40 * 823256 * 2
def baseEnd_823256 : Nat := 93939117710652497958649

theorem tailTrace_823256 : CollatzResearch.WordTrace tailWord_823256 prefixEnd_823256 93939117710652497958649 := by
  unfold tailWord_823256
  simp only [CollatzResearch.WordTrace]
  refine ⟨15013306552745793888048811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20017742070327725184065081 15013306552745793888048811)
  ·
    refine ⟨22519959829118690832073217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15013306552745793888048811 22519959829118690832073217)
    ·
      refine ⟨16889969871839018124054913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22519959829118690832073217 16889969871839018124054913)
      ·
        refine ⟨12667477403879263593041185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16889969871839018124054913 12667477403879263593041185)
        ·
          refine ⟨9500608052909447694780889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12667477403879263593041185 9500608052909447694780889)
          ·
            refine ⟨7125456039682085771085667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9500608052909447694780889 7125456039682085771085667)
            ·
              refine ⟨10688184059523128656628501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7125456039682085771085667 10688184059523128656628501)
              ·
                refine ⟨501008627790146655779461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10688184059523128656628501 501008627790146655779461)
                ·
                  refine ⟨93939117710652497958649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 501008627790146655779461 93939117710652497958649)
                  ·
                    rfl

theorem cell22_823256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 4].length) (baseStart_823256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823256 prefixEnd_823256 := by exact prefixLift 823256
  have htrace : WordTrace (prefixWord ++ tailWord_823256) baseStart_823256 baseEnd_823256 := by
    simpa [prefixWord, tailWord_823256, baseEnd_823256] using wordTrace_append hprefix tailTrace_823256
  have hstable : (prefixWord ++ tailWord_823256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823256).length < 2 ^ (prefixWord ++ tailWord_823256).sum := by decide
  have hdescent : baseEnd_823256 < baseStart_823256 := by decide
  rcases family_descends (prefixWord ++ tailWord_823256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823378 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_823378 : Nat := 118140960795 + 823378 * 2 ^ 59
def prefixEnd_823378 : Nat := 4983230072969 + 3 ^ 40 * 823378 * 2
def baseEnd_823378 : Nat := 281859116225189842325573

theorem tailTrace_823378 : CollatzResearch.WordTrace tailWord_823378 prefixEnd_823378 281859116225189842325573 := by
  unfold tailWord_823378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7507765702762400653009697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20020708540699735074692525 7507765702762400653009697)
  ·
    refine ⟨5630824277071800489757273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7507765702762400653009697 5630824277071800489757273)
    ·
      refine ⟨4223118207803850367317955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5630824277071800489757273 4223118207803850367317955)
      ·
        refine ⟨6334677311705775550976933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4223118207803850367317955 6334677311705775550976933)
        ·
          refine ⟨1187751995944832915808175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6334677311705775550976933 1187751995944832915808175)
          ·
            refine ⟨1781627993917249373712263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187751995944832915808175 1781627993917249373712263)
            ·
              refine ⟨2672441990875874060568395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781627993917249373712263 2672441990875874060568395)
              ·
                refine ⟨4008662986313811090852593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2672441990875874060568395 4008662986313811090852593)
                ·
                  refine ⟨3006497239735358318139445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4008662986313811090852593 3006497239735358318139445)
                  ·
                    refine ⟨281859116225189842325573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3006497239735358318139445 281859116225189842325573)
                    ·
                      rfl

theorem cell22_823378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_823378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823378 prefixEnd_823378 := by exact prefixLift 823378
  have htrace : WordTrace (prefixWord ++ tailWord_823378) baseStart_823378 baseEnd_823378 := by
    simpa [prefixWord, tailWord_823378, baseEnd_823378] using wordTrace_append hprefix tailTrace_823378
  have hstable : (prefixWord ++ tailWord_823378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823378).length < 2 ^ (prefixWord ++ tailWord_823378).sum := by decide
  have hdescent : baseEnd_823378 < baseStart_823378 := by decide
  rcases family_descends (prefixWord ++ tailWord_823378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823408 : List Nat := [2, 1, 1, 1, 5, 2, 1, 5, 4]
def baseStart_823408 : Nat := 118140960795 + 823408 * 2 ^ 59
def prefixEnd_823408 : Nat := 4983230072969 + 3 ^ 40 * 823408 * 2
def baseEnd_823408 : Nat := 93956461946093254691827

theorem tailTrace_823408 : CollatzResearch.WordTrace tailWord_823408 prefixEnd_823408 93956461946093254691827 := by
  unfold tailWord_823408
  simp only [CollatzResearch.WordTrace]
  refine ⟨15016078500470458867815439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20021438000627278490420585 15016078500470458867815439)
  ·
    refine ⟨22524117750705688301723159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15016078500470458867815439 22524117750705688301723159)
    ·
      refine ⟨33786176626058532452584739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22524117750705688301723159 33786176626058532452584739)
      ·
        refine ⟨50679264939087798678877109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33786176626058532452584739 50679264939087798678877109)
        ·
          refine ⟨4751181088039481126144729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50679264939087798678877109 4751181088039481126144729)
          ·
            refine ⟨3563385816029610844608547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4751181088039481126144729 3563385816029610844608547)
            ·
              refine ⟨5345078724044416266912821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563385816029610844608547 5345078724044416266912821)
              ·
                refine ⟨501101130379164025023077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5345078724044416266912821 501101130379164025023077)
                ·
                  refine ⟨93956461946093254691827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 501101130379164025023077 93956461946093254691827)
                  ·
                    rfl

theorem cell22_823408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 4].length) (baseStart_823408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823408 prefixEnd_823408 := by exact prefixLift 823408
  have htrace : WordTrace (prefixWord ++ tailWord_823408) baseStart_823408 baseEnd_823408 := by
    simpa [prefixWord, tailWord_823408, baseEnd_823408] using wordTrace_append hprefix tailTrace_823408
  have hstable : (prefixWord ++ tailWord_823408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823408).length < 2 ^ (prefixWord ++ tailWord_823408).sum := by decide
  have hdescent : baseEnd_823408 < baseStart_823408 := by decide
  rcases family_descends (prefixWord ++ tailWord_823408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823410 : List Nat := [3, 2, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_823410 : Nat := 118140960795 + 823410 * 2 ^ 59
def prefixEnd_823410 : Nat := 4983230072969 + 3 ^ 40 * 823410 * 2
def baseEnd_823410 : Nat := 281870070479152425525475

theorem tailTrace_823410 : CollatzResearch.WordTrace tailWord_823410 prefixEnd_823410 281870070479152425525475 := by
  unfold tailWord_823410
  simp only [CollatzResearch.WordTrace]
  refine ⟨7508057486733418019300921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20021486631289114718135789 7508057486733418019300921)
  ·
    refine ⟨5631043115050063514475691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7508057486733418019300921 5631043115050063514475691)
    ·
      refine ⟨8446564672575095271713537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5631043115050063514475691 8446564672575095271713537)
      ·
        refine ⟨6334923504431321453785153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8446564672575095271713537 6334923504431321453785153)
        ·
          refine ⟨4751192628323491090338865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6334923504431321453785153 4751192628323491090338865)
          ·
            refine ⟨3563394471242618317754149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4751192628323491090338865 3563394471242618317754149)
            ·
              refine ⟨668136463357990934578903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3563394471242618317754149 668136463357990934578903)
              ·
                refine ⟨1002204695036986401868355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668136463357990934578903 1002204695036986401868355)
                ·
                  refine ⟨1503307042555479602802533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002204695036986401868355 1503307042555479602802533)
                  ·
                    refine ⟨281870070479152425525475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1503307042555479602802533 281870070479152425525475)
                    ·
                      rfl

theorem cell22_823410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_823410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823410 prefixEnd_823410 := by exact prefixLift 823410
  have htrace : WordTrace (prefixWord ++ tailWord_823410) baseStart_823410 baseEnd_823410 := by
    simpa [prefixWord, tailWord_823410, baseEnd_823410] using wordTrace_append hprefix tailTrace_823410
  have hstable : (prefixWord ++ tailWord_823410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823410).length < 2 ^ (prefixWord ++ tailWord_823410).sum := by decide
  have hdescent : baseEnd_823410 < baseStart_823410 := by decide
  rcases family_descends (prefixWord ++ tailWord_823410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823440 : List Nat := [2, 1, 1, 1, 1, 1, 9, 1, 2, 3]
def baseStart_823440 : Nat := 118140960795 + 823440 * 2 ^ 59
def prefixEnd_823440 : Nat := 4983230072969 + 3 ^ 40 * 823440 * 2
def baseEnd_823440 : Nat := 281880340092242347275383

theorem tailTrace_823440 : CollatzResearch.WordTrace tailWord_823440 prefixEnd_823440 281880340092242347275383 := by
  unfold tailWord_823440
  simp only [CollatzResearch.WordTrace]
  refine ⟨15016662068412493600397887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20022216091216658133863849 15016662068412493600397887)
  ·
    refine ⟨22524993102618740400596831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15016662068412493600397887 22524993102618740400596831)
    ·
      refine ⟨33787489653928110600895247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22524993102618740400596831 33787489653928110600895247)
      ·
        refine ⟨50681234480892165901342871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33787489653928110600895247 50681234480892165901342871)
        ·
          refine ⟨76021851721338248852014307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50681234480892165901342871 76021851721338248852014307)
          ·
            refine ⟨114032777582007373278021461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76021851721338248852014307 114032777582007373278021461)
            ·
              refine ⟨668160806144574452800907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 114032777582007373278021461 668160806144574452800907)
              ·
                refine ⟨1002241209216861679201361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668160806144574452800907 1002241209216861679201361)
                ·
                  refine ⟨751680906912646259401021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1002241209216861679201361 751680906912646259401021)
                  ·
                    refine ⟨281880340092242347275383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 751680906912646259401021 281880340092242347275383)
                    ·
                      rfl

theorem cell22_823440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 2, 3].length) (baseStart_823440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823440 prefixEnd_823440 := by exact prefixLift 823440
  have htrace : WordTrace (prefixWord ++ tailWord_823440) baseStart_823440 baseEnd_823440 := by
    simpa [prefixWord, tailWord_823440, baseEnd_823440] using wordTrace_append hprefix tailTrace_823440
  have hstable : (prefixWord ++ tailWord_823440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823440).length < 2 ^ (prefixWord ++ tailWord_823440).sum := by decide
  have hdescent : baseEnd_823440 < baseStart_823440 := by decide
  rcases family_descends (prefixWord ++ tailWord_823440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823453 : List Nat := [1, 4, 2, 1, 1, 3, 4, 6]
def baseStart_823453 : Nat := 118140960795 + 823453 * 2 ^ 59
def prefixEnd_823453 : Nat := 4983230072969 + 3 ^ 40 * 823453 * 2
def baseEnd_823453 : Nat := 31320532250879405188927

theorem tailTrace_823453 : CollatzResearch.WordTrace tailWord_823453 prefixEnd_823453 31320532250879405188927 := by
  unfold tailWord_823453
  simp only [CollatzResearch.WordTrace]
  refine ⟨30033798285777890421019013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20022532190518593614012675 30033798285777890421019013)
  ·
    refine ⟨5631337178583354453941065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30033798285777890421019013 5631337178583354453941065)
    ·
      refine ⟨4223502883937515840455799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5631337178583354453941065 4223502883937515840455799)
      ·
        refine ⟨6335254325906273760683699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4223502883937515840455799 6335254325906273760683699)
        ·
          refine ⟨9502881488859410641025549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6335254325906273760683699 9502881488859410641025549)
          ·
            refine ⟨3563580558322278990384581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9502881488859410641025549 3563580558322278990384581)
            ·
              refine ⟨668171354685427310697109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3563580558322278990384581 668171354685427310697109)
              ·
                refine ⟨31320532250879405188927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 668171354685427310697109 31320532250879405188927)
                ·
                  rfl

theorem cell22_823453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 6].length) (baseStart_823453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823453 prefixEnd_823453 := by exact prefixLift 823453
  have htrace : WordTrace (prefixWord ++ tailWord_823453) baseStart_823453 baseEnd_823453 := by
    simpa [prefixWord, tailWord_823453, baseEnd_823453] using wordTrace_append hprefix tailTrace_823453
  have hstable : (prefixWord ++ tailWord_823453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823453).length < 2 ^ (prefixWord ++ tailWord_823453).sum := by decide
  have hdescent : baseEnd_823453 < baseStart_823453 := by decide
  rcases family_descends (prefixWord ++ tailWord_823453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823476 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 6]
def baseStart_823476 : Nat := 118140960795 + 823476 * 2 ^ 59
def prefixEnd_823476 : Nat := 4983230072969 + 3 ^ 40 * 823476 * 2
def baseEnd_823476 : Nat := 93964221209316751125091

theorem tailTrace_823476 : CollatzResearch.WordTrace tailWord_823476 prefixEnd_823476 93964221209316751125091 := by
  unfold tailWord_823476
  simp only [CollatzResearch.WordTrace]
  refine ⟨15017318582347282674553141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20023091443129710232737521 15017318582347282674553141)
  ·
    refine ⟨1407873617095057750739357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15017318582347282674553141 1407873617095057750739357)
    ·
      refine ⟨527952606410646656527259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1407873617095057750739357 527952606410646656527259)
      ·
        refine ⟨791928909615969984790889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527952606410646656527259 791928909615969984790889)
        ·
          refine ⟨593946682211977488593167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791928909615969984790889 593946682211977488593167)
          ·
            refine ⟨890920023317966232889751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593946682211977488593167 890920023317966232889751)
            ·
              refine ⟨1336380034976949349334627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890920023317966232889751 1336380034976949349334627)
              ·
                refine ⟨2004570052465424024001941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336380034976949349334627 2004570052465424024001941)
                ·
                  refine ⟨93964221209316751125091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2004570052465424024001941 93964221209316751125091)
                  ·
                    rfl

theorem cell22_823476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_823476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823476 prefixEnd_823476 := by exact prefixLift 823476
  have htrace : WordTrace (prefixWord ++ tailWord_823476) baseStart_823476 baseEnd_823476 := by
    simpa [prefixWord, tailWord_823476, baseEnd_823476] using wordTrace_append hprefix tailTrace_823476
  have hstable : (prefixWord ++ tailWord_823476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823476).length < 2 ^ (prefixWord ++ tailWord_823476).sum := by decide
  have hdescent : baseEnd_823476 < baseStart_823476 := by decide
  rcases family_descends (prefixWord ++ tailWord_823476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823481 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 7]
def baseStart_823481 : Nat := 118140960795 + 823481 * 2 ^ 59
def prefixEnd_823481 : Nat := 4983230072969 + 3 ^ 40 * 823481 * 2
def baseEnd_823481 : Nat := 93964791743377302333419

theorem tailTrace_823481 : CollatzResearch.WordTrace tailWord_823481 prefixEnd_823481 93964791743377302333419 := by
  unfold tailWord_823481
  simp only [CollatzResearch.WordTrace]
  refine ⟨30034819529676451203038297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20023213019784300802025531 30034819529676451203038297)
  ·
    refine ⟨22526114647257338402278723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30034819529676451203038297 22526114647257338402278723)
    ·
      refine ⟨33789171970886007603418085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22526114647257338402278723 33789171970886007603418085)
      ·
        refine ⟨6335469744541126425640891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33789171970886007603418085 6335469744541126425640891)
        ·
          refine ⟨9503204616811689638461337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6335469744541126425640891 9503204616811689638461337)
          ·
            refine ⟨7127403462608767228846003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9503204616811689638461337 7127403462608767228846003)
            ·
              refine ⟨10691105193913150843269005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7127403462608767228846003 10691105193913150843269005)
              ·
                refine ⟨4009164447717431566225877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10691105193913150843269005 4009164447717431566225877)
                ·
                  refine ⟨93964791743377302333419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4009164447717431566225877 93964791743377302333419)
                  ·
                    rfl

theorem cell22_823481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_823481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823481 prefixEnd_823481 := by exact prefixLift 823481
  have htrace : WordTrace (prefixWord ++ tailWord_823481) baseStart_823481 baseEnd_823481 := by
    simpa [prefixWord, tailWord_823481, baseEnd_823481] using wordTrace_append hprefix tailTrace_823481
  have hstable : (prefixWord ++ tailWord_823481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823481).length < 2 ^ (prefixWord ++ tailWord_823481).sum := by decide
  have hdescent : baseEnd_823481 < baseStart_823481 := by decide
  rcases family_descends (prefixWord ++ tailWord_823481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823496 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 1, 7]
def baseStart_823496 : Nat := 118140960795 + 823496 * 2 ^ 59
def prefixEnd_823496 : Nat := 4983230072969 + 3 ^ 40 * 823496 * 2
def baseEnd_823496 : Nat := 281899510036676867875211

theorem tailTrace_823496 : CollatzResearch.WordTrace tailWord_823496 prefixEnd_823496 281899510036676867875211 := by
  unfold tailWord_823496
  simp only [CollatzResearch.WordTrace]
  refine ⟨15017683312311054382417171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20023577749748072509889561 15017683312311054382417171)
  ·
    refine ⟨22526524968466581573625757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15017683312311054382417171 22526524968466581573625757)
    ·
      refine ⟨8447446863174968090109659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22526524968466581573625757 8447446863174968090109659)
      ·
        refine ⟨12671170294762452135164489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8447446863174968090109659 12671170294762452135164489)
        ·
          refine ⟨9503377721071839101373367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12671170294762452135164489 9503377721071839101373367)
          ·
            refine ⟨14255066581607758652060051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9503377721071839101373367 14255066581607758652060051)
            ·
              refine ⟨21382599872411637978090077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14255066581607758652060051 21382599872411637978090077)
              ·
                refine ⟨8018474952154364241783779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21382599872411637978090077 8018474952154364241783779)
                ·
                  refine ⟨12027712428231546362675669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8018474952154364241783779 12027712428231546362675669)
                  ·
                    refine ⟨281899510036676867875211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12027712428231546362675669 281899510036676867875211)
                    ·
                      rfl

theorem cell22_823496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_823496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823496 prefixEnd_823496 := by exact prefixLift 823496
  have htrace : WordTrace (prefixWord ++ tailWord_823496) baseStart_823496 baseEnd_823496 := by
    simpa [prefixWord, tailWord_823496, baseEnd_823496] using wordTrace_append hprefix tailTrace_823496
  have hstable : (prefixWord ++ tailWord_823496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823496).length < 2 ^ (prefixWord ++ tailWord_823496).sum := by decide
  have hdescent : baseEnd_823496 < baseStart_823496 := by decide
  rcases family_descends (prefixWord ++ tailWord_823496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823498 : List Nat := [3, 1, 2, 1, 3, 1, 3, 3, 5]
def baseStart_823498 : Nat := 118140960795 + 823498 * 2 ^ 59
def prefixEnd_823498 : Nat := 4983230072969 + 3 ^ 40 * 823498 * 2
def baseEnd_823498 : Nat := 93966731559183176441735

theorem tailTrace_823498 : CollatzResearch.WordTrace tailWord_823498 prefixEnd_823498 93966731559183176441735 := by
  unfold tailWord_823498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7508859892653715776601787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20023626380409908737604765 7508859892653715776601787)
  ·
    refine ⟨11263289838980573664902681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7508859892653715776601787 11263289838980573664902681)
    ·
      refine ⟨8447467379235430248677011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11263289838980573664902681 8447467379235430248677011)
      ·
        refine ⟨12671201068853145373015517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8447467379235430248677011 12671201068853145373015517)
        ·
          refine ⟨4751700400819929514880819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12671201068853145373015517 4751700400819929514880819)
          ·
            refine ⟨7127550601229894272321229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4751700400819929514880819 7127550601229894272321229)
            ·
              refine ⟨2672831475461210352120461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7127550601229894272321229 2672831475461210352120461)
              ·
                refine ⟨1002311803297953882045173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2672831475461210352120461 1002311803297953882045173)
                ·
                  refine ⟨93966731559183176441735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1002311803297953882045173 93966731559183176441735)
                  ·
                    rfl

theorem cell22_823498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_823498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823498 prefixEnd_823498 := by exact prefixLift 823498
  have htrace : WordTrace (prefixWord ++ tailWord_823498) baseStart_823498 baseEnd_823498 := by
    simpa [prefixWord, tailWord_823498, baseEnd_823498] using wordTrace_append hprefix tailTrace_823498
  have hstable : (prefixWord ++ tailWord_823498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823498).length < 2 ^ (prefixWord ++ tailWord_823498).sum := by decide
  have hdescent : baseEnd_823498 < baseStart_823498 := by decide
  rcases family_descends (prefixWord ++ tailWord_823498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823571 : List Nat := [1, 1, 1, 2, 1, 3, 1, 12]
def baseStart_823571 : Nat := 118140960795 + 823571 * 2 ^ 59
def prefixEnd_823571 : Nat := 4983230072969 + 3 ^ 40 * 823571 * 2
def baseEnd_823571 : Nat := 31325020452155741361109

theorem tailTrace_823571 : CollatzResearch.WordTrace tailWord_823571 prefixEnd_823571 31325020452155741361109 := by
  unfold tailWord_823571
  simp only [CollatzResearch.WordTrace]
  refine ⟨30038102099350396573814567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20025401399566931049209711 30038102099350396573814567)
  ·
    refine ⟨45057153149025594860721851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30038102099350396573814567 45057153149025594860721851)
    ·
      refine ⟨67585729723538392291082777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45057153149025594860721851 67585729723538392291082777)
      ·
        refine ⟨50689297292653794218312083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67585729723538392291082777 50689297292653794218312083)
        ·
          refine ⟨76033945938980691327468125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50689297292653794218312083 76033945938980691327468125)
          ·
            refine ⟨28512729727117759247800547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76033945938980691327468125 28512729727117759247800547)
            ·
              refine ⟨42769094590676638871700821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28512729727117759247800547 42769094590676638871700821)
              ·
                refine ⟨31325020452155741361109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 42769094590676638871700821 31325020452155741361109)
                ·
                  rfl

theorem cell22_823571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 12].length) (baseStart_823571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823571 prefixEnd_823571 := by exact prefixLift 823571
  have htrace : WordTrace (prefixWord ++ tailWord_823571) baseStart_823571 baseEnd_823571 := by
    simpa [prefixWord, tailWord_823571, baseEnd_823571] using wordTrace_append hprefix tailTrace_823571
  have hstable : (prefixWord ++ tailWord_823571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823571).length < 2 ^ (prefixWord ++ tailWord_823571).sum := by decide
  have hdescent : baseEnd_823571 < baseStart_823571 := by decide
  rcases family_descends (prefixWord ++ tailWord_823571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823588 : List Nat := [2, 3, 1, 3, 1, 3, 9]
def baseStart_823588 : Nat := 118140960795 + 823588 * 2 ^ 59
def prefixEnd_823588 : Nat := 4983230072969 + 3 ^ 40 * 823588 * 2
def baseEnd_823588 : Nat := 10441889019141455354627

theorem tailTrace_823588 : CollatzResearch.WordTrace tailWord_823588 prefixEnd_823588 10441889019141455354627 := by
  unfold tailWord_823588
  simp only [CollatzResearch.WordTrace]
  refine ⟨15019361070144404238591709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20025814760192538984788945 15019361070144404238591709)
  ·
    refine ⟨5632260401304151589471891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15019361070144404238591709 5632260401304151589471891)
    ·
      refine ⟨8448390601956227384207837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5632260401304151589471891 8448390601956227384207837)
      ·
        refine ⟨3168146475733585269077939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8448390601956227384207837 3168146475733585269077939)
        ·
          refine ⟨4752219713600377903616909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3168146475733585269077939 4752219713600377903616909)
          ·
            refine ⟨1782082392600141713856341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4752219713600377903616909 1782082392600141713856341)
            ·
              refine ⟨10441889019141455354627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1782082392600141713856341 10441889019141455354627)
              ·
                rfl

theorem cell22_823588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 9].length) (baseStart_823588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823588 prefixEnd_823588 := by exact prefixLift 823588
  have htrace : WordTrace (prefixWord ++ tailWord_823588) baseStart_823588 baseEnd_823588 := by
    simpa [prefixWord, tailWord_823588, baseEnd_823588] using wordTrace_append hprefix tailTrace_823588
  have hstable : (prefixWord ++ tailWord_823588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823588).length < 2 ^ (prefixWord ++ tailWord_823588).sum := by decide
  have hdescent : baseEnd_823588 < baseStart_823588 := by decide
  rcases family_descends (prefixWord ++ tailWord_823588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823592 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 4, 3]
def baseStart_823592 : Nat := 118140960795 + 823592 * 2 ^ 59
def prefixEnd_823592 : Nat := 4983230072969 + 3 ^ 40 * 823592 * 2
def baseEnd_823592 : Nat := 281932372798564617474917

theorem tailTrace_823592 : CollatzResearch.WordTrace tailWord_823592 prefixEnd_823592 281932372798564617474917 := by
  unfold tailWord_823592
  simp only [CollatzResearch.WordTrace]
  refine ⟨15019434016137158580164515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20025912021516211440219353 15019434016137158580164515)
  ·
    refine ⟨22529151024205737870246773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15019434016137158580164515 22529151024205737870246773)
    ·
      refine ⟨2112107908519287925335635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22529151024205737870246773 2112107908519287925335635)
      ·
        refine ⟨3168161862778931888003453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112107908519287925335635 3168161862778931888003453)
        ·
          refine ⟨1188060698542099458001295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3168161862778931888003453 1188060698542099458001295)
          ·
            refine ⟨1782091047813149187001943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188060698542099458001295 1782091047813149187001943)
            ·
              refine ⟨2673136571719723780502915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782091047813149187001943 2673136571719723780502915)
              ·
                refine ⟨4009704857579585670754373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673136571719723780502915 4009704857579585670754373)
                ·
                  refine ⟨751819660796172313266445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4009704857579585670754373 751819660796172313266445)
                  ·
                    refine ⟨281932372798564617474917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 751819660796172313266445 281932372798564617474917)
                    ·
                      rfl

theorem cell22_823592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_823592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823592 prefixEnd_823592 := by exact prefixLift 823592
  have htrace : WordTrace (prefixWord ++ tailWord_823592) baseStart_823592 baseEnd_823592 := by
    simpa [prefixWord, tailWord_823592, baseEnd_823592] using wordTrace_append hprefix tailTrace_823592
  have hstable : (prefixWord ++ tailWord_823592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823592).length < 2 ^ (prefixWord ++ tailWord_823592).sum := by decide
  have hdescent : baseEnd_823592 < baseStart_823592 := by decide
  rcases family_descends (prefixWord ++ tailWord_823592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823609 : List Nat := [1, 2, 1, 6, 1, 2, 3, 1, 2, 3]
def baseStart_823609 : Nat := 118140960795 + 823609 * 2 ^ 59
def prefixEnd_823609 : Nat := 4983230072969 + 3 ^ 40 * 823609 * 2
def baseEnd_823609 : Nat := 281938192245982239799865

theorem tailTrace_823609 : CollatzResearch.WordTrace tailWord_823609 prefixEnd_823609 281938192245982239799865 := by
  unfold tailWord_823609
  simp only [CollatzResearch.WordTrace]
  refine ⟨30039488073212729063697881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20026325382141819375798587 30039488073212729063697881)
  ·
    refine ⟨22529616054909546797773411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30039488073212729063697881 22529616054909546797773411)
    ·
      refine ⟨33794424082364320196660117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22529616054909546797773411 33794424082364320196660117)
      ·
        refine ⟨1584113628860827509218443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33794424082364320196660117 1584113628860827509218443)
        ·
          refine ⟨2376170443291241263827665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1584113628860827509218443 2376170443291241263827665)
          ·
            refine ⟨1782127832468430947870749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2376170443291241263827665 1782127832468430947870749)
            ·
              refine ⟨668297937175661605451531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1782127832468430947870749 668297937175661605451531)
              ·
                refine ⟨1002446905763492408177297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668297937175661605451531 1002446905763492408177297)
                ·
                  refine ⟨751835179322619306132973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1002446905763492408177297 751835179322619306132973)
                  ·
                    refine ⟨281938192245982239799865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 751835179322619306132973 281938192245982239799865)
                    ·
                      rfl

theorem cell22_823609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 2, 3].length) (baseStart_823609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823609 prefixEnd_823609 := by exact prefixLift 823609
  have htrace : WordTrace (prefixWord ++ tailWord_823609) baseStart_823609 baseEnd_823609 := by
    simpa [prefixWord, tailWord_823609, baseEnd_823609] using wordTrace_append hprefix tailTrace_823609
  have hstable : (prefixWord ++ tailWord_823609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823609).length < 2 ^ (prefixWord ++ tailWord_823609).sum := by decide
  have hdescent : baseEnd_823609 < baseStart_823609 := by decide
  rcases family_descends (prefixWord ++ tailWord_823609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823633 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 7]
def baseStart_823633 : Nat := 118140960795 + 823633 * 2 ^ 59
def prefixEnd_823633 : Nat := 4983230072969 + 3 ^ 40 * 823633 * 2
def baseEnd_823633 : Nat := 93982135978818059066597

theorem tailTrace_823633 : CollatzResearch.WordTrace tailWord_823633 prefixEnd_823633 93982135978818059066597 := by
  unfold tailWord_823633
  simp only [CollatzResearch.WordTrace]
  refine ⟨30040363425125781162571553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20026908950083854108381035 30040363425125781162571553)
  ·
    refine ⟨22530272568844335871928665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30040363425125781162571553 22530272568844335871928665)
    ·
      refine ⟨16897704426633251903946499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22530272568844335871928665 16897704426633251903946499)
      ·
        refine ⟨25346556639949877855919749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16897704426633251903946499 25346556639949877855919749)
        ·
          refine ⟨4752479369990602097984953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25346556639949877855919749 4752479369990602097984953)
          ·
            refine ⟨3564359527492951573488715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4752479369990602097984953 3564359527492951573488715)
            ·
              refine ⟨5346539291239427360233073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3564359527492951573488715 5346539291239427360233073)
              ·
                refine ⟨4009904468429570520174805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5346539291239427360233073 4009904468429570520174805)
                ·
                  refine ⟨93982135978818059066597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4009904468429570520174805 93982135978818059066597)
                  ·
                    rfl

theorem cell22_823633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_823633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823633 prefixEnd_823633 := by exact prefixLift 823633
  have htrace : WordTrace (prefixWord ++ tailWord_823633) baseStart_823633 baseEnd_823633 := by
    simpa [prefixWord, tailWord_823633, baseEnd_823633] using wordTrace_append hprefix tailTrace_823633
  have hstable : (prefixWord ++ tailWord_823633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823633).length < 2 ^ (prefixWord ++ tailWord_823633).sum := by decide
  have hdescent : baseEnd_823633 < baseStart_823633 := by decide
  rcases family_descends (prefixWord ++ tailWord_823633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823650 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 7]
def baseStart_823650 : Nat := 118140960795 + 823650 * 2 ^ 59
def prefixEnd_823650 : Nat := 4983230072969 + 3 ^ 40 * 823650 * 2
def baseEnd_823650 : Nat := 93984075794623933174913

theorem tailTrace_823650 : CollatzResearch.WordTrace tailWord_823650 prefixEnd_823650 93984075794623933174913 := by
  unfold tailWord_823650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7510245866516048266485101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20027322310709462043960269 7510245866516048266485101)
  ·
    refine ⟨2816342199943518099931913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7510245866516048266485101 2816342199943518099931913)
    ·
      refine ⟨2112256649957638574948935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2816342199943518099931913 2112256649957638574948935)
      ·
        refine ⟨3168384974936457862423403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112256649957638574948935 3168384974936457862423403)
        ·
          refine ⟨4752577462404686793635105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3168384974936457862423403 4752577462404686793635105)
          ·
            refine ⟨3564433096803515095226329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4752577462404686793635105 3564433096803515095226329)
            ·
              refine ⟨2673324822602636321419747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3564433096803515095226329 2673324822602636321419747)
              ·
                refine ⟨4009987233903954482129621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673324822602636321419747 4009987233903954482129621)
                ·
                  refine ⟨93984075794623933174913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4009987233903954482129621 93984075794623933174913)
                  ·
                    rfl

theorem cell22_823650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_823650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823650 prefixEnd_823650 := by exact prefixLift 823650
  have htrace : WordTrace (prefixWord ++ tailWord_823650) baseStart_823650 baseEnd_823650 := by
    simpa [prefixWord, tailWord_823650, baseEnd_823650] using wordTrace_append hprefix tailTrace_823650
  have hstable : (prefixWord ++ tailWord_823650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823650).length < 2 ^ (prefixWord ++ tailWord_823650).sum := by decide
  have hdescent : baseEnd_823650 < baseStart_823650 := by decide
  rcases family_descends (prefixWord ++ tailWord_823650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823712 : List Nat := [2, 1, 1, 4, 1, 4, 1, 4, 4]
def baseStart_823712 : Nat := 118140960795 + 823712 * 2 ^ 59
def prefixEnd_823712 : Nat := 4983230072969 + 3 ^ 40 * 823712 * 2
def baseEnd_823712 : Nat := 93991150416974768158183

theorem tailTrace_823712 : CollatzResearch.WordTrace tailWord_823712 prefixEnd_823712 93991150416974768158183 := by
  unfold tailWord_823712
  simp only [CollatzResearch.WordTrace]
  refine ⟨15021622395919788827348695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20028829861226385103131593 15021622395919788827348695)
  ·
    refine ⟨22532433593879683241023043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15021622395919788827348695 22532433593879683241023043)
    ·
      refine ⟨33798650390819524861534565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22532433593879683241023043 33798650390819524861534565)
      ·
        refine ⟨6337246948278660911537731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33798650390819524861534565 6337246948278660911537731)
        ·
          refine ⟨9505870422417991367306597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6337246948278660911537731 9505870422417991367306597)
          ·
            refine ⟨1782350704203373381369987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9505870422417991367306597 1782350704203373381369987)
            ·
              refine ⟨2673526056305060072054981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782350704203373381369987 2673526056305060072054981)
              ·
                refine ⟨501286135557198763510309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2673526056305060072054981 501286135557198763510309)
                ·
                  refine ⟨93991150416974768158183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 501286135557198763510309 93991150416974768158183)
                  ·
                    rfl

theorem cell22_823712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 4].length) (baseStart_823712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823712 prefixEnd_823712 := by exact prefixLift 823712
  have htrace : WordTrace (prefixWord ++ tailWord_823712) baseStart_823712 baseEnd_823712 := by
    simpa [prefixWord, tailWord_823712, baseEnd_823712] using wordTrace_append hprefix tailTrace_823712
  have hstable : (prefixWord ++ tailWord_823712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823712).length < 2 ^ (prefixWord ++ tailWord_823712).sum := by decide
  have hdescent : baseEnd_823712 < baseStart_823712 := by decide
  rcases family_descends (prefixWord ++ tailWord_823712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823742 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_823742 : Nat := 118140960795 + 823742 * 2 ^ 59
def prefixEnd_823742 : Nat := 4983230072969 + 3 ^ 40 * 823742 * 2
def baseEnd_823742 : Nat := 281983720864014226224457

theorem tailTrace_823742 : CollatzResearch.WordTrace tailWord_823742 prefixEnd_823742 281983720864014226224457 := by
  unfold tailWord_823742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3755542372716361597286185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20029559321153928518859653 3755542372716361597286185)
  ·
    refine ⟨2816656779537271197964639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3755542372716361597286185 2816656779537271197964639)
    ·
      refine ⟨4224985169305906796946959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816656779537271197964639 4224985169305906796946959)
      ·
        refine ⟨6337477753958860195420439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4224985169305906796946959 6337477753958860195420439)
        ·
          refine ⟨9506216630938290293130659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6337477753958860195420439 9506216630938290293130659)
          ·
            refine ⟨14259324946407435439695989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9506216630938290293130659 14259324946407435439695989)
            ·
              refine ⟨1336811713725697072471499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14259324946407435439695989 1336811713725697072471499)
              ·
                refine ⟨2005217570588545608707249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336811713725697072471499 2005217570588545608707249)
                ·
                  refine ⟨1503913177941409206530437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2005217570588545608707249 1503913177941409206530437)
                  ·
                    refine ⟨281983720864014226224457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1503913177941409206530437 281983720864014226224457)
                    ·
                      rfl

theorem cell22_823742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_823742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823742 prefixEnd_823742 := by exact prefixLift 823742
  have htrace : WordTrace (prefixWord ++ tailWord_823742) baseStart_823742 baseEnd_823742 := by
    simpa [prefixWord, tailWord_823742, baseEnd_823742] using wordTrace_append hprefix tailTrace_823742
  have hstable : (prefixWord ++ tailWord_823742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823742).length < 2 ^ (prefixWord ++ tailWord_823742).sum := by decide
  have hdescent : baseEnd_823742 < baseStart_823742 := by decide
  rcases family_descends (prefixWord ++ tailWord_823742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823748 : List Nat := [2, 3, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_823748 : Nat := 118140960795 + 823748 * 2 ^ 59
def prefixEnd_823748 : Nat := 4983230072969 + 3 ^ 40 * 823748 * 2
def baseEnd_823748 : Nat := 281985774786632210574439

theorem tailTrace_823748 : CollatzResearch.WordTrace tailWord_823748 prefixEnd_823748 281985774786632210574439 := by
  unfold tailWord_823748
  simp only [CollatzResearch.WordTrace]
  refine ⟨15022278909854577901503949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20029705213139437202005265 15022278909854577901503949)
  ·
    refine ⟨5633354591195466713063981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15022278909854577901503949 5633354591195466713063981)
    ·
      refine ⟨2112507971698300017398993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5633354591195466713063981 2112507971698300017398993)
      ·
        refine ⟨1584380978773725013049245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2112507971698300017398993 1584380978773725013049245)
        ·
          refine ⟨594142867040146879893467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1584380978773725013049245 594142867040146879893467)
          ·
            refine ⟨891214300560220319840201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594142867040146879893467 891214300560220319840201)
            ·
              refine ⟨668410725420165239880151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891214300560220319840201 668410725420165239880151)
              ·
                refine ⟨1002616088130247859820227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668410725420165239880151 1002616088130247859820227)
                ·
                  refine ⟨1503924132195371789730341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002616088130247859820227 1503924132195371789730341)
                  ·
                    refine ⟨281985774786632210574439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1503924132195371789730341 281985774786632210574439)
                    ·
                      rfl

theorem cell22_823748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_823748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823748 prefixEnd_823748 := by exact prefixLift 823748
  have htrace : WordTrace (prefixWord ++ tailWord_823748) baseStart_823748 baseEnd_823748 := by
    simpa [prefixWord, tailWord_823748, baseEnd_823748] using wordTrace_append hprefix tailTrace_823748
  have hstable : (prefixWord ++ tailWord_823748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823748).length < 2 ^ (prefixWord ++ tailWord_823748).sum := by decide
  have hdescent : baseEnd_823748 < baseStart_823748 := by decide
  rcases family_descends (prefixWord ++ tailWord_823748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823755 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 7, 3]
def baseStart_823755 : Nat := 118140960795 + 823755 * 2 ^ 59
def prefixEnd_823755 : Nat := 4983230072969 + 3 ^ 40 * 823755 * 2
def baseEnd_823755 : Nat := 281988171029686525649417

theorem tailTrace_823755 : CollatzResearch.WordTrace tailWord_823755 prefixEnd_823755 281988171029686525649417 := by
  unfold tailWord_823755
  simp only [CollatzResearch.WordTrace]
  refine ⟨30044813130683795998512719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20029875420455863999008479 30044813130683795998512719)
  ·
    refine ⟨45067219696025693997769079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30044813130683795998512719 45067219696025693997769079)
    ·
      refine ⟨67600829544038540996653619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45067219696025693997769079 67600829544038540996653619)
      ·
        refine ⟨101401244316057811494980429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67600829544038540996653619 101401244316057811494980429)
        ·
          refine ⟨38025466618521679310617661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101401244316057811494980429 38025466618521679310617661)
          ·
            refine ⟨14259549981945629741481623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38025466618521679310617661 14259549981945629741481623)
            ·
              refine ⟨21389324972918444612222435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14259549981945629741481623 21389324972918444612222435)
              ·
                refine ⟨32083987459377666918333653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21389324972918444612222435 32083987459377666918333653)
                ·
                  refine ⟨751968456079164068398445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 32083987459377666918333653 751968456079164068398445)
                  ·
                    refine ⟨281988171029686525649417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 751968456079164068398445 281988171029686525649417)
                    ·
                      rfl

theorem cell22_823755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 3].length) (baseStart_823755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823755 prefixEnd_823755 := by exact prefixLift 823755
  have htrace : WordTrace (prefixWord ++ tailWord_823755) baseStart_823755 baseEnd_823755 := by
    simpa [prefixWord, tailWord_823755, baseEnd_823755] using wordTrace_append hprefix tailTrace_823755
  have hstable : (prefixWord ++ tailWord_823755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823755).length < 2 ^ (prefixWord ++ tailWord_823755).sum := by decide
  have hdescent : baseEnd_823755 < baseStart_823755 := by decide
  rcases family_descends (prefixWord ++ tailWord_823755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823778 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_823778 : Nat := 118140960795 + 823778 * 2 ^ 59
def prefixEnd_823778 : Nat := 4983230072969 + 3 ^ 40 * 823778 * 2
def baseEnd_823778 : Nat := 281996044399722132324347

theorem tailTrace_823778 : CollatzResearch.WordTrace tailWord_823778 prefixEnd_823778 281996044399722132324347 := by
  unfold tailWord_823778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7511413002400117731649997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20030434673066980617733325 7511413002400117731649997)
  ·
    refine ⟨2816779875900044149368749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7511413002400117731649997 2816779875900044149368749)
    ·
      refine ⟨1056292453462516556013281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2816779875900044149368749 1056292453462516556013281)
      ·
        refine ⟨792219340096887417009961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1056292453462516556013281 792219340096887417009961)
        ·
          refine ⟨594164505072665562757471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792219340096887417009961 594164505072665562757471)
          ·
            refine ⟨891246757608998344136207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594164505072665562757471 891246757608998344136207)
            ·
              refine ⟨1336870136413497516204311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891246757608998344136207 1336870136413497516204311)
              ·
                refine ⟨2005305204620246274306467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336870136413497516204311 2005305204620246274306467)
                ·
                  refine ⟨3007957806930369411459701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005305204620246274306467 3007957806930369411459701)
                  ·
                    refine ⟨281996044399722132324347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3007957806930369411459701 281996044399722132324347)
                    ·
                      rfl

theorem cell22_823778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_823778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823778 prefixEnd_823778 := by exact prefixLift 823778
  have htrace : WordTrace (prefixWord ++ tailWord_823778) baseStart_823778 baseEnd_823778 := by
    simpa [prefixWord, tailWord_823778, baseEnd_823778] using wordTrace_append hprefix tailTrace_823778
  have hstable : (prefixWord ++ tailWord_823778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823778).length < 2 ^ (prefixWord ++ tailWord_823778).sum := by decide
  have hdescent : baseEnd_823778 < baseStart_823778 := by decide
  rcases family_descends (prefixWord ++ tailWord_823778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823789 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_823789 : Nat := 118140960795 + 823789 * 2 ^ 59
def prefixEnd_823789 : Nat := 4983230072969 + 3 ^ 40 * 823789 * 2
def baseEnd_823789 : Nat := 281999809924521770299313

theorem tailTrace_823789 : CollatzResearch.WordTrace tailWord_823789 prefixEnd_823789 281999809924521770299313 := by
  unfold tailWord_823789
  simp only [CollatzResearch.WordTrace]
  refine ⟨30046053212560619805250421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20030702141707079870166947 30046053212560619805250421)
  ·
    refine ⟨2816817488677558106742227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30046053212560619805250421 2816817488677558106742227)
    ·
      refine ⟨4225226233016337160113341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816817488677558106742227 4225226233016337160113341)
      ·
        refine ⟨1584459837381126435042503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4225226233016337160113341 1584459837381126435042503)
        ·
          refine ⟨2376689756071689652563755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1584459837381126435042503 2376689756071689652563755)
          ·
            refine ⟨3565034634107534478845633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376689756071689652563755 3565034634107534478845633)
            ·
              refine ⟨2673775975580650859134225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3565034634107534478845633 2673775975580650859134225)
              ·
                refine ⟨2005331981685488144350669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2673775975580650859134225 2005331981685488144350669)
                ·
                  refine ⟨751999493132058054131501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2005331981685488144350669 751999493132058054131501)
                  ·
                    refine ⟨281999809924521770299313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 751999493132058054131501 281999809924521770299313)
                    ·
                      rfl

theorem cell22_823789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_823789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823789 prefixEnd_823789 := by exact prefixLift 823789
  have htrace : WordTrace (prefixWord ++ tailWord_823789) baseStart_823789 baseEnd_823789 := by
    simpa [prefixWord, tailWord_823789, baseEnd_823789] using wordTrace_append hprefix tailTrace_823789
  have hstable : (prefixWord ++ tailWord_823789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823789).length < 2 ^ (prefixWord ++ tailWord_823789).sum := by decide
  have hdescent : baseEnd_823789 < baseStart_823789 := by decide
  rcases family_descends (prefixWord ++ tailWord_823789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823877 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_823877 : Nat := 118140960795 + 823877 * 2 ^ 59
def prefixEnd_823877 : Nat := 4983230072969 + 3 ^ 40 * 823877 * 2
def baseEnd_823877 : Nat := 282029934122918874099043

theorem tailTrace_823877 : CollatzResearch.WordTrace tailWord_823877 prefixEnd_823877 282029934122918874099043 := by
  unfold tailWord_823877
  simp only [CollatzResearch.WordTrace]
  refine ⟨30049262836241810834453885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20032841890827873889635923 30049262836241810834453885)
  ·
    refine ⟨11268473563590679062920207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30049262836241810834453885 11268473563590679062920207)
    ·
      refine ⟨16902710345386018594380311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11268473563590679062920207 16902710345386018594380311)
      ·
        refine ⟨25354065518079027891570467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16902710345386018594380311 25354065518079027891570467)
        ·
          refine ⟨38031098277118541837355701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25354065518079027891570467 38031098277118541837355701)
          ·
            refine ⟨3565415463479863297252097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38031098277118541837355701 3565415463479863297252097)
            ·
              refine ⟨2674061597609897472939073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3565415463479863297252097 2674061597609897472939073)
              ·
                refine ⟨2005546198207423104704305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2674061597609897472939073 2005546198207423104704305)
                ·
                  refine ⟨1504159648655567328528229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2005546198207423104704305 1504159648655567328528229)
                  ·
                    refine ⟨282029934122918874099043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1504159648655567328528229 282029934122918874099043)
                    ·
                      rfl

theorem cell22_823877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_823877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823877 prefixEnd_823877 := by exact prefixLift 823877
  have htrace : WordTrace (prefixWord ++ tailWord_823877) baseStart_823877 baseEnd_823877 := by
    simpa [prefixWord, tailWord_823877, baseEnd_823877] using wordTrace_append hprefix tailTrace_823877
  have hstable : (prefixWord ++ tailWord_823877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823877).length < 2 ^ (prefixWord ++ tailWord_823877).sum := by decide
  have hdescent : baseEnd_823877 < baseStart_823877 := by decide
  rcases family_descends (prefixWord ++ tailWord_823877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823879 : List Nat := [1, 1, 4, 1, 4, 1, 1, 4, 2, 3]
def baseStart_823879 : Nat := 118140960795 + 823879 * 2 ^ 59
def prefixEnd_823879 : Nat := 4983230072969 + 3 ^ 40 * 823879 * 2
def baseEnd_823879 : Nat := 282030618763791535549037

theorem tailTrace_823879 : CollatzResearch.WordTrace tailWord_823879 prefixEnd_823879 282030618763791535549037 := by
  unfold tailWord_823879
  simp only [CollatzResearch.WordTrace]
  refine ⟨30049335782234565176026691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20032890521489710117351127 30049335782234565176026691)
  ·
    refine ⟨45074003673351847764040037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30049335782234565176026691 45074003673351847764040037)
    ·
      refine ⟨8451375688753471455757507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45074003673351847764040037 8451375688753471455757507)
      ·
        refine ⟨12677063533130207183636261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8451375688753471455757507 12677063533130207183636261)
        ·
          refine ⟨2376949412461913846931799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12677063533130207183636261 2376949412461913846931799)
          ·
            refine ⟨3565424118692870770397699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376949412461913846931799 3565424118692870770397699)
            ·
              refine ⟨5348136178039306155596549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3565424118692870770397699 5348136178039306155596549)
              ·
                refine ⟨1002775533382369904174353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5348136178039306155596549 1002775533382369904174353)
                ·
                  refine ⟨752081650036777428130765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1002775533382369904174353 752081650036777428130765)
                  ·
                    refine ⟨282030618763791535549037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 752081650036777428130765 282030618763791535549037)
                    ·
                      rfl

theorem cell22_823879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_823879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823879 prefixEnd_823879 := by exact prefixLift 823879
  have htrace : WordTrace (prefixWord ++ tailWord_823879) baseStart_823879 baseEnd_823879 := by
    simpa [prefixWord, tailWord_823879, baseEnd_823879] using wordTrace_append hprefix tailTrace_823879
  have hstable : (prefixWord ++ tailWord_823879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823879).length < 2 ^ (prefixWord ++ tailWord_823879).sum := by decide
  have hdescent : baseEnd_823879 < baseStart_823879 := by decide
  rcases family_descends (prefixWord ++ tailWord_823879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823892 : List Nat := [2, 4, 1, 1, 1, 3, 3, 7]
def baseStart_823892 : Nat := 118140960795 + 823892 * 2 ^ 59
def prefixEnd_823892 : Nat := 4983230072969 + 3 ^ 40 * 823892 * 2
def baseEnd_823892 : Nat := 31337229881051537219333

theorem tailTrace_823892 : CollatzResearch.WordTrace tailWord_823892 prefixEnd_823892 31337229881051537219333 := by
  unfold tailWord_823892
  simp only [CollatzResearch.WordTrace]
  refine ⟨15024904965593734198124965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20033206620791645597499953 15024904965593734198124965)
  ·
    refine ⟨2817169681048825162148431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15024904965593734198124965 2817169681048825162148431)
    ·
      refine ⟨4225754521573237743222647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2817169681048825162148431 4225754521573237743222647)
      ·
        refine ⟨6338631782359856614833971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4225754521573237743222647 6338631782359856614833971)
        ·
          refine ⟨9507947673539784922250957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6338631782359856614833971 9507947673539784922250957)
          ·
            refine ⟨3565480377577419345844109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9507947673539784922250957 3565480377577419345844109)
            ·
              refine ⟨1337055141591532254691541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3565480377577419345844109 1337055141591532254691541)
              ·
                refine ⟨31337229881051537219333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1337055141591532254691541 31337229881051537219333)
                ·
                  rfl

theorem cell22_823892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 7].length) (baseStart_823892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823892 prefixEnd_823892 := by exact prefixLift 823892
  have htrace : WordTrace (prefixWord ++ tailWord_823892) baseStart_823892 baseEnd_823892 := by
    simpa [prefixWord, tailWord_823892, baseEnd_823892] using wordTrace_append hprefix tailTrace_823892
  have hstable : (prefixWord ++ tailWord_823892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823892).length < 2 ^ (prefixWord ++ tailWord_823892).sum := by decide
  have hdescent : baseEnd_823892 < baseStart_823892 := by decide
  rcases family_descends (prefixWord ++ tailWord_823892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823909 : List Nat := [1, 3, 1, 3, 4, 1, 3, 6]
def baseStart_823909 : Nat := 118140960795 + 823909 * 2 ^ 59
def prefixEnd_823909 : Nat := 4983230072969 + 3 ^ 40 * 823909 * 2
def baseEnd_823909 : Nat := 31337876486320161922105

theorem tailTrace_823909 : CollatzResearch.WordTrace tailWord_823909 prefixEnd_823909 31337876486320161922105 := by
  unfold tailWord_823909
  simp only [CollatzResearch.WordTrace]
  refine ⟨30050429972125880299618781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20033619981417253533079187 30050429972125880299618781)
  ·
    refine ⟨11268911239547205112357043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30050429972125880299618781 11268911239547205112357043)
    ·
      refine ⟨16903366859320807668535565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11268911239547205112357043 16903366859320807668535565)
      ·
        refine ⟨6338762572245302875700837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16903366859320807668535565 6338762572245302875700837)
        ·
          refine ⟨1188517982295994289193907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6338762572245302875700837 1188517982295994289193907)
          ·
            refine ⟨1782776973443991433790861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188517982295994289193907 1782776973443991433790861)
            ·
              refine ⟨668541365041496787671573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1782776973443991433790861 668541365041496787671573)
              ·
                refine ⟨31337876486320161922105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 668541365041496787671573 31337876486320161922105)
                ·
                  rfl

theorem cell22_823909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 6].length) (baseStart_823909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823909 prefixEnd_823909 := by exact prefixLift 823909
  have htrace : WordTrace (prefixWord ++ tailWord_823909) baseStart_823909 baseEnd_823909 := by
    simpa [prefixWord, tailWord_823909, baseEnd_823909] using wordTrace_append hprefix tailTrace_823909
  have hstable : (prefixWord ++ tailWord_823909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823909).length < 2 ^ (prefixWord ++ tailWord_823909).sum := by decide
  have hdescent : baseEnd_823909 < baseStart_823909 := by decide
  rcases family_descends (prefixWord ++ tailWord_823909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823937 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 7]
def baseStart_823937 : Nat := 118140960795 + 823937 * 2 ^ 59
def prefixEnd_823937 : Nat := 4983230072969 + 3 ^ 40 * 823937 * 2
def baseEnd_823937 : Nat := 94016824449699572532953

theorem tailTrace_823937 : CollatzResearch.WordTrace tailWord_823937 prefixEnd_823937 94016824449699572532953 := by
  unfold tailWord_823937
  simp only [CollatzResearch.WordTrace]
  refine ⟨30051451216024441081638065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20034300810682960721092043 30051451216024441081638065)
  ·
    refine ⟨22538588412018330811228549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30051451216024441081638065 22538588412018330811228549)
    ·
      refine ⟨4225985327253437027105353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22538588412018330811228549 4225985327253437027105353)
      ·
        refine ⟨3169488995440077770329015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4225985327253437027105353 3169488995440077770329015)
        ·
          refine ⟨4754233493160116655493523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3169488995440077770329015 4754233493160116655493523)
          ·
            refine ⟨7131350239740174983240285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4754233493160116655493523 7131350239740174983240285)
            ·
              refine ⟨2674256339902565618715107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7131350239740174983240285 2674256339902565618715107)
              ·
                refine ⟨4011384509853848428072661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2674256339902565618715107 4011384509853848428072661)
                ·
                  refine ⟨94016824449699572532953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4011384509853848428072661 94016824449699572532953)
                  ·
                    rfl

theorem cell22_823937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_823937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823937 prefixEnd_823937 := by exact prefixLift 823937
  have htrace : WordTrace (prefixWord ++ tailWord_823937) baseStart_823937 baseEnd_823937 := by
    simpa [prefixWord, tailWord_823937, baseEnd_823937] using wordTrace_append hprefix tailTrace_823937
  have hstable : (prefixWord ++ tailWord_823937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823937).length < 2 ^ (prefixWord ++ tailWord_823937).sum := by decide
  have hdescent : baseEnd_823937 < baseStart_823937 := by decide
  rcases family_descends (prefixWord ++ tailWord_823937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823941 : List Nat := [1, 3, 1, 1, 4, 2, 2, 4, 1, 3]
def baseStart_823941 : Nat := 118140960795 + 823941 * 2 ^ 59
def prefixEnd_823941 : Nat := 4983230072969 + 3 ^ 40 * 823941 * 2
def baseEnd_823941 : Nat := 282051842630844040498847

theorem tailTrace_823941 : CollatzResearch.WordTrace tailWord_823941 prefixEnd_823941 282051842630844040498847 := by
  unfold tailWord_823941
  simp only [CollatzResearch.WordTrace]
  refine ⟨30051597108009949764783677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20034398072006633176522451 30051597108009949764783677)
  ·
    refine ⟨11269348915503731161793879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30051597108009949764783677 11269348915503731161793879)
    ·
      refine ⟨16904023373255596742690819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11269348915503731161793879 16904023373255596742690819)
      ·
        refine ⟨25356035059883395114036229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16904023373255596742690819 25356035059883395114036229)
        ·
          refine ⟨4754256573728136583881793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25356035059883395114036229 4754256573728136583881793)
          ·
            refine ⟨3565692430296102437911345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4754256573728136583881793 3565692430296102437911345)
            ·
              refine ⟨2674269322722076828433509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3565692430296102437911345 2674269322722076828433509)
              ·
                refine ⟨501425498010389405331283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2674269322722076828433509 501425498010389405331283)
                ·
                  refine ⟨752138247015584107996925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501425498010389405331283 752138247015584107996925)
                  ·
                    refine ⟨282051842630844040498847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 752138247015584107996925 282051842630844040498847)
                    ·
                      rfl

theorem cell22_823941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_823941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823941 prefixEnd_823941 := by exact prefixLift 823941
  have htrace : WordTrace (prefixWord ++ tailWord_823941) baseStart_823941 baseEnd_823941 := by
    simpa [prefixWord, tailWord_823941, baseEnd_823941] using wordTrace_append hprefix tailTrace_823941
  have hstable : (prefixWord ++ tailWord_823941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823941).length < 2 ^ (prefixWord ++ tailWord_823941).sum := by decide
  have hdescent : baseEnd_823941 < baseStart_823941 := by decide
  rcases family_descends (prefixWord ++ tailWord_823941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823999 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 6]
def baseStart_823999 : Nat := 118140960795 + 823999 * 2 ^ 59
def prefixEnd_823999 : Nat := 4983230072969 + 3 ^ 40 * 823999 * 2
def baseEnd_823999 : Nat := 94023899072050407516223

theorem tailTrace_823999 : CollatzResearch.WordTrace tailWord_823999 prefixEnd_823999 94023899072050407516223 := by
  unfold tailWord_823999
  simp only [CollatzResearch.WordTrace]
  refine ⟨30053712541799825670395051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20035808361199883780263367 30053712541799825670395051)
  ·
    refine ⟨45080568812699738505592577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30053712541799825670395051 45080568812699738505592577)
    ·
      refine ⟨33810426609524803879194433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45080568812699738505592577 33810426609524803879194433)
      ·
        refine ⟨25357819957143602909395825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33810426609524803879194433 25357819957143602909395825)
        ·
          refine ⟨19018364967857702182046869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25357819957143602909395825 19018364967857702182046869)
          ·
            refine ⟨891485857868329789783447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19018364967857702182046869 891485857868329789783447)
            ·
              refine ⟨1337228786802494684675171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891485857868329789783447 1337228786802494684675171)
              ·
                refine ⟨2005843180203742027012757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337228786802494684675171 2005843180203742027012757)
                ·
                  refine ⟨94023899072050407516223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2005843180203742027012757 94023899072050407516223)
                  ·
                    rfl

theorem cell22_823999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 6].length) (baseStart_823999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_823999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_823999 prefixEnd_823999 := by exact prefixLift 823999
  have htrace : WordTrace (prefixWord ++ tailWord_823999) baseStart_823999 baseEnd_823999 := by
    simpa [prefixWord, tailWord_823999, baseEnd_823999] using wordTrace_append hprefix tailTrace_823999
  have hstable : (prefixWord ++ tailWord_823999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823999).length < 2 ^ (prefixWord ++ tailWord_823999).sum := by decide
  have hdescent : baseEnd_823999 < baseStart_823999 := by decide
  rcases family_descends (prefixWord ++ tailWord_823999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824018 : List Nat := [3, 2, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_824018 : Nat := 118140960795 + 824018 * 2 ^ 59
def prefixEnd_824018 : Nat := 4983230072969 + 3 ^ 40 * 824018 * 2
def baseEnd_824018 : Nat := 282078201304441506323611

theorem tailTrace_824018 : CollatzResearch.WordTrace tailWord_824018 prefixEnd_824018 282078201304441506323611 := by
  unfold tailWord_824018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7513601382182747978834177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20036270352487327943557805 7513601382182747978834177)
  ·
    refine ⟨5635201036637060984125633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7513601382182747978834177 5635201036637060984125633)
    ·
      refine ⟨4226400777477795738094225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5635201036637060984125633 4226400777477795738094225)
      ·
        refine ⟨3169800583108346803570669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4226400777477795738094225 3169800583108346803570669)
        ·
          refine ⟨1188675218665630051339001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3169800583108346803570669 1188675218665630051339001)
          ·
            refine ⟨891506413999222538504251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188675218665630051339001 891506413999222538504251)
            ·
              refine ⟨1337259620998833807756377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891506413999222538504251 1337259620998833807756377)
              ·
                refine ⟨1002944715749125355817283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1337259620998833807756377 1002944715749125355817283)
                ·
                  refine ⟨1504417073623688033725925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002944715749125355817283 1504417073623688033725925)
                  ·
                    refine ⟨282078201304441506323611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1504417073623688033725925 282078201304441506323611)
                    ·
                      rfl

theorem cell22_824018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_824018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824018 prefixEnd_824018 := by exact prefixLift 824018
  have htrace : WordTrace (prefixWord ++ tailWord_824018) baseStart_824018 baseEnd_824018 := by
    simpa [prefixWord, tailWord_824018, baseEnd_824018] using wordTrace_append hprefix tailTrace_824018
  have hstable : (prefixWord ++ tailWord_824018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824018).length < 2 ^ (prefixWord ++ tailWord_824018).sum := by decide
  have hdescent : baseEnd_824018 < baseStart_824018 := by decide
  rcases family_descends (prefixWord ++ tailWord_824018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824104 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 4, 5]
def baseStart_824104 : Nat := 118140960795 + 824104 * 2 ^ 59
def prefixEnd_824104 : Nat := 4983230072969 + 3 ^ 40 * 824104 * 2
def baseEnd_824104 : Nat := 282107640861965948673347

theorem tailTrace_824104 : CollatzResearch.WordTrace tailWord_824104 prefixEnd_824104 282107640861965948673347 := by
  unfold tailWord_824104
  simp only [CollatzResearch.WordTrace]
  refine ⟨15028771103209714301483683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20038361470946285735311577 15028771103209714301483683)
  ·
    refine ⟨22543156654814571452225525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15028771103209714301483683 22543156654814571452225525)
    ·
      refine ⟨2113420936388866073646143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22543156654814571452225525 2113420936388866073646143)
      ·
        refine ⟨3170131404583299110469215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2113420936388866073646143 3170131404583299110469215)
        ·
          refine ⟨4755197106874948665703823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3170131404583299110469215 4755197106874948665703823)
          ·
            refine ⟨7132795660312422998555735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755197106874948665703823 7132795660312422998555735)
            ·
              refine ⟨10699193490468634497833603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7132795660312422998555735 10699193490468634497833603)
              ·
                refine ⟨16048790235702951746750405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10699193490468634497833603 16048790235702951746750405)
                ·
                  refine ⟨3009148169194303452515701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16048790235702951746750405 3009148169194303452515701)
                  ·
                    refine ⟨282107640861965948673347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3009148169194303452515701 282107640861965948673347)
                    ·
                      rfl

theorem cell22_824104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_824104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824104 prefixEnd_824104 := by exact prefixLift 824104
  have htrace : WordTrace (prefixWord ++ tailWord_824104) baseStart_824104 baseEnd_824104 := by
    simpa [prefixWord, tailWord_824104, baseEnd_824104] using wordTrace_append hprefix tailTrace_824104
  have hstable : (prefixWord ++ tailWord_824104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824104).length < 2 ^ (prefixWord ++ tailWord_824104).sum := by decide
  have hdescent : baseEnd_824104 < baseStart_824104 := by decide
  rcases family_descends (prefixWord ++ tailWord_824104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824110 : List Nat := [4, 1, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_824110 : Nat := 118140960795 + 824110 * 2 ^ 59
def prefixEnd_824110 : Nat := 4983230072969 + 3 ^ 40 * 824110 * 2
def baseEnd_824110 : Nat := 282109694784583933023329

theorem tailTrace_824110 : CollatzResearch.WordTrace tailWord_824110 prefixEnd_824110 282109694784583933023329 := by
  unfold tailWord_824110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3757220130549711453460723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20038507362931794418457189 3757220130549711453460723)
  ·
    refine ⟨5635830195824567180191085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3757220130549711453460723 5635830195824567180191085)
    ·
      refine ⟨2113436323434212692571657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5635830195824567180191085 2113436323434212692571657)
      ·
        refine ⟨1585077242575659519428743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2113436323434212692571657 1585077242575659519428743)
        ·
          refine ⟨2377615863863489279143115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1585077242575659519428743 2377615863863489279143115)
          ·
            refine ⟨3566423795795233918714673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2377615863863489279143115 3566423795795233918714673)
            ·
              refine ⟨2674817846846425439036005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3566423795795233918714673 2674817846846425439036005)
              ·
                refine ⟨501528346283704769819251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2674817846846425439036005 501528346283704769819251)
                ·
                  refine ⟨752292519425557154728877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501528346283704769819251 752292519425557154728877)
                  ·
                    refine ⟨282109694784583933023329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 752292519425557154728877 282109694784583933023329)
                    ·
                      rfl

theorem cell22_824110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_824110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824110 prefixEnd_824110 := by exact prefixLift 824110
  have htrace : WordTrace (prefixWord ++ tailWord_824110) baseStart_824110 baseEnd_824110 := by
    simpa [prefixWord, tailWord_824110, baseEnd_824110] using wordTrace_append hprefix tailTrace_824110
  have hstable : (prefixWord ++ tailWord_824110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824110).length < 2 ^ (prefixWord ++ tailWord_824110).sum := by decide
  have hdescent : baseEnd_824110 < baseStart_824110 := by decide
  rcases family_descends (prefixWord ++ tailWord_824110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824136 : List Nat := [2, 1, 3, 1, 1, 3, 4, 2, 1, 4]
def baseStart_824136 : Nat := 118140960795 + 824136 * 2 ^ 59
def prefixEnd_824136 : Nat := 4983230072969 + 3 ^ 40 * 824136 * 2
def baseEnd_824136 : Nat := 282118595115928531873249

theorem tailTrace_824136 : CollatzResearch.WordTrace tailWord_824136 prefixEnd_824136 282118595115928531873249 := by
  unfold tailWord_824136
  simp only [CollatzResearch.WordTrace]
  refine ⟨15029354671151749034066131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20039139561535665378754841 15029354671151749034066131)
  ·
    refine ⟨22544032006727623551099197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15029354671151749034066131 22544032006727623551099197)
    ·
      refine ⟨8454012002522858831662199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22544032006727623551099197 8454012002522858831662199)
      ·
        refine ⟨12681018003784288247493299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8454012002522858831662199 12681018003784288247493299)
        ·
          refine ⟨19021527005676432371239949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12681018003784288247493299 19021527005676432371239949)
          ·
            refine ⟨7133072627128662139214981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19021527005676432371239949 7133072627128662139214981)
            ·
              refine ⟨1337451117586624151102809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7133072627128662139214981 1337451117586624151102809)
              ·
                refine ⟨1003088338189968113327107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1337451117586624151102809 1003088338189968113327107)
                ·
                  refine ⟨1504632507284952169990661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003088338189968113327107 1504632507284952169990661)
                  ·
                    refine ⟨282118595115928531873249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1504632507284952169990661 282118595115928531873249)
                    ·
                      rfl

theorem cell22_824136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_824136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824136 prefixEnd_824136 := by exact prefixLift 824136
  have htrace : WordTrace (prefixWord ++ tailWord_824136) baseStart_824136 baseEnd_824136 := by
    simpa [prefixWord, tailWord_824136, baseEnd_824136] using wordTrace_append hprefix tailTrace_824136
  have hstable : (prefixWord ++ tailWord_824136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824136).length < 2 ^ (prefixWord ++ tailWord_824136).sum := by decide
  have hdescent : baseEnd_824136 < baseStart_824136 := by decide
  rcases family_descends (prefixWord ++ tailWord_824136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824149 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_824149 : Nat := 118140960795 + 824149 * 2 ^ 59
def prefixEnd_824149 : Nat := 4983230072969 + 3 ^ 40 * 824149 * 2
def baseEnd_824149 : Nat := 282123045281600831298209

theorem tailTrace_824149 : CollatzResearch.WordTrace tailWord_824149 prefixEnd_824149 282123045281600831298209 := by
  unfold tailWord_824149
  simp only [CollatzResearch.WordTrace]
  refine ⟨30059183491256401288355501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20039455660837600858903667 30059183491256401288355501)
  ·
    refine ⟨11272193809221150483133313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30059183491256401288355501 11272193809221150483133313)
    ·
      refine ⟨8454145356915862862349985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11272193809221150483133313 8454145356915862862349985)
      ·
        refine ⟨6340609017686897146762489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8454145356915862862349985 6340609017686897146762489)
        ·
          refine ⟨4755456763265172860071867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6340609017686897146762489 4755456763265172860071867)
          ·
            refine ⟨7133185144897759290107801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755456763265172860071867 7133185144897759290107801)
            ·
              refine ⟨5349888858673319467580851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7133185144897759290107801 5349888858673319467580851)
              ·
                refine ⟨8024833288009979201371277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5349888858673319467580851 8024833288009979201371277)
                ·
                  refine ⟨3009312483003742200514229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8024833288009979201371277 3009312483003742200514229)
                  ·
                    refine ⟨282123045281600831298209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3009312483003742200514229 282123045281600831298209)
                    ·
                      rfl

theorem cell22_824149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_824149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824149 prefixEnd_824149 := by exact prefixLift 824149
  have htrace : WordTrace (prefixWord ++ tailWord_824149) baseStart_824149 baseEnd_824149 := by
    simpa [prefixWord, tailWord_824149, baseEnd_824149] using wordTrace_append hprefix tailTrace_824149
  have hstable : (prefixWord ++ tailWord_824149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824149).length < 2 ^ (prefixWord ++ tailWord_824149).sum := by decide
  have hdescent : baseEnd_824149 < baseStart_824149 := by decide
  rcases family_descends (prefixWord ++ tailWord_824149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824224 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 7]
def baseStart_824224 : Nat := 118140960795 + 824224 * 2 ^ 59
def prefixEnd_824224 : Nat := 4983230072969 + 3 ^ 40 * 824224 * 2
def baseEnd_824224 : Nat := 94049573104775211890993

theorem tailTrace_824224 : CollatzResearch.WordTrace tailWord_824224 prefixEnd_824224 94049573104775211890993 := by
  unfold tailWord_824224
  simp only [CollatzResearch.WordTrace]
  refine ⟨15030959482992344548667863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20041279310656459398223817 15030959482992344548667863)
  ·
    refine ⟨22546439224488516823001795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15030959482992344548667863 22546439224488516823001795)
    ·
      refine ⟨33819658836732775234502693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22546439224488516823001795 33819658836732775234502693)
      ·
        refine ⟨6341186031887395356469255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33819658836732775234502693 6341186031887395356469255)
        ·
          refine ⟨9511779047831093034703883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6341186031887395356469255 9511779047831093034703883)
          ·
            refine ⟨14267668571746639552055825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9511779047831093034703883 14267668571746639552055825)
            ·
              refine ⟨10700751428809979664041869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14267668571746639552055825 10700751428809979664041869)
              ·
                refine ⟨4012781785803742374015701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10700751428809979664041869 4012781785803742374015701)
                ·
                  refine ⟨94049573104775211890993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4012781785803742374015701 94049573104775211890993)
                  ·
                    rfl

theorem cell22_824224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_824224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824224 prefixEnd_824224 := by exact prefixLift 824224
  have htrace : WordTrace (prefixWord ++ tailWord_824224) baseStart_824224 baseEnd_824224 := by
    simpa [prefixWord, tailWord_824224, baseEnd_824224] using wordTrace_append hprefix tailTrace_824224
  have hstable : (prefixWord ++ tailWord_824224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824224).length < 2 ^ (prefixWord ++ tailWord_824224).sum := by decide
  have hdescent : baseEnd_824224 < baseStart_824224 := by decide
  rcases family_descends (prefixWord ++ tailWord_824224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824226 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_824226 : Nat := 118140960795 + 824226 * 2 ^ 59
def prefixEnd_824226 : Nat := 4983230072969 + 3 ^ 40 * 824226 * 2
def baseEnd_824226 : Nat := 282149403955198297122973

theorem tailTrace_824226 : CollatzResearch.WordTrace tailWord_824226 prefixEnd_824226 282149403955198297122973 := by
  unfold tailWord_824226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7515497977994360859727133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20041327941318295625939021 7515497977994360859727133)
  ·
    refine ⟨2818311741747885322397675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7515497977994360859727133 2818311741747885322397675)
    ·
      refine ⟨4227467612621827983596513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2818311741747885322397675 4227467612621827983596513)
      ·
        refine ⟨3170600709466370987697385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4227467612621827983596513 3170600709466370987697385)
        ·
          refine ⟨2377950532099778240773039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3170600709466370987697385 2377950532099778240773039)
          ·
            refine ⟨3566925798149667361159559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2377950532099778240773039 3566925798149667361159559)
            ·
              refine ⟨5350388697224501041739339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3566925798149667361159559 5350388697224501041739339)
              ·
                refine ⟨8025583045836751562609009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5350388697224501041739339 8025583045836751562609009)
                ·
                  refine ⟨6019187284377563671956757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8025583045836751562609009 6019187284377563671956757)
                  ·
                    refine ⟨282149403955198297122973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6019187284377563671956757 282149403955198297122973)
                    ·
                      rfl

theorem cell22_824226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_824226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824226 prefixEnd_824226 := by exact prefixLift 824226
  have htrace : WordTrace (prefixWord ++ tailWord_824226) baseStart_824226 baseEnd_824226 := by
    simpa [prefixWord, tailWord_824226, baseEnd_824226] using wordTrace_append hprefix tailTrace_824226
  have hstable : (prefixWord ++ tailWord_824226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824226).length < 2 ^ (prefixWord ++ tailWord_824226).sum := by decide
  have hdescent : baseEnd_824226 < baseStart_824226 := by decide
  rcases family_descends (prefixWord ++ tailWord_824226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824316 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_824316 : Nat := 118140960795 + 824316 * 2 ^ 59
def prefixEnd_824316 : Nat := 4983230072969 + 3 ^ 40 * 824316 * 2
def baseEnd_824316 : Nat := 282180212794468062372697

theorem tailTrace_824316 : CollatzResearch.WordTrace tailWord_824316 prefixEnd_824316 282180212794468062372697 := by
  unfold tailWord_824316
  simp only [CollatzResearch.WordTrace]
  refine ⟨15032637240825694404842401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20043516321100925873123201 15032637240825694404842401)
  ·
    refine ⟨11274477930619270803631801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15032637240825694404842401 11274477930619270803631801)
    ·
      refine ⟨8455858447964453102723851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11274477930619270803631801 8455858447964453102723851)
      ·
        refine ⟨12683787671946679654085777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8455858447964453102723851 12683787671946679654085777)
        ·
          refine ⟨9512840753960009740564333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12683787671946679654085777 9512840753960009740564333)
          ·
            refine ⟨3567315282735003652711625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9512840753960009740564333 3567315282735003652711625)
            ·
              refine ⟨2675486462051252739533719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3567315282735003652711625 2675486462051252739533719)
              ·
                refine ⟨4013229693076879109300579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675486462051252739533719 4013229693076879109300579)
                ·
                  refine ⟨6019844539615318663950869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4013229693076879109300579 6019844539615318663950869)
                  ·
                    refine ⟨282180212794468062372697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6019844539615318663950869 282180212794468062372697)
                    ·
                      rfl

theorem cell22_824316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_824316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824316 prefixEnd_824316 := by exact prefixLift 824316
  have htrace : WordTrace (prefixWord ++ tailWord_824316) baseStart_824316 baseEnd_824316 := by
    simpa [prefixWord, tailWord_824316, baseEnd_824316] using wordTrace_append hprefix tailTrace_824316
  have hstable : (prefixWord ++ tailWord_824316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824316).length < 2 ^ (prefixWord ++ tailWord_824316).sum := by decide
  have hdescent : baseEnd_824316 < baseStart_824316 := by decide
  rcases family_descends (prefixWord ++ tailWord_824316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824331 : List Nat := [1, 1, 1, 1, 6, 4, 8]
def baseStart_824331 : Nat := 118140960795 + 824331 * 2 ^ 59
def prefixEnd_824331 : Nat := 4983230072969 + 3 ^ 40 * 824331 * 2
def baseEnd_824331 : Nat := 10451309170407889749913

theorem tailTrace_824331 : CollatzResearch.WordTrace tailWord_824331 prefixEnd_824331 10451309170407889749913 := by
  unfold tailWord_824331
  simp only [CollatzResearch.WordTrace]
  refine ⟨30065821576597046371480847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20043881051064697580987231 30065821576597046371480847)
  ·
    refine ⟨45098732364895569557221271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30065821576597046371480847 45098732364895569557221271)
    ·
      refine ⟨67648098547343354335831907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45098732364895569557221271 67648098547343354335831907)
      ·
        refine ⟨101472147821015031503747861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67648098547343354335831907 101472147821015031503747861)
        ·
          refine ⟨4756506929110079601738181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101472147821015031503747861 4756506929110079601738181)
          ·
            refine ⟨891845049208139925325909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4756506929110079601738181 891845049208139925325909)
            ·
              refine ⟨10451309170407889749913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 891845049208139925325909 10451309170407889749913)
              ·
                rfl

theorem cell22_824331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 8].length) (baseStart_824331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824331 prefixEnd_824331 := by exact prefixLift 824331
  have htrace : WordTrace (prefixWord ++ tailWord_824331) baseStart_824331 baseEnd_824331 := by
    simpa [prefixWord, tailWord_824331, baseEnd_824331] using wordTrace_append hprefix tailTrace_824331
  have hstable : (prefixWord ++ tailWord_824331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824331).length < 2 ^ (prefixWord ++ tailWord_824331).sum := by decide
  have hdescent : baseEnd_824331 < baseStart_824331 := by decide
  rcases family_descends (prefixWord ++ tailWord_824331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824348 : List Nat := [2, 2, 3, 1, 4, 1, 2, 7]
def baseStart_824348 : Nat := 118140960795 + 824348 * 2 ^ 59
def prefixEnd_824348 : Nat := 4983230072969 + 3 ^ 40 * 824348 * 2
def baseEnd_824348 : Nat := 31354574116492293952511

theorem tailTrace_824348 : CollatzResearch.WordTrace tailWord_824348 prefixEnd_824348 31354574116492293952511 := by
  unfold tailWord_824348
  simp only [CollatzResearch.WordTrace]
  refine ⟨15033220808767729137424849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20044294411690305516566465 15033220808767729137424849)
  ·
    refine ⟨11274915606575796853068637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15033220808767729137424849 11274915606575796853068637)
    ·
      refine ⟨4228093352465923819900739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11274915606575796853068637 4228093352465923819900739)
      ·
        refine ⟨6342140028698885729851109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4228093352465923819900739 6342140028698885729851109)
        ·
          refine ⟨1189151255381041074347083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6342140028698885729851109 1189151255381041074347083)
          ·
            refine ⟨1783726883071561611520625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189151255381041074347083 1783726883071561611520625)
            ·
              refine ⟨1337795162303671208640469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1783726883071561611520625 1337795162303671208640469)
              ·
                refine ⟨31354574116492293952511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1337795162303671208640469 31354574116492293952511)
                ·
                  rfl

theorem cell22_824348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 7].length) (baseStart_824348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824348 prefixEnd_824348 := by exact prefixLift 824348
  have htrace : WordTrace (prefixWord ++ tailWord_824348) baseStart_824348 baseEnd_824348 := by
    simpa [prefixWord, tailWord_824348, baseEnd_824348] using wordTrace_append hprefix tailTrace_824348
  have hstable : (prefixWord ++ tailWord_824348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824348).length < 2 ^ (prefixWord ++ tailWord_824348).sum := by decide
  have hdescent : baseEnd_824348 < baseStart_824348 := by decide
  rcases family_descends (prefixWord ++ tailWord_824348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824352 : List Nat := [2, 1, 1, 7, 1, 1, 1, 3, 2, 3]
def baseStart_824352 : Nat := 118140960795 + 824352 * 2 ^ 59
def prefixEnd_824352 : Nat := 4983230072969 + 3 ^ 40 * 824352 * 2
def baseEnd_824352 : Nat := 282192536330175968472587

theorem tailTrace_824352 : CollatzResearch.WordTrace tailWord_824352 prefixEnd_824352 282192536330175968472587 := by
  unfold tailWord_824352
  simp only [CollatzResearch.WordTrace]
  refine ⟨15033293754760483478997655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20044391673013977971996873 15033293754760483478997655)
  ·
    refine ⟨22549940632140725218496483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15033293754760483478997655 22549940632140725218496483)
    ·
      refine ⟨33824910948211087827744725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22549940632140725218496483 33824910948211087827744725)
      ·
        refine ⟨792771350348697370962767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 33824910948211087827744725 792771350348697370962767)
        ·
          refine ⟨1189157025523046056444151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792771350348697370962767 1189157025523046056444151)
          ·
            refine ⟨1783735538284569084666227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189157025523046056444151 1783735538284569084666227)
            ·
              refine ⟨2675603307426853626999341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783735538284569084666227 2675603307426853626999341)
              ·
                refine ⟨1003351240285070110124753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2675603307426853626999341 1003351240285070110124753)
                ·
                  refine ⟨752513430213802582593565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1003351240285070110124753 752513430213802582593565)
                  ·
                    refine ⟨282192536330175968472587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 752513430213802582593565 282192536330175968472587)
                    ·
                      rfl

theorem cell22_824352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 2, 3].length) (baseStart_824352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824352 prefixEnd_824352 := by exact prefixLift 824352
  have htrace : WordTrace (prefixWord ++ tailWord_824352) baseStart_824352 baseEnd_824352 := by
    simpa [prefixWord, tailWord_824352, baseEnd_824352] using wordTrace_append hprefix tailTrace_824352
  have hstable : (prefixWord ++ tailWord_824352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824352).length < 2 ^ (prefixWord ++ tailWord_824352).sum := by decide
  have hdescent : baseEnd_824352 < baseStart_824352 := by decide
  rcases family_descends (prefixWord ++ tailWord_824352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824414 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_824414 : Nat := 118140960795 + 824414 * 2 ^ 59
def prefixEnd_824414 : Nat := 4983230072969 + 3 ^ 40 * 824414 * 2
def baseEnd_824414 : Nat := 282213760197228473422397

theorem tailTrace_824414 : CollatzResearch.WordTrace tailWord_824414 prefixEnd_824414 282213760197228473422397 := by
  unfold tailWord_824414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3758606104412043943344037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20045899223530901031168197 3758606104412043943344037)
  ·
    refine ⟨704738644577258239377007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3758606104412043943344037 704738644577258239377007)
    ·
      refine ⟨1057107966865887359065511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 704738644577258239377007 1057107966865887359065511)
      ·
        refine ⟨1585661950298831038598267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057107966865887359065511 1585661950298831038598267)
        ·
          refine ⟨2378492925448246557897401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1585661950298831038598267 2378492925448246557897401)
          ·
            refine ⟨1783869694086184918423051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2378492925448246557897401 1783869694086184918423051)
            ·
              refine ⟨2675804541129277377634577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783869694086184918423051 2675804541129277377634577)
              ·
                refine ⟨2006853405846958033225933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2675804541129277377634577 2006853405846958033225933)
                ·
                  refine ⟨752570027192609262459725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2006853405846958033225933 752570027192609262459725)
                  ·
                    refine ⟨282213760197228473422397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 752570027192609262459725 282213760197228473422397)
                    ·
                      rfl

theorem cell22_824414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_824414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824414 prefixEnd_824414 := by exact prefixLift 824414
  have htrace : WordTrace (prefixWord ++ tailWord_824414) baseStart_824414 baseEnd_824414 := by
    simpa [prefixWord, tailWord_824414, baseEnd_824414] using wordTrace_append hprefix tailTrace_824414
  have hstable : (prefixWord ++ tailWord_824414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824414).length < 2 ^ (prefixWord ++ tailWord_824414).sum := by decide
  have hdescent : baseEnd_824414 < baseStart_824414 := by decide
  rcases family_descends (prefixWord ++ tailWord_824414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824423 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 3, 4]
def baseStart_824423 : Nat := 118140960795 + 824423 * 2 ^ 59
def prefixEnd_824423 : Nat := 4983230072969 + 3 ^ 40 * 824423 * 2
def baseEnd_824423 : Nat := 282216841081155449947369

theorem tailTrace_824423 : CollatzResearch.WordTrace tailWord_824423 prefixEnd_824423 282216841081155449947369 := by
  unfold tailWord_824423
  simp only [CollatzResearch.WordTrace]
  refine ⟨30069177092263746083829923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20046118061509164055886615 30069177092263746083829923)
  ·
    refine ⟨45103765638395619125744885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30069177092263746083829923 45103765638395619125744885)
    ·
      refine ⟨4228478028599589293038583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45103765638395619125744885 4228478028599589293038583)
      ·
        refine ⟨6342717042899383939557875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4228478028599589293038583 6342717042899383939557875)
        ·
          refine ⟨9514075564349075909336813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6342717042899383939557875 9514075564349075909336813)
          ·
            refine ⟨3567778336630903466001305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9514075564349075909336813 3567778336630903466001305)
            ·
              refine ⟨2675833752473177599500979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3567778336630903466001305 2675833752473177599500979)
              ·
                refine ⟨4013750628709766399251469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675833752473177599500979 4013750628709766399251469)
                ·
                  refine ⟨1505156485766162399719301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4013750628709766399251469 1505156485766162399719301)
                  ·
                    refine ⟨282216841081155449947369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1505156485766162399719301 282216841081155449947369)
                    ·
                      rfl

theorem cell22_824423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_824423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824423 prefixEnd_824423 := by exact prefixLift 824423
  have htrace : WordTrace (prefixWord ++ tailWord_824423) baseStart_824423 baseEnd_824423 := by
    simpa [prefixWord, tailWord_824423, baseEnd_824423] using wordTrace_append hprefix tailTrace_824423
  have hstable : (prefixWord ++ tailWord_824423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824423).length < 2 ^ (prefixWord ++ tailWord_824423).sum := by decide
  have hdescent : baseEnd_824423 < baseStart_824423 := by decide
  rcases family_descends (prefixWord ++ tailWord_824423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824438 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_824438 : Nat := 118140960795 + 824438 * 2 ^ 59
def prefixEnd_824438 : Nat := 4983230072969 + 3 ^ 40 * 824438 * 2
def baseEnd_824438 : Nat := 94073991962566803607441

theorem tailTrace_824438 : CollatzResearch.WordTrace tailWord_824438 prefixEnd_824438 94073991962566803607441 := by
  unfold tailWord_824438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1879357761700587727851623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20046482791472935763750645 1879357761700587727851623)
  ·
    refine ⟨2819036642550881591777435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1879357761700587727851623 2819036642550881591777435)
    ·
      refine ⟨4228554963826322387666153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2819036642550881591777435 4228554963826322387666153)
      ·
        refine ⟨3171416222869741790749615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4228554963826322387666153 3171416222869741790749615)
        ·
          refine ⟨4757124334304612686124423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171416222869741790749615 4757124334304612686124423)
          ·
            refine ⟨7135686501456919029186635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4757124334304612686124423 7135686501456919029186635)
            ·
              refine ⟨10703529752185378543779953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7135686501456919029186635 10703529752185378543779953)
              ·
                refine ⟨8027647314139033907834965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10703529752185378543779953 8027647314139033907834965)
                ·
                  refine ⟨94073991962566803607441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8027647314139033907834965 94073991962566803607441)
                  ·
                    rfl

theorem cell22_824438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_824438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824438 prefixEnd_824438 := by exact prefixLift 824438
  have htrace : WordTrace (prefixWord ++ tailWord_824438) baseStart_824438 baseEnd_824438 := by
    simpa [prefixWord, tailWord_824438, baseEnd_824438] using wordTrace_append hprefix tailTrace_824438
  have hstable : (prefixWord ++ tailWord_824438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824438).length < 2 ^ (prefixWord ++ tailWord_824438).sum := by decide
  have hdescent : baseEnd_824438 < baseStart_824438 := by decide
  rcases family_descends (prefixWord ++ tailWord_824438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824440 : List Nat := [2, 1, 2, 1, 1, 1, 8, 1, 1, 4]
def baseStart_824440 : Nat := 118140960795 + 824440 * 2 ^ 59
def prefixEnd_824440 : Nat := 4983230072969 + 3 ^ 40 * 824440 * 2
def baseEnd_824440 : Nat := 282222660528573072272317

theorem tailTrace_824440 : CollatzResearch.WordTrace tailWord_824440 prefixEnd_824440 282222660528573072272317 := by
  unfold tailWord_824440
  simp only [CollatzResearch.WordTrace]
  refine ⟨15034898566601078993599387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20046531422134771991465849 15034898566601078993599387)
  ·
    refine ⟨22552347849901618490399081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15034898566601078993599387 22552347849901618490399081)
    ·
      refine ⟨16914260887426213867799311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22552347849901618490399081 16914260887426213867799311)
      ·
        refine ⟨25371391331139320801698967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16914260887426213867799311 25371391331139320801698967)
        ·
          refine ⟨38057086996708981202548451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25371391331139320801698967 38057086996708981202548451)
          ·
            refine ⟨57085630495063471803822677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38057086996708981202548451 57085630495063471803822677)
            ·
              refine ⟨668972232364025060201047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 57085630495063471803822677 668972232364025060201047)
              ·
                refine ⟨1003458348546037590301571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668972232364025060201047 1003458348546037590301571)
                ·
                  refine ⟨1505187522819056385452357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003458348546037590301571 1505187522819056385452357)
                  ·
                    refine ⟨282222660528573072272317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1505187522819056385452357 282222660528573072272317)
                    ·
                      rfl

theorem cell22_824440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_824440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824440 prefixEnd_824440 := by exact prefixLift 824440
  have htrace : WordTrace (prefixWord ++ tailWord_824440) baseStart_824440 baseEnd_824440 := by
    simpa [prefixWord, tailWord_824440, baseEnd_824440] using wordTrace_append hprefix tailTrace_824440
  have hstable : (prefixWord ++ tailWord_824440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824440).length < 2 ^ (prefixWord ++ tailWord_824440).sum := by decide
  have hdescent : baseEnd_824440 < baseStart_824440 := by decide
  rcases family_descends (prefixWord ++ tailWord_824440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824562 : List Nat := [3, 2, 1, 3, 3, 1, 2, 2, 5]
def baseStart_824562 : Nat := 118140960795 + 824562 * 2 ^ 59
def prefixEnd_824562 : Nat := 4983230072969 + 3 ^ 40 * 824562 * 2
def baseEnd_824562 : Nat := 94088141207268473573981

theorem tailTrace_824562 : CollatzResearch.WordTrace tailWord_824562 prefixEnd_824562 94088141207268473573981 := by
  unfold tailWord_824562
  simp only [CollatzResearch.WordTrace]
  refine ⟨7518561709690043205784985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20049497892506781882093293 7518561709690043205784985)
  ·
    refine ⟨5638921282267532404338739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7518561709690043205784985 5638921282267532404338739)
    ·
      refine ⟨8458381923401298606508109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5638921282267532404338739 8458381923401298606508109)
      ·
        refine ⟨3171893221275486977440541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8458381923401298606508109 3171893221275486977440541)
        ·
          refine ⟨1189459957978307616540203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3171893221275486977440541 1189459957978307616540203)
          ·
            refine ⟨1784189936967461424810305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189459957978307616540203 1784189936967461424810305)
            ·
              refine ⟨1338142452725596068607729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784189936967461424810305 1338142452725596068607729)
              ·
                refine ⟨1003606839544197051455797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1338142452725596068607729 1003606839544197051455797)
                ·
                  refine ⟨94088141207268473573981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1003606839544197051455797 94088141207268473573981)
                  ·
                    rfl

theorem cell22_824562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_824562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824562 prefixEnd_824562 := by exact prefixLift 824562
  have htrace : WordTrace (prefixWord ++ tailWord_824562) baseStart_824562 baseEnd_824562 := by
    simpa [prefixWord, tailWord_824562, baseEnd_824562] using wordTrace_append hprefix tailTrace_824562
  have hstable : (prefixWord ++ tailWord_824562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824562).length < 2 ^ (prefixWord ++ tailWord_824562).sum := by decide
  have hdescent : baseEnd_824562 < baseStart_824562 := by decide
  rcases family_descends (prefixWord ++ tailWord_824562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824590 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_824590 : Nat := 118140960795 + 824590 * 2 ^ 59
def prefixEnd_824590 : Nat := 4983230072969 + 3 ^ 40 * 824590 * 2
def baseEnd_824590 : Nat := 94091336198007560340619

theorem tailTrace_824590 : CollatzResearch.WordTrace tailWord_824590 prefixEnd_824590 94091336198007560340619 := by
  unfold tailWord_824590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3759408510332341700644903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20050178721772489070106149 3759408510332341700644903)
  ·
    refine ⟨5639112765498512550967355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3759408510332341700644903 5639112765498512550967355)
    ·
      refine ⟨8458669148247768826451033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5639112765498512550967355 8458669148247768826451033)
      ·
        refine ⟨6344001861185826619838275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8458669148247768826451033 6344001861185826619838275)
        ·
          refine ⟨9516002791778739929757413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6344001861185826619838275 9516002791778739929757413)
          ·
            refine ⟨1784250523458513736829515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9516002791778739929757413 1784250523458513736829515)
            ·
              refine ⟨2676375785187770605244273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784250523458513736829515 2676375785187770605244273)
              ·
                refine ⟨2007281838890827953933205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2676375785187770605244273 2007281838890827953933205)
                ·
                  refine ⟨94091336198007560340619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2007281838890827953933205 94091336198007560340619)
                  ·
                    rfl

theorem cell22_824590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_824590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824590 prefixEnd_824590 := by exact prefixLift 824590
  have htrace : WordTrace (prefixWord ++ tailWord_824590) baseStart_824590 baseEnd_824590 := by
    simpa [prefixWord, tailWord_824590, baseEnd_824590] using wordTrace_append hprefix tailTrace_824590
  have hstable : (prefixWord ++ tailWord_824590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824590).length < 2 ^ (prefixWord ++ tailWord_824590).sum := by decide
  have hdescent : baseEnd_824590 < baseStart_824590 := by decide
  rcases family_descends (prefixWord ++ tailWord_824590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824639 : List Nat := [1, 1, 2, 2, 4, 3, 3, 1, 2, 3]
def baseStart_824639 : Nat := 118140960795 + 824639 * 2 ^ 59
def prefixEnd_824639 : Nat := 4983230072969 + 3 ^ 40 * 824639 * 2
def baseEnd_824639 : Nat := 282290782295402886546707

theorem tailTrace_824639 : CollatzResearch.WordTrace tailWord_824639 prefixEnd_824639 282290782295402886546707 := by
  unfold tailWord_824639
  simp only [CollatzResearch.WordTrace]
  refine ⟨30077055259481214973692971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20051370172987476649128647 30077055259481214973692971)
  ·
    refine ⟨45115582889221822460539457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30077055259481214973692971 45115582889221822460539457)
    ·
      refine ⟨33836687166916366845404593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45115582889221822460539457 33836687166916366845404593)
      ·
        refine ⟨25377515375187275134053445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33836687166916366845404593 25377515375187275134053445)
        ·
          refine ⟨4758284132847614087635021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25377515375187275134053445 4758284132847614087635021)
          ·
            refine ⟨1784356549817855282863133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4758284132847614087635021 1784356549817855282863133)
            ·
              refine ⟨669133706181695731073675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1784356549817855282863133 669133706181695731073675)
              ·
                refine ⟨1003700559272543596610513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669133706181695731073675 1003700559272543596610513)
                ·
                  refine ⟨752775419454407697457885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1003700559272543596610513 752775419454407697457885)
                  ·
                    refine ⟨282290782295402886546707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 752775419454407697457885 282290782295402886546707)
                    ·
                      rfl

theorem cell22_824639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 2, 3].length) (baseStart_824639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824639 prefixEnd_824639 := by exact prefixLift 824639
  have htrace : WordTrace (prefixWord ++ tailWord_824639) baseStart_824639 baseEnd_824639 := by
    simpa [prefixWord, tailWord_824639, baseEnd_824639] using wordTrace_append hprefix tailTrace_824639
  have hstable : (prefixWord ++ tailWord_824639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824639).length < 2 ^ (prefixWord ++ tailWord_824639).sum := by decide
  have hdescent : baseEnd_824639 < baseStart_824639 := by decide
  rcases family_descends (prefixWord ++ tailWord_824639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824652 : List Nat := [2, 2, 1, 3, 2, 4, 2, 6]
def baseStart_824652 : Nat := 118140960795 + 824652 * 2 ^ 59
def prefixEnd_824652 : Nat := 4983230072969 + 3 ^ 40 * 824652 * 2
def baseEnd_824652 : Nat := 31366136940119465107963

theorem tailTrace_824652 : CollatzResearch.WordTrace tailWord_824652 prefixEnd_824652 31366136940119465107963 := by
  unfold tailWord_824652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15038764704217059096958105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20051686272289412129277473 15038764704217059096958105)
  ·
    refine ⟨11279073528162794322718579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15038764704217059096958105 11279073528162794322718579)
    ·
      refine ⟨16918610292244191484077869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11279073528162794322718579 16918610292244191484077869)
      ·
        refine ⟨6344478859591571806529201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16918610292244191484077869 6344478859591571806529201)
        ·
          refine ⟨4758359144693678854896901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6344478859591571806529201 4758359144693678854896901)
          ·
            refine ⟨892192339630064785293169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4758359144693678854896901 892192339630064785293169)
            ·
              refine ⟨669144254722548588969877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892192339630064785293169 669144254722548588969877)
              ·
                refine ⟨31366136940119465107963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 669144254722548588969877 31366136940119465107963)
                ·
                  rfl

theorem cell22_824652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 6].length) (baseStart_824652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824652 prefixEnd_824652 := by exact prefixLift 824652
  have htrace : WordTrace (prefixWord ++ tailWord_824652) baseStart_824652 baseEnd_824652 := by
    simpa [prefixWord, tailWord_824652, baseEnd_824652] using wordTrace_append hprefix tailTrace_824652
  have hstable : (prefixWord ++ tailWord_824652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824652).length < 2 ^ (prefixWord ++ tailWord_824652).sum := by decide
  have hdescent : baseEnd_824652 < baseStart_824652 := by decide
  rcases family_descends (prefixWord ++ tailWord_824652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824684 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 3, 3]
def baseStart_824684 : Nat := 118140960795 + 824684 * 2 ^ 59
def prefixEnd_824684 : Nat := 4983230072969 + 3 ^ 40 * 824684 * 2
def baseEnd_824684 : Nat := 282306186715037769171569

theorem tailTrace_824684 : CollatzResearch.WordTrace tailWord_824684 prefixEnd_824684 282306186715037769171569 := by
  unfold tailWord_824684
  simp only [CollatzResearch.WordTrace]
  refine ⟨15039348272159093829540553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20052464362878791772720737 15039348272159093829540553)
  ·
    refine ⟨11279511204119320372155415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15039348272159093829540553 11279511204119320372155415)
    ·
      refine ⟨16919266806178980558233123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11279511204119320372155415 16919266806178980558233123)
      ·
        refine ⟨25378900209268470837349685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16919266806178980558233123 25378900209268470837349685)
        ·
          refine ⟨2379271894618919141001533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25378900209268470837349685 2379271894618919141001533)
          ·
            refine ⟨892226960482094677875575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2379271894618919141001533 892226960482094677875575)
            ·
              refine ⟨1338340440723142016813363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892226960482094677875575 1338340440723142016813363)
              ·
                refine ⟨2007510661084713025220045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338340440723142016813363 2007510661084713025220045)
                ·
                  refine ⟨752816497906767384457517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2007510661084713025220045 752816497906767384457517)
                  ·
                    refine ⟨282306186715037769171569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 752816497906767384457517 282306186715037769171569)
                    ·
                      rfl

theorem cell22_824684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_824684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824684 prefixEnd_824684 := by exact prefixLift 824684
  have htrace : WordTrace (prefixWord ++ tailWord_824684) baseStart_824684 baseEnd_824684 := by
    simpa [prefixWord, tailWord_824684, baseEnd_824684] using wordTrace_append hprefix tailTrace_824684
  have hstable : (prefixWord ++ tailWord_824684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824684).length < 2 ^ (prefixWord ++ tailWord_824684).sum := by decide
  have hdescent : baseEnd_824684 < baseStart_824684 := by decide
  rcases family_descends (prefixWord ++ tailWord_824684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824697 : List Nat := [1, 2, 1, 3, 2, 1, 6, 1, 5]
def baseStart_824697 : Nat := 118140960795 + 824697 * 2 ^ 59
def prefixEnd_824697 : Nat := 4983230072969 + 3 ^ 40 * 824697 * 2
def baseEnd_824697 : Nat := 94103545626903356198843

theorem tailTrace_824697 : CollatzResearch.WordTrace tailWord_824697 prefixEnd_824697 94103545626903356198843 := by
  unfold tailWord_824697
  simp only [CollatzResearch.WordTrace]
  refine ⟨30079170693271090879304345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20052780462180727252869563 30079170693271090879304345)
  ·
    refine ⟨22559378019953318159478259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30079170693271090879304345 22559378019953318159478259)
    ·
      refine ⟨33839067029929977239217389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22559378019953318159478259 33839067029929977239217389)
      ·
        refine ⟨12689650136223741464706521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33839067029929977239217389 12689650136223741464706521)
        ·
          refine ⟨9517237602167806098529891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12689650136223741464706521 9517237602167806098529891)
          ·
            refine ⟨14275856403251709147794837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9517237602167806098529891 14275856403251709147794837)
            ·
              refine ⟨669180768902423866302883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14275856403251709147794837 669180768902423866302883)
              ·
                refine ⟨1003771153353635799454325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669180768902423866302883 1003771153353635799454325)
                ·
                  refine ⟨94103545626903356198843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1003771153353635799454325 94103545626903356198843)
                  ·
                    rfl

theorem cell22_824697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 5].length) (baseStart_824697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824697 prefixEnd_824697 := by exact prefixLift 824697
  have htrace : WordTrace (prefixWord ++ tailWord_824697) baseStart_824697 baseEnd_824697 := by
    simpa [prefixWord, tailWord_824697, baseEnd_824697] using wordTrace_append hprefix tailTrace_824697
  have hstable : (prefixWord ++ tailWord_824697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824697).length < 2 ^ (prefixWord ++ tailWord_824697).sum := by decide
  have hdescent : baseEnd_824697 < baseStart_824697 := by decide
  rcases family_descends (prefixWord ++ tailWord_824697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824740 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_824740 : Nat := 118140960795 + 824740 * 2 ^ 59
def prefixEnd_824740 : Nat := 4983230072969 + 3 ^ 40 * 824740 * 2
def baseEnd_824740 : Nat := 282325356659472289771397

theorem tailTrace_824740 : CollatzResearch.WordTrace tailWord_824740 prefixEnd_824740 282325356659472289771397 := by
  unfold tailWord_824740
  simp only [CollatzResearch.WordTrace]
  refine ⟨15040369516057654611559837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20053826021410206148746449 15040369516057654611559837)
  ·
    refine ⟨5640138568521620479334939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15040369516057654611559837 5640138568521620479334939)
    ·
      refine ⟨8460207852782430719002409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5640138568521620479334939 8460207852782430719002409)
      ·
        refine ⟨6345155889586823039251807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8460207852782430719002409 6345155889586823039251807)
        ·
          refine ⟨9517733834380234558877711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6345155889586823039251807 9517733834380234558877711)
          ·
            refine ⟨14276600751570351838316567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9517733834380234558877711 14276600751570351838316567)
            ·
              refine ⟨21414901127355527757474851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14276600751570351838316567 21414901127355527757474851)
              ·
                refine ⟨32122351691033291636212277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21414901127355527757474851 32122351691033291636212277)
                ·
                  refine ⟨3011470471034371090894901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32122351691033291636212277 3011470471034371090894901)
                  ·
                    refine ⟨282325356659472289771397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3011470471034371090894901 282325356659472289771397)
                    ·
                      rfl

theorem cell22_824740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_824740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824740 prefixEnd_824740 := by exact prefixLift 824740
  have htrace : WordTrace (prefixWord ++ tailWord_824740) baseStart_824740 baseEnd_824740 := by
    simpa [prefixWord, tailWord_824740, baseEnd_824740] using wordTrace_append hprefix tailTrace_824740
  have hstable : (prefixWord ++ tailWord_824740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824740).length < 2 ^ (prefixWord ++ tailWord_824740).sum := by decide
  have hdescent : baseEnd_824740 < baseStart_824740 := by decide
  rcases family_descends (prefixWord ++ tailWord_824740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824755 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 4, 4]
def baseStart_824755 : Nat := 118140960795 + 824755 * 2 ^ 59
def prefixEnd_824755 : Nat := 4983230072969 + 3 ^ 40 * 824755 * 2
def baseEnd_824755 : Nat := 282330491466017250646351

theorem tailTrace_824755 : CollatzResearch.WordTrace tailWord_824755 prefixEnd_824755 282330491466017250646351 := by
  unfold tailWord_824755
  simp only [CollatzResearch.WordTrace]
  refine ⟨30081286127060966784915719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20054190751373977856610479 30081286127060966784915719)
  ·
    refine ⟨45121929190591450177373579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30081286127060966784915719 45121929190591450177373579)
    ·
      refine ⟨67682893785887175266060369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45121929190591450177373579 67682893785887175266060369)
      ·
        refine ⟨50762170339415381449545277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67682893785887175266060369 50762170339415381449545277)
        ·
          refine ⟨19035813877280768043579479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50762170339415381449545277 19035813877280768043579479)
          ·
            refine ⟨28553720815921152065369219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19035813877280768043579479 28553720815921152065369219)
            ·
              refine ⟨42830581223881728098053829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28553720815921152065369219 42830581223881728098053829)
              ·
                refine ⟨8030733979477824018385093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42830581223881728098053829 8030733979477824018385093)
                ·
                  refine ⟨1505762621152092003447205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8030733979477824018385093 1505762621152092003447205)
                  ·
                    refine ⟨282330491466017250646351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1505762621152092003447205 282330491466017250646351)
                    ·
                      rfl

theorem cell22_824755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 4].length) (baseStart_824755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824755 prefixEnd_824755 := by exact prefixLift 824755
  have htrace : WordTrace (prefixWord ++ tailWord_824755) baseStart_824755 baseEnd_824755 := by
    simpa [prefixWord, tailWord_824755, baseEnd_824755] using wordTrace_append hprefix tailTrace_824755
  have hstable : (prefixWord ++ tailWord_824755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824755).length < 2 ^ (prefixWord ++ tailWord_824755).sum := by decide
  have hdescent : baseEnd_824755 < baseStart_824755 := by decide
  rcases family_descends (prefixWord ++ tailWord_824755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824757 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_824757 : Nat := 118140960795 + 824757 * 2 ^ 59
def prefixEnd_824757 : Nat := 4983230072969 + 3 ^ 40 * 824757 * 2
def baseEnd_824757 : Nat := 282331176106889912096345

theorem tailTrace_824757 : CollatzResearch.WordTrace tailWord_824757 prefixEnd_824757 282331176106889912096345 := by
  unfold tailWord_824757
  simp only [CollatzResearch.WordTrace]
  refine ⟨30081359073053721126488525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20054239382035814084325683 30081359073053721126488525)
  ·
    refine ⟨11280509652395145422433197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30081359073053721126488525 11280509652395145422433197)
    ·
      refine ⟨4230191119648179533412449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11280509652395145422433197 4230191119648179533412449)
      ·
        refine ⟨3172643339736134650059337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4230191119648179533412449 3172643339736134650059337)
        ·
          refine ⟨2379482504802100987544503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3172643339736134650059337 2379482504802100987544503)
          ·
            refine ⟨3569223757203151481316755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2379482504802100987544503 3569223757203151481316755)
            ·
              refine ⟨5353835635804727221975133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569223757203151481316755 5353835635804727221975133)
              ·
                refine ⟨2007688363426772708240675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5353835635804727221975133 2007688363426772708240675)
                ·
                  refine ⟨3011532545140159062361013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007688363426772708240675 3011532545140159062361013)
                  ·
                    refine ⟨282331176106889912096345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3011532545140159062361013 282331176106889912096345)
                    ·
                      rfl

theorem cell22_824757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_824757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824757 prefixEnd_824757 := by exact prefixLift 824757
  have htrace : WordTrace (prefixWord ++ tailWord_824757) baseStart_824757 baseEnd_824757 := by
    simpa [prefixWord, tailWord_824757, baseEnd_824757] using wordTrace_append hprefix tailTrace_824757
  have hstable : (prefixWord ++ tailWord_824757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824757).length < 2 ^ (prefixWord ++ tailWord_824757).sum := by decide
  have hdescent : baseEnd_824757 < baseStart_824757 := by decide
  rcases family_descends (prefixWord ++ tailWord_824757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824800 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 2, 6]
def baseStart_824800 : Nat := 118140960795 + 824800 * 2 ^ 59
def prefixEnd_824800 : Nat := 4983230072969 + 3 ^ 40 * 824800 * 2
def baseEnd_824800 : Nat := 282345895885652133271213

theorem tailTrace_824800 : CollatzResearch.WordTrace tailWord_824800 prefixEnd_824800 282345895885652133271213 := by
  unfold tailWord_824800
  simp only [CollatzResearch.WordTrace]
  refine ⟨15041463705948969735151927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20055284941265292980202569 15041463705948969735151927)
  ·
    refine ⟨22562195558923454602727891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15041463705948969735151927 22562195558923454602727891)
    ·
      refine ⟨33843293338385181904091837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22562195558923454602727891 33843293338385181904091837)
      ·
        refine ⟨12691235001894443214034439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33843293338385181904091837 12691235001894443214034439)
        ·
          refine ⟨19036852502841664821051659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12691235001894443214034439 19036852502841664821051659)
          ·
            refine ⟨28555278754262497231577489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19036852502841664821051659 28555278754262497231577489)
            ·
              refine ⟨21416459065696872923683117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28555278754262497231577489 21416459065696872923683117)
              ·
                refine ⟨8031172149636327346381169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21416459065696872923683117 8031172149636327346381169)
                ·
                  refine ⟨6023379112227245509785877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8031172149636327346381169 6023379112227245509785877)
                  ·
                    refine ⟨282345895885652133271213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6023379112227245509785877 282345895885652133271213)
                    ·
                      rfl

theorem cell22_824800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_824800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824800 prefixEnd_824800 := by exact prefixLift 824800
  have htrace : WordTrace (prefixWord ++ tailWord_824800) baseStart_824800 baseEnd_824800 := by
    simpa [prefixWord, tailWord_824800, baseEnd_824800] using wordTrace_append hprefix tailTrace_824800
  have hstable : (prefixWord ++ tailWord_824800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824800).length < 2 ^ (prefixWord ++ tailWord_824800).sum := by decide
  have hdescent : baseEnd_824800 < baseStart_824800 := by decide
  rcases family_descends (prefixWord ++ tailWord_824800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824821 : List Nat := [1, 3, 5, 1, 1, 3, 2, 6]
def baseStart_824821 : Nat := 118140960795 + 824821 * 2 ^ 59
def prefixEnd_824821 : Nat := 4983230072969 + 3 ^ 40 * 824821 * 2
def baseEnd_824821 : Nat := 31372564957201675388461

theorem tailTrace_824821 : CollatzResearch.WordTrace tailWord_824821 prefixEnd_824821 31372564957201675388461 := by
  unfold tailWord_824821
  simp only [CollatzResearch.WordTrace]
  refine ⟨30083693344821860056818317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20055795563214573371212211 30083693344821860056818317)
  ·
    refine ⟨11281385004308197521306869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30083693344821860056818317 11281385004308197521306869)
    ·
      refine ⟨1057629844153893517622519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11281385004308197521306869 1057629844153893517622519)
      ·
        refine ⟨1586444766230840276433779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057629844153893517622519 1586444766230840276433779)
        ·
          refine ⟨2379667149346260414650669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586444766230840276433779 2379667149346260414650669)
          ·
            refine ⟨892375181004847655494001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2379667149346260414650669 892375181004847655494001)
            ·
              refine ⟨669281385753635741620501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892375181004847655494001 669281385753635741620501)
              ·
                refine ⟨31372564957201675388461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 669281385753635741620501 31372564957201675388461)
                ·
                  rfl

theorem cell22_824821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 6].length) (baseStart_824821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824821 prefixEnd_824821 := by exact prefixLift 824821
  have htrace : WordTrace (prefixWord ++ tailWord_824821) baseStart_824821 baseEnd_824821 := by
    simpa [prefixWord, tailWord_824821, baseEnd_824821] using wordTrace_append hprefix tailTrace_824821
  have hstable : (prefixWord ++ tailWord_824821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824821).length < 2 ^ (prefixWord ++ tailWord_824821).sum := by decide
  have hdescent : baseEnd_824821 < baseStart_824821 := by decide
  rcases family_descends (prefixWord ++ tailWord_824821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824838 : List Nat := [6, 2, 1, 1, 2, 2, 8]
def baseStart_824838 : Nat := 118140960795 + 824838 * 2 ^ 59
def prefixEnd_824838 : Nat := 4983230072969 + 3 ^ 40 * 824838 * 2
def baseEnd_824838 : Nat := 10457737187490100030411

theorem tailTrace_824838 : CollatzResearch.WordTrace tailWord_824838 prefixEnd_824838 10457737187490100030411 := by
  unfold tailWord_824838
  simp only [CollatzResearch.WordTrace]
  refine ⟨940134793305008498755849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20056208923840181306791445 940134793305008498755849)
  ·
    refine ⟨705101094978756374066887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 940134793305008498755849 705101094978756374066887)
    ·
      refine ⟨1057651642468134561100331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 705101094978756374066887 1057651642468134561100331)
      ·
        refine ⟨1586477463702201841650497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057651642468134561100331 1586477463702201841650497)
        ·
          refine ⟨1189858097776651381237873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1586477463702201841650497 1189858097776651381237873)
          ·
            refine ⟨892393573332488535928405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189858097776651381237873 892393573332488535928405)
            ·
              refine ⟨10457737187490100030411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 892393573332488535928405 10457737187490100030411)
              ·
                rfl

theorem cell22_824838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 8].length) (baseStart_824838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824838 prefixEnd_824838 := by exact prefixLift 824838
  have htrace : WordTrace (prefixWord ++ tailWord_824838) baseStart_824838 baseEnd_824838 := by
    simpa [prefixWord, tailWord_824838, baseEnd_824838] using wordTrace_append hprefix tailTrace_824838
  have hstable : (prefixWord ++ tailWord_824838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824838).length < 2 ^ (prefixWord ++ tailWord_824838).sum := by decide
  have hdescent : baseEnd_824838 < baseStart_824838 := by decide
  rcases family_descends (prefixWord ++ tailWord_824838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824853 : List Nat := [1, 3, 2, 1, 3, 3, 3, 2, 1, 3]
def baseStart_824853 : Nat := 118140960795 + 824853 * 2 ^ 59
def prefixEnd_824853 : Nat := 4983230072969 + 3 ^ 40 * 824853 * 2
def baseEnd_824853 : Nat := 282364038868777661696051

theorem tailTrace_824853 : CollatzResearch.WordTrace tailWord_824853 prefixEnd_824853 282364038868777661696051 := by
  unfold tailWord_824853
  simp only [CollatzResearch.WordTrace]
  refine ⟨30084860480705929521983213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20056573653803953014655475 30084860480705929521983213)
  ·
    refine ⟨11281822680264723570743705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30084860480705929521983213 11281822680264723570743705)
    ·
      refine ⟨8461367010198542678057779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11281822680264723570743705 8461367010198542678057779)
      ·
        refine ⟨12692050515297814017086669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8461367010198542678057779 12692050515297814017086669)
        ·
          refine ⟨4759518943236680256407501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12692050515297814017086669 4759518943236680256407501)
          ·
            refine ⟨1784819603713755096152813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4759518943236680256407501 1784819603713755096152813)
            ·
              refine ⟨669307351392658161057305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1784819603713755096152813 669307351392658161057305)
              ·
                refine ⟨501980513544493620792979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669307351392658161057305 501980513544493620792979)
                ·
                  refine ⟨752970770316740431189469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501980513544493620792979 752970770316740431189469)
                  ·
                    refine ⟨282364038868777661696051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 752970770316740431189469 282364038868777661696051)
                    ·
                      rfl

theorem cell22_824853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_824853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824853 prefixEnd_824853 := by exact prefixLift 824853
  have htrace : WordTrace (prefixWord ++ tailWord_824853) baseStart_824853 baseEnd_824853 := by
    simpa [prefixWord, tailWord_824853, baseEnd_824853] using wordTrace_append hprefix tailTrace_824853
  have hstable : (prefixWord ++ tailWord_824853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824853).length < 2 ^ (prefixWord ++ tailWord_824853).sum := by decide
  have hdescent : baseEnd_824853 < baseStart_824853 := by decide
  rcases family_descends (prefixWord ++ tailWord_824853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824971 : List Nat := [1, 1, 1, 1, 4, 1, 3, 6, 1, 3]
def baseStart_824971 : Nat := 118140960795 + 824971 * 2 ^ 59
def prefixEnd_824971 : Nat := 4983230072969 + 3 ^ 40 * 824971 * 2
def baseEnd_824971 : Nat := 282404432680264687245689

theorem tailTrace_824971 : CollatzResearch.WordTrace tailWord_824971 prefixEnd_824971 282404432680264687245689 := by
  unfold tailWord_824971
  simp only [CollatzResearch.WordTrace]
  refine ⟨30089164294278435674778767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20059442862852290449852511 30089164294278435674778767)
  ·
    refine ⟨45133746441417653512168151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30089164294278435674778767 45133746441417653512168151)
    ·
      refine ⟨67700619662126480268252227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45133746441417653512168151 67700619662126480268252227)
      ·
        refine ⟨101550929493189720402378341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67700619662126480268252227 101550929493189720402378341)
        ·
          refine ⟨19040799279973072575445939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101550929493189720402378341 19040799279973072575445939)
          ·
            refine ⟨28561198919959608863168909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19040799279973072575445939 28561198919959608863168909)
            ·
              refine ⟨10710449594984853323688341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28561198919959608863168909 10710449594984853323688341)
              ·
                refine ⟨502052324764914999547891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10710449594984853323688341 502052324764914999547891)
                ·
                  refine ⟨753078487147372499321837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502052324764914999547891 753078487147372499321837)
                  ·
                    refine ⟨282404432680264687245689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 753078487147372499321837 282404432680264687245689)
                    ·
                      rfl

theorem cell22_824971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 1, 3].length) (baseStart_824971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_824971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_824971 prefixEnd_824971 := by exact prefixLift 824971
  have htrace : WordTrace (prefixWord ++ tailWord_824971) baseStart_824971 baseEnd_824971 := by
    simpa [prefixWord, tailWord_824971, baseEnd_824971] using wordTrace_append hprefix tailTrace_824971
  have hstable : (prefixWord ++ tailWord_824971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824971).length < 2 ^ (prefixWord ++ tailWord_824971).sum := by decide
  have hdescent : baseEnd_824971 < baseStart_824971 := by decide
  rcases family_descends (prefixWord ++ tailWord_824971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825078 : List Nat := [5, 1, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_825078 : Nat := 118140960795 + 825078 * 2 ^ 59
def prefixEnd_825078 : Nat := 4983230072969 + 3 ^ 40 * 825078 * 2
def baseEnd_825078 : Nat := 282441060966952074820361

theorem tailTrace_825078 : CollatzResearch.WordTrace tailWord_825078 prefixEnd_825078 282441060966952074820361 := by
  unfold tailWord_825078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1880816681555674559307743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20062044603260528632615925 1880816681555674559307743)
  ·
    refine ⟨2821225022333511838961615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1880816681555674559307743 2821225022333511838961615)
    ·
      refine ⟨4231837533500267758442423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2821225022333511838961615 4231837533500267758442423)
      ·
        refine ⟨6347756300250401637663635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4231837533500267758442423 6347756300250401637663635)
        ·
          refine ⟨9521634450375602456495453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6347756300250401637663635 9521634450375602456495453)
          ·
            refine ⟨3570612918890850921185795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9521634450375602456495453 3570612918890850921185795)
            ·
              refine ⟨5355919378336276381778693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3570612918890850921185795 5355919378336276381778693)
              ·
                refine ⟨1004234883438051821583505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5355919378336276381778693 1004234883438051821583505)
                ·
                  refine ⟨753176162578538866187629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1004234883438051821583505 753176162578538866187629)
                  ·
                    refine ⟨282441060966952074820361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 753176162578538866187629 282441060966952074820361)
                    ·
                      rfl

theorem cell22_825078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_825078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825078 prefixEnd_825078 := by exact prefixLift 825078
  have htrace : WordTrace (prefixWord ++ tailWord_825078) baseStart_825078 baseEnd_825078 := by
    simpa [prefixWord, tailWord_825078, baseEnd_825078] using wordTrace_append hprefix tailTrace_825078
  have hstable : (prefixWord ++ tailWord_825078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825078).length < 2 ^ (prefixWord ++ tailWord_825078).sum := by decide
  have hdescent : baseEnd_825078 < baseStart_825078 := by decide
  rcases family_descends (prefixWord ++ tailWord_825078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825119 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 7]
def baseStart_825119 : Nat := 118140960795 + 825119 * 2 ^ 59
def prefixEnd_825119 : Nat := 4983230072969 + 3 ^ 40 * 825119 * 2
def baseEnd_825119 : Nat := 94151698701613878181745

theorem tailTrace_825119 : CollatzResearch.WordTrace tailWord_825119 prefixEnd_825119 94151698701613878181745 := by
  unfold tailWord_825119
  simp only [CollatzResearch.WordTrace]
  refine ⟨30094562297742256951166411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20063041531828171300777607 30094562297742256951166411)
  ·
    refine ⟨45141843446613385426749617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30094562297742256951166411 45141843446613385426749617)
    ·
      refine ⟨33856382584960039070062213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45141843446613385426749617 33856382584960039070062213)
      ·
        refine ⟨6348071734680007325636665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33856382584960039070062213 6348071734680007325636665)
        ·
          refine ⟨4761053801010005494227499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6348071734680007325636665 4761053801010005494227499)
          ·
            refine ⟨7141580701515008241341249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4761053801010005494227499 7141580701515008241341249)
            ·
              refine ⟨5356185526136256181005937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7141580701515008241341249 5356185526136256181005937)
              ·
                refine ⟨4017139144602192135754453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5356185526136256181005937 4017139144602192135754453)
                ·
                  refine ⟨94151698701613878181745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4017139144602192135754453 94151698701613878181745)
                  ·
                    rfl

theorem cell22_825119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 7].length) (baseStart_825119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825119 prefixEnd_825119 := by exact prefixLift 825119
  have htrace : WordTrace (prefixWord ++ tailWord_825119) baseStart_825119 baseEnd_825119 := by
    simpa [prefixWord, tailWord_825119, baseEnd_825119] using wordTrace_append hprefix tailTrace_825119
  have hstable : (prefixWord ++ tailWord_825119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825119).length < 2 ^ (prefixWord ++ tailWord_825119).sum := by decide
  have hdescent : baseEnd_825119 < baseStart_825119 := by decide
  rcases family_descends (prefixWord ++ tailWord_825119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825123 : List Nat := [1, 1, 1, 4, 2, 1, 3, 5, 1, 3]
def baseStart_825123 : Nat := 118140960795 + 825123 * 2 ^ 59
def prefixEnd_825123 : Nat := 4983230072969 + 3 ^ 40 * 825123 * 2
def baseEnd_825123 : Nat := 282456465386586957445223

theorem tailTrace_825123 : CollatzResearch.WordTrace tailWord_825123 prefixEnd_825123 282456465386586957445223 := by
  unfold tailWord_825123
  simp only [CollatzResearch.WordTrace]
  refine ⟨30094708189727765634312023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20063138793151843756208015 30094708189727765634312023)
  ·
    refine ⟨45142062284591648451468035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30094708189727765634312023 45142062284591648451468035)
    ·
      refine ⟨67713093426887472677202053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45142062284591648451468035 67713093426887472677202053)
      ·
        refine ⟨12696205017541401126975385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67713093426887472677202053 12696205017541401126975385)
        ·
          refine ⟨9522153763156050845231539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12696205017541401126975385 9522153763156050845231539)
          ·
            refine ⟨14283230644734076267847309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9522153763156050845231539 14283230644734076267847309)
            ·
              refine ⟨5356211491775278600442741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14283230644734076267847309 5356211491775278600442741)
              ·
                refine ⟨502144827353932368791507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5356211491775278600442741 502144827353932368791507)
                ·
                  refine ⟨753217241030898553187261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502144827353932368791507 753217241030898553187261)
                  ·
                    refine ⟨282456465386586957445223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 753217241030898553187261 282456465386586957445223)
                    ·
                      rfl

theorem cell22_825123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 1, 3].length) (baseStart_825123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825123 prefixEnd_825123 := by exact prefixLift 825123
  have htrace : WordTrace (prefixWord ++ tailWord_825123) baseStart_825123 baseEnd_825123 := by
    simpa [prefixWord, tailWord_825123, baseEnd_825123] using wordTrace_append hprefix tailTrace_825123
  have hstable : (prefixWord ++ tailWord_825123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825123).length < 2 ^ (prefixWord ++ tailWord_825123).sum := by decide
  have hdescent : baseEnd_825123 < baseStart_825123 := by decide
  rcases family_descends (prefixWord ++ tailWord_825123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825140 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_825140 : Nat := 118140960795 + 825140 * 2 ^ 59
def prefixEnd_825140 : Nat := 4983230072969 + 3 ^ 40 * 825140 * 2
def baseEnd_825140 : Nat := 282462284834004579770171

theorem tailTrace_825140 : CollatzResearch.WordTrace tailWord_825140 prefixEnd_825140 282462284834004579770171 := by
  unfold tailWord_825140
  simp only [CollatzResearch.WordTrace]
  refine ⟨15047664115333088768840437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20063552153777451691787249 15047664115333088768840437)
  ·
    refine ⟨1410718510812477072078791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15047664115333088768840437 1410718510812477072078791)
    ·
      refine ⟨2116077766218715608118187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410718510812477072078791 2116077766218715608118187)
      ·
        refine ⟨3174116649328073412177281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116077766218715608118187 3174116649328073412177281)
        ·
          refine ⟨2380587486996055059132961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3174116649328073412177281 2380587486996055059132961)
          ·
            refine ⟨1785440615247041294349721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2380587486996055059132961 1785440615247041294349721)
            ·
              refine ⟨1339080461435280970762291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785440615247041294349721 1339080461435280970762291)
              ·
                refine ⟨2008620692152921456143437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339080461435280970762291 2008620692152921456143437)
                ·
                  refine ⟨753232759557345546053789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2008620692152921456143437 753232759557345546053789)
                  ·
                    refine ⟨282462284834004579770171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 753232759557345546053789 282462284834004579770171)
                    ·
                      rfl

theorem cell22_825140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_825140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825140 prefixEnd_825140 := by exact prefixLift 825140
  have htrace : WordTrace (prefixWord ++ tailWord_825140) baseStart_825140 baseEnd_825140 := by
    simpa [prefixWord, tailWord_825140, baseEnd_825140] using wordTrace_append hprefix tailTrace_825140
  have hstable : (prefixWord ++ tailWord_825140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825140).length < 2 ^ (prefixWord ++ tailWord_825140).sum := by decide
  have hdescent : baseEnd_825140 < baseStart_825140 := by decide
  rcases family_descends (prefixWord ++ tailWord_825140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825198 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_825198 : Nat := 118140960795 + 825198 * 2 ^ 59
def prefixEnd_825198 : Nat := 4983230072969 + 3 ^ 40 * 825198 * 2
def baseEnd_825198 : Nat := 94160713139770587273331

theorem tailTrace_825198 : CollatzResearch.WordTrace tailWord_825198 prefixEnd_825198 94160713139770587273331 := by
  unfold tailWord_825198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3762180458057006680411531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20064962442970702295528165 3762180458057006680411531)
  ·
    refine ⟨5643270687085510020617297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3762180458057006680411531 5643270687085510020617297)
    ·
      refine ⟨4232453015314132515462973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5643270687085510020617297 4232453015314132515462973)
      ·
        refine ⟨1587169880742799693298615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4232453015314132515462973 1587169880742799693298615)
        ·
          refine ⟨2380754821114199539947923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587169880742799693298615 2380754821114199539947923)
          ·
            refine ⟨3571132231671299309921885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2380754821114199539947923 3571132231671299309921885)
            ·
              refine ⟨1339174586876737241220707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3571132231671299309921885 1339174586876737241220707)
              ·
                refine ⟨2008761880315105861831061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339174586876737241220707 2008761880315105861831061)
                ·
                  refine ⟨94160713139770587273331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2008761880315105861831061 94160713139770587273331)
                  ·
                    rfl

theorem cell22_825198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_825198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825198 prefixEnd_825198 := by exact prefixLift 825198
  have htrace : WordTrace (prefixWord ++ tailWord_825198) baseStart_825198 baseEnd_825198 := by
    simpa [prefixWord, tailWord_825198, baseEnd_825198] using wordTrace_append hprefix tailTrace_825198
  have hstable : (prefixWord ++ tailWord_825198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825198).length < 2 ^ (prefixWord ++ tailWord_825198).sum := by decide
  have hdescent : baseEnd_825198 < baseStart_825198 := by decide
  rcases family_descends (prefixWord ++ tailWord_825198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825217 : List Nat := [1, 2, 4, 4, 1, 2, 1, 2, 1, 4]
def baseStart_825217 : Nat := 118140960795 + 825217 * 2 ^ 59
def prefixEnd_825217 : Nat := 4983230072969 + 3 ^ 40 * 825217 * 2
def baseEnd_825217 : Nat := 282488643507602045594935

theorem tailTrace_825217 : CollatzResearch.WordTrace tailWord_825217 prefixEnd_825217 282488643507602045594935 := by
  unfold tailWord_825217
  simp only [CollatzResearch.WordTrace]
  refine ⟨30098136651387219688233905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20065424434258146458822603 30098136651387219688233905)
  ·
    refine ⟨22573602488540414766175429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30098136651387219688233905 22573602488540414766175429)
    ·
      refine ⟨4232550466601327768657893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22573602488540414766175429 4232550466601327768657893)
      ·
        refine ⟨793603212487748956623355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4232550466601327768657893 793603212487748956623355)
        ·
          refine ⟨1190404818731623434935033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793603212487748956623355 1190404818731623434935033)
          ·
            refine ⟨892803614048717576201275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190404818731623434935033 892803614048717576201275)
            ·
              refine ⟨1339205421073076364301913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892803614048717576201275 1339205421073076364301913)
              ·
                refine ⟨1004404065804807273226435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1339205421073076364301913 1004404065804807273226435)
                ·
                  refine ⟨1506606098707210909839653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004404065804807273226435 1506606098707210909839653)
                  ·
                    refine ⟨282488643507602045594935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1506606098707210909839653 282488643507602045594935)
                    ·
                      rfl

theorem cell22_825217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_825217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825217 prefixEnd_825217 := by exact prefixLift 825217
  have htrace : WordTrace (prefixWord ++ tailWord_825217) baseStart_825217 baseEnd_825217 := by
    simpa [prefixWord, tailWord_825217, baseEnd_825217] using wordTrace_append hprefix tailTrace_825217
  have hstable : (prefixWord ++ tailWord_825217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825217).length < 2 ^ (prefixWord ++ tailWord_825217).sum := by decide
  have hdescent : baseEnd_825217 < baseStart_825217 := by decide
  rcases family_descends (prefixWord ++ tailWord_825217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825230 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_825230 : Nat := 118140960795 + 825230 * 2 ^ 59
def prefixEnd_825230 : Nat := 4983230072969 + 3 ^ 40 * 825230 * 2
def baseEnd_825230 : Nat := 282493093673274345019895

theorem tailTrace_825230 : CollatzResearch.WordTrace tailWord_825230 prefixEnd_825230 282493093673274345019895 := by
  unfold tailWord_825230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3762326350042515363557143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20065740533560081938971429 3762326350042515363557143)
  ·
    refine ⟨5643489525063773045335715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3762326350042515363557143 5643489525063773045335715)
    ·
      refine ⟨8465234287595659568003573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5643489525063773045335715 8465234287595659568003573)
      ·
        refine ⟨793615714462093084500335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8465234287595659568003573 793615714462093084500335)
        ·
          refine ⟨1190423571693139626750503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793615714462093084500335 1190423571693139626750503)
          ·
            refine ⟨1785635357539709440125755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190423571693139626750503 1785635357539709440125755)
            ·
              refine ⟨2678453036309564160188633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1785635357539709440125755 2678453036309564160188633)
              ·
                refine ⟨2008839777232173120141475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2678453036309564160188633 2008839777232173120141475)
                ·
                  refine ⟨3013259665848259680212213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008839777232173120141475 3013259665848259680212213)
                  ·
                    refine ⟨282493093673274345019895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3013259665848259680212213 282493093673274345019895)
                    ·
                      rfl

theorem cell22_825230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_825230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825230 prefixEnd_825230 := by exact prefixLift 825230
  have htrace : WordTrace (prefixWord ++ tailWord_825230) baseStart_825230 baseEnd_825230 := by
    simpa [prefixWord, tailWord_825230, baseEnd_825230] using wordTrace_append hprefix tailTrace_825230
  have hstable : (prefixWord ++ tailWord_825230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825230).length < 2 ^ (prefixWord ++ tailWord_825230).sum := by decide
  have hdescent : baseEnd_825230 < baseStart_825230 := by decide
  rcases family_descends (prefixWord ++ tailWord_825230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825249 : List Nat := [1, 2, 3, 4, 3, 1, 2, 2, 4]
def baseStart_825249 : Nat := 118140960795 + 825249 * 2 ^ 59
def prefixEnd_825249 : Nat := 4983230072969 + 3 ^ 40 * 825249 * 2
def baseEnd_825249 : Nat := 94166532587188209598279

theorem tailTrace_825249 : CollatzResearch.WordTrace tailWord_825249 prefixEnd_825249 94166532587188209598279 := by
  unfold tailWord_825249
  simp only [CollatzResearch.WordTrace]
  refine ⟨30099303787271289153398801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20066202524847526102265867 30099303787271289153398801)
  ·
    refine ⟨22574477840453466865049101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30099303787271289153398801 22574477840453466865049101)
    ·
      refine ⟨8465429190170050074393413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22574477840453466865049101 8465429190170050074393413)
      ·
        refine ⟨1587267973156884388948765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8465429190170050074393413 1587267973156884388948765)
        ·
          refine ⟨595225489933831645855787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1587267973156884388948765 595225489933831645855787)
          ·
            refine ⟨892838234900747468783681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595225489933831645855787 892838234900747468783681)
            ·
              refine ⟨669628676175560601587761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892838234900747468783681 669628676175560601587761)
              ·
                refine ⟨502221507131670451190821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669628676175560601587761 502221507131670451190821)
                ·
                  refine ⟨94166532587188209598279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502221507131670451190821 94166532587188209598279)
                  ·
                    rfl

theorem cell22_825249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 4].length) (baseStart_825249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825249 prefixEnd_825249 := by exact prefixLift 825249
  have htrace : WordTrace (prefixWord ++ tailWord_825249) baseStart_825249 baseEnd_825249 := by
    simpa [prefixWord, tailWord_825249, baseEnd_825249] using wordTrace_append hprefix tailTrace_825249
  have hstable : (prefixWord ++ tailWord_825249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825249).length < 2 ^ (prefixWord ++ tailWord_825249).sum := by decide
  have hdescent : baseEnd_825249 < baseStart_825249 := by decide
  rcases family_descends (prefixWord ++ tailWord_825249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825292 : List Nat := [2, 2, 1, 4, 1, 3, 2, 3, 1, 3]
def baseStart_825292 : Nat := 118140960795 + 825292 * 2 ^ 59
def prefixEnd_825292 : Nat := 4983230072969 + 3 ^ 40 * 825292 * 2
def baseEnd_825292 : Nat := 282514317540326849969705

theorem tailTrace_825292 : CollatzResearch.WordTrace tailWord_825292 prefixEnd_825292 282514317540326849969705 := by
  unfold tailWord_825292
  simp only [CollatzResearch.WordTrace]
  refine ⟨15050436063057753748607065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20067248084077004998142753 15050436063057753748607065)
  ·
    refine ⟨11287827047293315311455299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15050436063057753748607065 11287827047293315311455299)
    ·
      refine ⟨16931740570939972967182949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11287827047293315311455299 16931740570939972967182949)
      ·
        refine ⟨3174701357051244931346803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16931740570939972967182949 3174701357051244931346803)
        ·
          refine ⟨4762052035576867397020205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3174701357051244931346803 4762052035576867397020205)
          ·
            refine ⟨1785769513341325273882577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4762052035576867397020205 1785769513341325273882577)
            ·
              refine ⟨1339327135005993955411933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785769513341325273882577 1339327135005993955411933)
              ·
                refine ⟨502247675627247733279475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1339327135005993955411933 502247675627247733279475)
                ·
                  refine ⟨753371513440871599919213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502247675627247733279475 753371513440871599919213)
                  ·
                    refine ⟨282514317540326849969705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 753371513440871599919213 282514317540326849969705)
                    ·
                      rfl

theorem cell22_825292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_825292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825292 prefixEnd_825292 := by exact prefixLift 825292
  have htrace : WordTrace (prefixWord ++ tailWord_825292) baseStart_825292 baseEnd_825292 := by
    simpa [prefixWord, tailWord_825292, baseEnd_825292] using wordTrace_append hprefix tailTrace_825292
  have hstable : (prefixWord ++ tailWord_825292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825292).length < 2 ^ (prefixWord ++ tailWord_825292).sum := by decide
  have hdescent : baseEnd_825292 < baseStart_825292 := by decide
  rcases family_descends (prefixWord ++ tailWord_825292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825305 : List Nat := [1, 2, 1, 2, 6, 2, 1, 2, 5]
def baseStart_825305 : Nat := 118140960795 + 825305 * 2 ^ 59
def prefixEnd_825305 : Nat := 4983230072969 + 3 ^ 40 * 825305 * 2
def baseEnd_825305 : Nat := 94172922568666383131555

theorem tailTrace_825305 : CollatzResearch.WordTrace tailWord_825305 prefixEnd_825305 94172922568666383131555 := by
  unfold tailWord_825305
  simp only [CollatzResearch.WordTrace]
  refine ⟨30101346275068410717437369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20067564183378940478291579 30101346275068410717437369)
  ·
    refine ⟨22576009706301308038078027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30101346275068410717437369 22576009706301308038078027)
    ·
      refine ⟨33864014559451962057117041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22576009706301308038078027 33864014559451962057117041)
      ·
        refine ⟨25398010919588971542837781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33864014559451962057117041 25398010919588971542837781)
        ·
          refine ⟨1190531761855733041070521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25398010919588971542837781 1190531761855733041070521)
          ·
            refine ⟨892898821391799780802891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190531761855733041070521 892898821391799780802891)
            ·
              refine ⟨1339348232087699671204337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892898821391799780802891 1339348232087699671204337)
              ·
                refine ⟨1004511174065774753403253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1339348232087699671204337 1004511174065774753403253)
                ·
                  refine ⟨94172922568666383131555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1004511174065774753403253 94172922568666383131555)
                  ·
                    rfl

theorem cell22_825305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 5].length) (baseStart_825305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825305 prefixEnd_825305 := by exact prefixLift 825305
  have htrace : WordTrace (prefixWord ++ tailWord_825305) baseStart_825305 baseEnd_825305 := by
    simpa [prefixWord, tailWord_825305, baseEnd_825305] using wordTrace_append hprefix tailTrace_825305
  have hstable : (prefixWord ++ tailWord_825305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825305).length < 2 ^ (prefixWord ++ tailWord_825305).sum := by decide
  have hdescent : baseEnd_825305 < baseStart_825305 := by decide
  rcases family_descends (prefixWord ++ tailWord_825305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825367 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 6]
def baseStart_825367 : Nat := 118140960795 + 825367 * 2 ^ 59
def prefixEnd_825367 : Nat := 4983230072969 + 3 ^ 40 * 825367 * 2
def baseEnd_825367 : Nat := 94179997191017218114825

theorem tailTrace_825367 : CollatzResearch.WordTrace tailWord_825367 prefixEnd_825367 94179997191017218114825 := by
  unfold tailWord_825367
  simp only [CollatzResearch.WordTrace]
  refine ⟨30103607600843795306194355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20069071733895863537462903 30103607600843795306194355)
  ·
    refine ⟨45155411401265692959291533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30103607600843795306194355 45155411401265692959291533)
    ·
      refine ⟨16933279275474634859734325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45155411401265692959291533 16933279275474634859734325)
      ·
        refine ⟨1587494932075747018100093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16933279275474634859734325 1587494932075747018100093)
        ·
          refine ⟨595310599528405131787535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1587494932075747018100093 595310599528405131787535)
          ·
            refine ⟨892965899292607697681303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595310599528405131787535 892965899292607697681303)
            ·
              refine ⟨1339448848938911546521955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892965899292607697681303 1339448848938911546521955)
              ·
                refine ⟨2009173273408367319782933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339448848938911546521955 2009173273408367319782933)
                ·
                  refine ⟨94179997191017218114825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2009173273408367319782933 94179997191017218114825)
                  ·
                    rfl

theorem cell22_825367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 6].length) (baseStart_825367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825367 prefixEnd_825367 := by exact prefixLift 825367
  have htrace : WordTrace (prefixWord ++ tailWord_825367) baseStart_825367 baseEnd_825367 := by
    simpa [prefixWord, tailWord_825367, baseEnd_825367] using wordTrace_append hprefix tailTrace_825367
  have hstable : (prefixWord ++ tailWord_825367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825367).length < 2 ^ (prefixWord ++ tailWord_825367).sum := by decide
  have hdescent : baseEnd_825367 < baseStart_825367 := by decide
  rcases family_descends (prefixWord ++ tailWord_825367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825378 : List Nat := [3, 3, 1, 1, 1, 2, 4, 7]
def baseStart_825378 : Nat := 118140960795 + 825378 * 2 ^ 59
def prefixEnd_825378 : Nat := 4983230072969 + 3 ^ 40 * 825378 * 2
def baseEnd_825378 : Nat := 31393750788650143591049

theorem tailTrace_825378 : CollatzResearch.WordTrace tailWord_825378 prefixEnd_825378 31393750788650143591049 := by
  unfold tailWord_825378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7526002200950986046211197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20069339202535962789896525 7526002200950986046211197)
  ·
    refine ⟨2822250825356619767329199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7526002200950986046211197 2822250825356619767329199)
    ·
      refine ⟨4233376238034929650993799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2822250825356619767329199 4233376238034929650993799)
      ·
        refine ⟨6350064357052394476490699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4233376238034929650993799 6350064357052394476490699)
        ·
          refine ⟨9525096535578591714736049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6350064357052394476490699 9525096535578591714736049)
          ·
            refine ⟨7143822401683943786052037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9525096535578591714736049 7143822401683943786052037)
            ·
              refine ⟨1339466700315739459884757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7143822401683943786052037 1339466700315739459884757)
              ·
                refine ⟨31393750788650143591049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1339466700315739459884757 31393750788650143591049)
                ·
                  rfl

theorem cell22_825378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_825378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825378 prefixEnd_825378 := by exact prefixLift 825378
  have htrace : WordTrace (prefixWord ++ tailWord_825378) baseStart_825378 baseEnd_825378 := by
    simpa [prefixWord, tailWord_825378, baseEnd_825378] using wordTrace_append hprefix tailTrace_825378
  have hstable : (prefixWord ++ tailWord_825378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825378).length < 2 ^ (prefixWord ++ tailWord_825378).sum := by decide
  have hdescent : baseEnd_825378 < baseStart_825378 := by decide
  rcases family_descends (prefixWord ++ tailWord_825378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825391 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 4, 6]
def baseStart_825391 : Nat := 118140960795 + 825391 * 2 ^ 59
def prefixEnd_825391 : Nat := 4983230072969 + 3 ^ 40 * 825391 * 2
def baseEnd_825391 : Nat := 282548207263523591744401

theorem tailTrace_825391 : CollatzResearch.WordTrace tailWord_825391 prefixEnd_825391 282548207263523591744401 := by
  unfold tailWord_825391
  simp only [CollatzResearch.WordTrace]
  refine ⟨30104482952756847405068027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20069655301837898270045351 30104482952756847405068027)
  ·
    refine ⟨45156724429135271107602041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30104482952756847405068027 45156724429135271107602041)
    ·
      refine ⟨33867543321851453330701531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45156724429135271107602041 33867543321851453330701531)
      ·
        refine ⟨50801314982777179996052297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33867543321851453330701531 50801314982777179996052297)
        ·
          refine ⟨38100986237082884997039223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50801314982777179996052297 38100986237082884997039223)
          ·
            refine ⟨57151479355624327495558835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38100986237082884997039223 57151479355624327495558835)
            ·
              refine ⟨85727219033436491243338253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57151479355624327495558835 85727219033436491243338253)
              ·
                refine ⟨32147707137538684216251845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85727219033436491243338253 32147707137538684216251845)
                ·
                  refine ⟨6027695088288503290547221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32147707137538684216251845 6027695088288503290547221)
                  ·
                    refine ⟨282548207263523591744401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6027695088288503290547221 282548207263523591744401)
                    ·
                      rfl

theorem cell22_825391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_825391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825391 prefixEnd_825391 := by exact prefixLift 825391
  have htrace : WordTrace (prefixWord ++ tailWord_825391) baseStart_825391 baseEnd_825391 := by
    simpa [prefixWord, tailWord_825391, baseEnd_825391] using wordTrace_append hprefix tailTrace_825391
  have hstable : (prefixWord ++ tailWord_825391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825391).length < 2 ^ (prefixWord ++ tailWord_825391).sum := by decide
  have hdescent : baseEnd_825391 < baseStart_825391 := by decide
  rcases family_descends (prefixWord ++ tailWord_825391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825517 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_825517 : Nat := 118140960795 + 825517 * 2 ^ 59
def prefixEnd_825517 : Nat := 4983230072969 + 3 ^ 40 * 825517 * 2
def baseEnd_825517 : Nat := 282591339638501263094015

theorem tailTrace_825517 : CollatzResearch.WordTrace tailWord_825517 prefixEnd_825517 282591339638501263094015 := by
  unfold tailWord_825517
  simp only [CollatzResearch.WordTrace]
  refine ⟨30109078550300370924154805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20072719033533580616103203 30109078550300370924154805)
  ·
    refine ⟨2822726114090659774139513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30109078550300370924154805 2822726114090659774139513)
    ·
      refine ⟨2117044585567994830604635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2822726114090659774139513 2117044585567994830604635)
      ·
        refine ⟨3175566878351992245906953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2117044585567994830604635 3175566878351992245906953)
        ·
          refine ⟨2381675158763994184430215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3175566878351992245906953 2381675158763994184430215)
          ·
            refine ⟨3572512738145991276645323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381675158763994184430215 3572512738145991276645323)
            ·
              refine ⟨5358769107218986914967985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3572512738145991276645323 5358769107218986914967985)
              ·
                refine ⟨4019076830414240186225989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5358769107218986914967985 4019076830414240186225989)
                ·
                  refine ⟨753576905702670034917373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4019076830414240186225989 753576905702670034917373)
                  ·
                    refine ⟨282591339638501263094015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 753576905702670034917373 282591339638501263094015)
                    ·
                      rfl

theorem cell22_825517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_825517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825517 prefixEnd_825517 := by exact prefixLift 825517
  have htrace : WordTrace (prefixWord ++ tailWord_825517) baseStart_825517 baseEnd_825517 := by
    simpa [prefixWord, tailWord_825517, baseEnd_825517] using wordTrace_append hprefix tailTrace_825517
  have hstable : (prefixWord ++ tailWord_825517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825517).length < 2 ^ (prefixWord ++ tailWord_825517).sum := by decide
  have hdescent : baseEnd_825517 < baseStart_825517 := by decide
  rcases family_descends (prefixWord ++ tailWord_825517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825532 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_825532 : Nat := 118140960795 + 825532 * 2 ^ 59
def prefixEnd_825532 : Nat := 4983230072969 + 3 ^ 40 * 825532 * 2
def baseEnd_825532 : Nat := 282596474445046223968969

theorem tailTrace_825532 : CollatzResearch.WordTrace tailWord_825532 prefixEnd_825532 282596474445046223968969 := by
  unfold tailWord_825532
  simp only [CollatzResearch.WordTrace]
  refine ⟨15054812822623014242975425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20073083763497352323967233 15054812822623014242975425)
  ·
    refine ⟨11291109616967260682231569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15054812822623014242975425 11291109616967260682231569)
    ·
      refine ⟨8468332212725445511673677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11291109616967260682231569 8468332212725445511673677)
      ·
        refine ⟨3175624579772042066877629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8468332212725445511673677 3175624579772042066877629)
        ·
          refine ⟨1190859217414515775079111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3175624579772042066877629 1190859217414515775079111)
          ·
            refine ⟨1786288826121773662618667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190859217414515775079111 1786288826121773662618667)
            ·
              refine ⟨2679433239182660493928001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1786288826121773662618667 2679433239182660493928001)
              ·
                refine ⟨2009574929386995370446001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2679433239182660493928001 2009574929386995370446001)
                ·
                  refine ⟨1507181197040246527834501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2009574929386995370446001 1507181197040246527834501)
                  ·
                    refine ⟨282596474445046223968969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1507181197040246527834501 282596474445046223968969)
                    ·
                      rfl

theorem cell22_825532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_825532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825532 prefixEnd_825532 := by exact prefixLift 825532
  have htrace : WordTrace (prefixWord ++ tailWord_825532) baseStart_825532 baseEnd_825532 := by
    simpa [prefixWord, tailWord_825532, baseEnd_825532] using wordTrace_append hprefix tailTrace_825532
  have hstable : (prefixWord ++ tailWord_825532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825532).length < 2 ^ (prefixWord ++ tailWord_825532).sum := by decide
  have hdescent : baseEnd_825532 < baseStart_825532 := by decide
  rcases family_descends (prefixWord ++ tailWord_825532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
