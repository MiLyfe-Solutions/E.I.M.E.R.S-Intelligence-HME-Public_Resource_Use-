import V185TrunkScan23Chunk1139

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6752779 : List Nat := [1, 1, 1, 1, 7, 1, 3, 2, 2, 2, 2]
def baseStart_6752779 : Nat := 118140960795 + 6752779 * 2 ^ 59
def prefixEnd_6752779 : Nat := 4983230072969 + 3 ^ 40 * 6752779 * 2
def baseEnd_6752779 : Nat := 3467421380587540454807041

theorem tailTrace_6752779 : CollatzResearch.WordTrace tailWord_6752779 prefixEnd_6752779 3467421380587540454807041 := by
  unfold tailWord_6752779
  simp only [CollatzResearch.WordTrace]
  refine ⟨246294084002842440680773391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164196056001894960453848927 246294084002842440680773391)
  ·
    refine ⟨369441126004263661021160087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246294084002842440680773391 369441126004263661021160087)
    ·
      refine ⟨554161689006395491531740131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369441126004263661021160087 554161689006395491531740131)
      ·
        refine ⟨831242533509593237297610197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554161689006395491531740131 831242533509593237297610197)
        ·
          refine ⟨19482246879131091499162739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 831242533509593237297610197 19482246879131091499162739)
          ·
            refine ⟨29223370318696637248744109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19482246879131091499162739 29223370318696637248744109)
            ·
              refine ⟨10958763869511238968279041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29223370318696637248744109 10958763869511238968279041)
              ·
                refine ⟨8219072902133429226209281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10958763869511238968279041 8219072902133429226209281)
                ·
                  refine ⟨6164304676600071919656961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8219072902133429226209281 6164304676600071919656961)
                  ·
                    refine ⟨4623228507450053939742721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6164304676600071919656961 4623228507450053939742721)
                    ·
                      refine ⟨3467421380587540454807041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623228507450053939742721 3467421380587540454807041)
                      ·
                        rfl

theorem cell23_6752779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 2, 2].length) (baseStart_6752779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752779 prefixEnd_6752779 := by exact prefixLift 6752779
  have htrace : WordTrace (prefixWord ++ tailWord_6752779) baseStart_6752779 baseEnd_6752779 := by
    simpa [prefixWord, tailWord_6752779, baseEnd_6752779] using wordTrace_append hprefix tailTrace_6752779
  have hstable : (prefixWord ++ tailWord_6752779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752779).length < 2 ^ (prefixWord ++ tailWord_6752779).sum := by decide
  have hdescent : baseEnd_6752779 < baseStart_6752779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752796 : List Nat := [2, 2, 3, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_6752796 : Nat := 118140960795 + 6752796 * 2 ^ 59
def prefixEnd_6752796 : Nat := 4983230072969 + 3 ^ 40 * 6752796 * 2
def baseEnd_6752796 : Nat := 3467430109758666888294463

theorem tailTrace_6752796 : CollatzResearch.WordTrace tailWord_6752796 prefixEnd_6752796 3467430109758666888294463 := by
  unfold tailWord_6752796
  simp only [CollatzResearch.WordTrace]
  refine ⟨123147352021890426292071121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164196469362520568389428161 123147352021890426292071121)
  ·
    refine ⟨92360514016417819719053341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123147352021890426292071121 92360514016417819719053341)
    ·
      refine ⟨34635192756156682394645003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92360514016417819719053341 34635192756156682394645003)
      ·
        refine ⟨51952789134235023591967505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34635192756156682394645003 51952789134235023591967505)
        ·
          refine ⟨38964591850676267693975629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51952789134235023591967505 38964591850676267693975629)
          ·
            refine ⟨14611721944003600385240861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38964591850676267693975629 14611721944003600385240861)
            ·
              refine ⟨5479395729001350144465323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14611721944003600385240861 5479395729001350144465323)
              ·
                refine ⟨8219093593502025216697985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479395729001350144465323 8219093593502025216697985)
                ·
                  refine ⟨6164320195126518912523489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8219093593502025216697985 6164320195126518912523489)
                  ·
                    refine ⟨4623240146344889184392617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6164320195126518912523489 4623240146344889184392617)
                    ·
                      refine ⟨3467430109758666888294463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623240146344889184392617 3467430109758666888294463)
                      ·
                        rfl

theorem cell23_6752796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_6752796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752796 prefixEnd_6752796 := by exact prefixLift 6752796
  have htrace : WordTrace (prefixWord ++ tailWord_6752796) baseStart_6752796 baseEnd_6752796 := by
    simpa [prefixWord, tailWord_6752796, baseEnd_6752796] using wordTrace_append hprefix tailTrace_6752796
  have hstable : (prefixWord ++ tailWord_6752796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752796).length < 2 ^ (prefixWord ++ tailWord_6752796).sum := by decide
  have hdescent : baseEnd_6752796 < baseStart_6752796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752805 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 2, 5, 2]
def baseStart_6752805 : Nat := 118140960795 + 6752805 * 2 ^ 59
def prefixEnd_6752805 : Nat := 4983230072969 + 3 ^ 40 * 6752805 * 2
def baseEnd_6752805 : Nat := 3467434731084557353081921

theorem tailTrace_6752805 : CollatzResearch.WordTrace tailWord_6752805 prefixEnd_6752805 3467434731084557353081921 := by
  unfold tailWord_6752805
  simp only [CollatzResearch.WordTrace]
  refine ⟨246295032300748247121219869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164196688200498831414146579 246295032300748247121219869)
  ·
    refine ⟨92360637112780592670457451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246295032300748247121219869 92360637112780592670457451)
    ·
      refine ⟨138540955669170889005686177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92360637112780592670457451 138540955669170889005686177)
      ·
        refine ⟨103905716751878166754264633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138540955669170889005686177 103905716751878166754264633)
        ·
          refine ⟨77929287563908625065698475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103905716751878166754264633 77929287563908625065698475)
          ·
            refine ⟨116893931345862937598547713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77929287563908625065698475 116893931345862937598547713)
            ·
              refine ⟨87670448509397203198910785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116893931345862937598547713 87670448509397203198910785)
              ·
                refine ⟨65752836382047902399183089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87670448509397203198910785 65752836382047902399183089)
                ·
                  refine ⟨49314627286535926799387317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65752836382047902399183089 49314627286535926799387317)
                  ·
                    refine ⟨4623246308112743137442561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49314627286535926799387317 4623246308112743137442561)
                    ·
                      refine ⟨3467434731084557353081921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623246308112743137442561 3467434731084557353081921)
                      ·
                        rfl

theorem cell23_6752805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_6752805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752805 prefixEnd_6752805 := by exact prefixLift 6752805
  have htrace : WordTrace (prefixWord ++ tailWord_6752805) baseStart_6752805 baseEnd_6752805 := by
    simpa [prefixWord, tailWord_6752805, baseEnd_6752805] using wordTrace_append hprefix tailTrace_6752805
  have hstable : (prefixWord ++ tailWord_6752805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752805).length < 2 ^ (prefixWord ++ tailWord_6752805).sum := by decide
  have hdescent : baseEnd_6752805 < baseStart_6752805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752835 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 4, 4, 2]
def baseStart_6752835 : Nat := 118140960795 + 6752835 * 2 ^ 59
def prefixEnd_6752835 : Nat := 4983230072969 + 3 ^ 40 * 6752835 * 2
def baseEnd_6752835 : Nat := 3467450135504192235706783

theorem tailTrace_6752835 : CollatzResearch.WordTrace tailWord_6752835 prefixEnd_6752835 3467450135504192235706783 := by
  unfold tailWord_6752835
  simp only [CollatzResearch.WordTrace]
  refine ⟨246296126490639562244811959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164197417660426374829874639 246296126490639562244811959)
  ·
    refine ⟨369444189735959343367217939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246296126490639562244811959 369444189735959343367217939)
    ·
      refine ⟨554166284603939015050826909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369444189735959343367217939 554166284603939015050826909)
      ·
        refine ⟨207812356726477130644060091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 554166284603939015050826909 207812356726477130644060091)
        ·
          refine ⟨311718535089715695966090137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207812356726477130644060091 311718535089715695966090137)
          ·
            refine ⟨233788901317286771974567603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311718535089715695966090137 233788901317286771974567603)
            ·
              refine ⟨350683351975930157961851405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233788901317286771974567603 350683351975930157961851405)
              ·
                refine ⟨131506256990973809235694277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350683351975930157961851405 131506256990973809235694277)
                ·
                  refine ⟨24657423185807589231692677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131506256990973809235694277 24657423185807589231692677)
                  ·
                    refine ⟨4623266847338922980942377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24657423185807589231692677 4623266847338922980942377)
                    ·
                      refine ⟨3467450135504192235706783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623266847338922980942377 3467450135504192235706783)
                      ·
                        rfl

theorem cell23_6752835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 4, 2].length) (baseStart_6752835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752835 prefixEnd_6752835 := by exact prefixLift 6752835
  have htrace : WordTrace (prefixWord ++ tailWord_6752835) baseStart_6752835 baseEnd_6752835 := by
    simpa [prefixWord, tailWord_6752835, baseEnd_6752835] using wordTrace_append hprefix tailTrace_6752835
  have hstable : (prefixWord ++ tailWord_6752835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752835).length < 2 ^ (prefixWord ++ tailWord_6752835).sum := by decide
  have hdescent : baseEnd_6752835 < baseStart_6752835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752836 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 7]
def baseStart_6752836 : Nat := 118140960795 + 6752836 * 2 ^ 59
def prefixEnd_6752836 : Nat := 4983230072969 + 3 ^ 40 * 6752836 * 2
def baseEnd_6752836 : Nat := 385272294331649636866031

theorem tailTrace_6752836 : CollatzResearch.WordTrace tailWord_6752836 prefixEnd_6752836 385272294331649636866031 := by
  unfold tailWord_6752836
  simp only [CollatzResearch.WordTrace]
  refine ⟨123148081481817969707799181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164197441975757292943732241 123148081481817969707799181)
  ·
    refine ⟨46180530555681738640424693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123148081481817969707799181 46180530555681738640424693)
    ·
      refine ⟨4329424739595162997539815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46180530555681738640424693 4329424739595162997539815)
      ·
        refine ⟨6494137109392744496309723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4329424739595162997539815 6494137109392744496309723)
        ·
          refine ⟨9741205664089116744464585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6494137109392744496309723 9741205664089116744464585)
          ·
            refine ⟨7305904248066837558348439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9741205664089116744464585 7305904248066837558348439)
            ·
              refine ⟨10958856372100256337522659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7305904248066837558348439 10958856372100256337522659)
              ·
                refine ⟨16438284558150384506283989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10958856372100256337522659 16438284558150384506283989)
                ·
                  refine ⟨385272294331649636866031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16438284558150384506283989 385272294331649636866031)
                  ·
                    rfl

theorem cell23_6752836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_6752836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752836 prefixEnd_6752836 := by exact prefixLift 6752836
  have htrace : WordTrace (prefixWord ++ tailWord_6752836) baseStart_6752836 baseEnd_6752836 := by
    simpa [prefixWord, tailWord_6752836, baseEnd_6752836] using wordTrace_append hprefix tailTrace_6752836
  have hstable : (prefixWord ++ tailWord_6752836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752836).length < 2 ^ (prefixWord ++ tailWord_6752836).sum := by decide
  have hdescent : baseEnd_6752836 < baseStart_6752836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752848 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 4]
def baseStart_6752848 : Nat := 118140960795 + 6752848 * 2 ^ 59
def prefixEnd_6752848 : Nat := 4983230072969 + 3 ^ 40 * 6752848 * 2
def baseEnd_6752848 : Nat := 3467456810752700684844223

theorem tailTrace_6752848 : CollatzResearch.WordTrace tailWord_6752848 prefixEnd_6752848 3467456810752700684844223 := by
  unfold tailWord_6752848
  simp only [CollatzResearch.WordTrace]
  refine ⟨123148300319796232732517599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164197733759728310310023465 123148300319796232732517599)
  ·
    refine ⟨184722450479694349098776399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123148300319796232732517599 184722450479694349098776399)
    ·
      refine ⟨277083675719541523648164599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184722450479694349098776399 277083675719541523648164599)
      ·
        refine ⟨415625513579312285472246899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277083675719541523648164599 415625513579312285472246899)
        ·
          refine ⟨623438270368968428208370349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415625513579312285472246899 623438270368968428208370349)
          ·
            refine ⟨233789351388363160578138881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 623438270368968428208370349 233789351388363160578138881)
            ·
              refine ⟨175342013541272370433604161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233789351388363160578138881 175342013541272370433604161)
              ·
                refine ⟨131506510155954277825203121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175342013541272370433604161 131506510155954277825203121)
                ·
                  refine ⟨98629882616965708368902341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131506510155954277825203121 98629882616965708368902341)
                  ·
                    refine ⟨18493102990681070319169189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98629882616965708368902341 18493102990681070319169189)
                    ·
                      refine ⟨3467456810752700684844223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18493102990681070319169189 3467456810752700684844223)
                      ·
                        rfl

theorem cell23_6752848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_6752848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752848 prefixEnd_6752848 := by exact prefixLift 6752848
  have htrace : WordTrace (prefixWord ++ tailWord_6752848) baseStart_6752848 baseEnd_6752848 := by
    simpa [prefixWord, tailWord_6752848, baseEnd_6752848] using wordTrace_append hprefix tailTrace_6752848
  have hstable : (prefixWord ++ tailWord_6752848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752848).length < 2 ^ (prefixWord ++ tailWord_6752848).sum := by decide
  have hdescent : baseEnd_6752848 < baseStart_6752848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752855 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 3]
def baseStart_6752855 : Nat := 118140960795 + 6752855 * 2 ^ 59
def prefixEnd_6752855 : Nat := 4983230072969 + 3 ^ 40 * 6752855 * 2
def baseEnd_6752855 : Nat := 3467460405117282157456691

theorem tailTrace_6752855 : CollatzResearch.WordTrace tailWord_6752855 prefixEnd_6752855 3467460405117282157456691 := by
  unfold tailWord_6752855
  simp only [CollatzResearch.WordTrace]
  refine ⟨246296855950567105660540019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164197903967044737107026679 246296855950567105660540019)
  ·
    refine ⟨369445283925850658490810029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246296855950567105660540019 369445283925850658490810029)
    ·
      refine ⟨138541981472193996934053761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369445283925850658490810029 138541981472193996934053761)
      ·
        refine ⟨103906486104145497700540321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138541981472193996934053761 103906486104145497700540321)
        ·
          refine ⟨77929864578109123275405241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103906486104145497700540321 77929864578109123275405241)
          ·
            refine ⟨58447398433581842456553931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77929864578109123275405241 58447398433581842456553931)
            ·
              refine ⟨87671097650372763684830897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58447398433581842456553931 87671097650372763684830897)
              ·
                refine ⟨65753323237779572763623173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87671097650372763684830897 65753323237779572763623173)
                ·
                  refine ⟨12328748107083669893179345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65753323237779572763623173 12328748107083669893179345)
                  ·
                    refine ⟨9246561080312752419884509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12328748107083669893179345 9246561080312752419884509)
                    ·
                      refine ⟨3467460405117282157456691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9246561080312752419884509 3467460405117282157456691)
                      ·
                        rfl

theorem cell23_6752855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_6752855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752855 prefixEnd_6752855 := by exact prefixLift 6752855
  have htrace : WordTrace (prefixWord ++ tailWord_6752855) baseStart_6752855 baseEnd_6752855 := by
    simpa [prefixWord, tailWord_6752855, baseEnd_6752855] using wordTrace_append hprefix tailTrace_6752855
  have hstable : (prefixWord ++ tailWord_6752855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752855).length < 2 ^ (prefixWord ++ tailWord_6752855).sum := by decide
  have hdescent : baseEnd_6752855 < baseStart_6752855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752896 : List Nat := [2, 1, 1, 2, 1, 7, 2, 2, 1, 4]
def baseStart_6752896 : Nat := 118140960795 + 6752896 * 2 ^ 59
def prefixEnd_6752896 : Nat := 4983230072969 + 3 ^ 40 * 6752896 * 2
def baseEnd_6752896 : Nat := 1155827152608038832348001

theorem tailTrace_6752896 : CollatzResearch.WordTrace tailWord_6752896 prefixEnd_6752896 1155827152608038832348001 := by
  unfold tailWord_6752896
  simp only [CollatzResearch.WordTrace]
  refine ⟨123149175671709284831391271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164198900895612379775188361 123149175671709284831391271)
  ·
    refine ⟨184723763507563927247086907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123149175671709284831391271 184723763507563927247086907)
    ·
      refine ⟨277085645261345890870630361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184723763507563927247086907 277085645261345890870630361)
      ·
        refine ⟨207814233946009418152972771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277085645261345890870630361 207814233946009418152972771)
        ·
          refine ⟨311721350919014127229459157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207814233946009418152972771 311721350919014127229459157)
          ·
            refine ⟨7305969162164393606940449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 311721350919014127229459157 7305969162164393606940449)
            ·
              refine ⟨5479476871623295205205337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7305969162164393606940449 5479476871623295205205337)
              ·
                refine ⟨4109607653717471403904003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5479476871623295205205337 4109607653717471403904003)
                ·
                  refine ⟨6164411480576207105856005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4109607653717471403904003 6164411480576207105856005)
                  ·
                    refine ⟨1155827152608038832348001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6164411480576207105856005 1155827152608038832348001)
                    ·
                      rfl

theorem cell23_6752896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 1, 4].length) (baseStart_6752896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752896 prefixEnd_6752896 := by exact prefixLift 6752896
  have htrace : WordTrace (prefixWord ++ tailWord_6752896) baseStart_6752896 baseEnd_6752896 := by
    simpa [prefixWord, tailWord_6752896, baseEnd_6752896] using wordTrace_append hprefix tailTrace_6752896
  have hstable : (prefixWord ++ tailWord_6752896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752896).length < 2 ^ (prefixWord ++ tailWord_6752896).sum := by decide
  have hdescent : baseEnd_6752896 < baseStart_6752896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752929 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 1, 5, 2]
def baseStart_6752929 : Nat := 118140960795 + 6752929 * 2 ^ 59
def prefixEnd_6752929 : Nat := 4983230072969 + 3 ^ 40 * 6752929 * 2
def baseEnd_6752929 : Nat := 3467498402685714867931351

theorem tailTrace_6752929 : CollatzResearch.WordTrace tailWord_6752929 prefixEnd_6752929 3467498402685714867931351 := by
  unfold tailWord_6752929
  simp only [CollatzResearch.WordTrace]
  refine ⟨246299554952299016298733841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164199703301532677532489227 246299554952299016298733841)
  ·
    refine ⟨184724666214224262224050381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246299554952299016298733841 184724666214224262224050381)
    ·
      refine ⟨69271749830334098334018893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184724666214224262224050381 69271749830334098334018893)
      ·
        refine ⟨25976906186375286875257085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69271749830334098334018893 25976906186375286875257085)
        ·
          refine ⟨9741339819890732578221407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25976906186375286875257085 9741339819890732578221407)
          ·
            refine ⟨14612009729836098867332111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9741339819890732578221407 14612009729836098867332111)
            ·
              refine ⟨21918014594754148300998167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14612009729836098867332111 21918014594754148300998167)
              ·
                refine ⟨32877021892131222451497251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21918014594754148300998167 32877021892131222451497251)
                ·
                  refine ⟨49315532838196833677245877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32877021892131222451497251 49315532838196833677245877)
                  ·
                    refine ⟨4623331203580953157241801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49315532838196833677245877 4623331203580953157241801)
                    ·
                      refine ⟨3467498402685714867931351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623331203580953157241801 3467498402685714867931351)
                      ·
                        rfl

theorem cell23_6752929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_6752929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752929 prefixEnd_6752929 := by exact prefixLift 6752929
  have htrace : WordTrace (prefixWord ++ tailWord_6752929) baseStart_6752929 baseEnd_6752929 := by
    simpa [prefixWord, tailWord_6752929, baseEnd_6752929] using wordTrace_append hprefix tailTrace_6752929
  have hstable : (prefixWord ++ tailWord_6752929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752929).length < 2 ^ (prefixWord ++ tailWord_6752929).sum := by decide
  have hdescent : baseEnd_6752929 < baseStart_6752929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752959 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 3, 2, 2]
def baseStart_6752959 : Nat := 118140960795 + 6752959 * 2 ^ 59
def prefixEnd_6752959 : Nat := 4983230072969 + 3 ^ 40 * 6752959 * 2
def baseEnd_6752959 : Nat := 3467513807105349750556213

theorem tailTrace_6752959 : CollatzResearch.WordTrace tailWord_6752959 prefixEnd_6752959 3467513807105349750556213 := by
  unfold tailWord_6752959
  simp only [CollatzResearch.WordTrace]
  refine ⟨246300649142190331422325931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164200432761460220948217287 246300649142190331422325931)
  ·
    refine ⟨369450973713285497133488897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246300649142190331422325931 369450973713285497133488897)
    ·
      refine ⟨277088230284964122850116673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369450973713285497133488897 277088230284964122850116673)
      ·
        refine ⟨207816172713723092137587505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277088230284964122850116673 207816172713723092137587505)
        ·
          refine ⟨155862129535292319103190629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207816172713723092137587505 155862129535292319103190629)
          ·
            refine ⟨29224149287867309831848243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155862129535292319103190629 29224149287867309831848243)
            ·
              refine ⟨43836223931800964747772365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29224149287867309831848243 43836223931800964747772365)
              ·
                refine ⟨16438583974425361780414637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43836223931800964747772365 16438583974425361780414637)
                ·
                  refine ⟨6164468990409510667655489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16438583974425361780414637 6164468990409510667655489)
                  ·
                    refine ⟨4623351742807133000741617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6164468990409510667655489 4623351742807133000741617)
                    ·
                      refine ⟨3467513807105349750556213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623351742807133000741617 3467513807105349750556213)
                      ·
                        rfl

theorem cell23_6752959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 2, 2].length) (baseStart_6752959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752959 prefixEnd_6752959 := by exact prefixLift 6752959
  have htrace : WordTrace (prefixWord ++ tailWord_6752959) baseStart_6752959 baseEnd_6752959 := by
    simpa [prefixWord, tailWord_6752959, baseEnd_6752959] using wordTrace_append hprefix tailTrace_6752959
  have hstable : (prefixWord ++ tailWord_6752959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752959).length < 2 ^ (prefixWord ++ tailWord_6752959).sum := by decide
  have hdescent : baseEnd_6752959 < baseStart_6752959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752972 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6752972 : Nat := 118140960795 + 6752972 * 2 ^ 59
def prefixEnd_6752972 : Nat := 4983230072969 + 3 ^ 40 * 6752972 * 2
def baseEnd_6752972 : Nat := 3467520482353858199693653

theorem tailTrace_6752972 : CollatzResearch.WordTrace tailWord_6752972 prefixEnd_6752972 3467520482353858199693653 := by
  unfold tailWord_6752972
  simp only [CollatzResearch.WordTrace]
  refine ⟨123150561645571617321274585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164200748860762156428366113 123150561645571617321274585)
  ·
    refine ⟨92362921234178712990955939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123150561645571617321274585 92362921234178712990955939)
    ·
      refine ⟨138544381851268069486433909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92362921234178712990955939 138544381851268069486433909)
      ·
        refine ⟨12988535798556381514353179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138544381851268069486433909 12988535798556381514353179)
        ·
          refine ⟨19482803697834572271529769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12988535798556381514353179 19482803697834572271529769)
          ·
            refine ⟨14612102773375929203647327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19482803697834572271529769 14612102773375929203647327)
            ·
              refine ⟨21918154160063893805470991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14612102773375929203647327 21918154160063893805470991)
              ·
                refine ⟨32877231240095840708206487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21918154160063893805470991 32877231240095840708206487)
                ·
                  refine ⟨49315846860143761062309731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32877231240095840708206487 49315846860143761062309731)
                  ·
                    refine ⟨73973770290215641593464597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49315846860143761062309731 73973770290215641593464597)
                    ·
                      refine ⟨3467520482353858199693653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73973770290215641593464597 3467520482353858199693653)
                      ·
                        rfl

theorem cell23_6752972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6752972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752972 prefixEnd_6752972 := by exact prefixLift 6752972
  have htrace : WordTrace (prefixWord ++ tailWord_6752972) baseStart_6752972 baseEnd_6752972 := by
    simpa [prefixWord, tailWord_6752972, baseEnd_6752972] using wordTrace_append hprefix tailTrace_6752972
  have hstable : (prefixWord ++ tailWord_6752972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752972).length < 2 ^ (prefixWord ++ tailWord_6752972).sum := by decide
  have hdescent : baseEnd_6752972 < baseStart_6752972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6752993 : List Nat := [1, 2, 3, 1, 4, 1, 3, 3, 1, 2, 2]
def baseStart_6752993 : Nat := 118140960795 + 6752993 * 2 ^ 59
def prefixEnd_6752993 : Nat := 4983230072969 + 3 ^ 40 * 6752993 * 2
def baseEnd_6752993 : Nat := 3467531265447602617531057

theorem tailTrace_6752993 : CollatzResearch.WordTrace tailWord_6752993 prefixEnd_6752993 3467531265447602617531057 := by
  unfold tailWord_6752993
  simp only [CollatzResearch.WordTrace]
  refine ⟨246301889224067155229063633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164201259482711436819375755 246301889224067155229063633)
  ·
    refine ⟨184726416918050366421797725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246301889224067155229063633 184726416918050366421797725)
    ·
      refine ⟨69272406344268887408174147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184726416918050366421797725 69272406344268887408174147)
      ·
        refine ⟨103908609516403331112261221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69272406344268887408174147 103908609516403331112261221)
        ·
          refine ⟨19482864284325624583548979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103908609516403331112261221 19482864284325624583548979)
          ·
            refine ⟨29224296426488436875323469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19482864284325624583548979 29224296426488436875323469)
            ·
              refine ⟨10959111159933163828246301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29224296426488436875323469 10959111159933163828246301)
              ·
                refine ⟨4109666684974936435592363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10959111159933163828246301 4109666684974936435592363)
                ·
                  refine ⟨6164500027462404653388545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4109666684974936435592363 6164500027462404653388545)
                  ·
                    refine ⟨4623375020596803490041409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6164500027462404653388545 4623375020596803490041409)
                    ·
                      refine ⟨3467531265447602617531057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623375020596803490041409 3467531265447602617531057)
                      ·
                        rfl

theorem cell23_6752993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_6752993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6752993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6752993 prefixEnd_6752993 := by exact prefixLift 6752993
  have htrace : WordTrace (prefixWord ++ tailWord_6752993) baseStart_6752993 baseEnd_6752993 := by
    simpa [prefixWord, tailWord_6752993, baseEnd_6752993] using wordTrace_append hprefix tailTrace_6752993
  have hstable : (prefixWord ++ tailWord_6752993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6752993).length < 2 ^ (prefixWord ++ tailWord_6752993).sum := by decide
  have hdescent : baseEnd_6752993 < baseStart_6752993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6752993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753009 : List Nat := [1, 2, 2, 2, 2, 2, 2, 4, 2, 1, 3]
def baseStart_6753009 : Nat := 118140960795 + 6753009 * 2 ^ 59
def prefixEnd_6753009 : Nat := 4983230072969 + 3 ^ 40 * 6753009 * 2
def baseEnd_6753009 : Nat := 3467539481138074554930983

theorem tailTrace_6753009 : CollatzResearch.WordTrace tailWord_6753009 prefixEnd_6753009 3467539481138074554930983 := by
  unfold tailWord_6753009
  simp only [CollatzResearch.WordTrace]
  refine ⟨246302472792009189961646081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164201648528006126641097387 246302472792009189961646081)
  ·
    refine ⟨184726854594006892471234561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246302472792009189961646081 184726854594006892471234561)
    ·
      refine ⟨138545140945505169353425921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184726854594006892471234561 138545140945505169353425921)
      ·
        refine ⟨103908855709128877015069441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138545140945505169353425921 103908855709128877015069441)
        ·
          refine ⟨77931641781846657761302081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103908855709128877015069441 77931641781846657761302081)
          ·
            refine ⟨58448731336384993320976561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77931641781846657761302081 58448731336384993320976561)
            ·
              refine ⟨43836548502288744990732421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58448731336384993320976561 43836548502288744990732421)
              ·
                refine ⟨8219352844179139685762329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43836548502288744990732421 8219352844179139685762329)
                ·
                  refine ⟨6164514633134354764321747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8219352844179139685762329 6164514633134354764321747)
                  ·
                    refine ⟨9246771949701532146482621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6164514633134354764321747 9246771949701532146482621)
                    ·
                      refine ⟨3467539481138074554930983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9246771949701532146482621 3467539481138074554930983)
                      ·
                        rfl

theorem cell23_6753009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_6753009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753009 prefixEnd_6753009 := by exact prefixLift 6753009
  have htrace : WordTrace (prefixWord ++ tailWord_6753009) baseStart_6753009 baseEnd_6753009 := by
    simpa [prefixWord, tailWord_6753009, baseEnd_6753009] using wordTrace_append hprefix tailTrace_6753009
  have hstable : (prefixWord ++ tailWord_6753009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753009).length < 2 ^ (prefixWord ++ tailWord_6753009).sum := by decide
  have hdescent : baseEnd_6753009 < baseStart_6753009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753010 : List Nat := [3, 2, 1, 3, 1, 3, 3, 2, 1, 2, 2]
def baseStart_6753010 : Nat := 118140960795 + 6753010 * 2 ^ 59
def prefixEnd_6753010 : Nat := 4983230072969 + 3 ^ 40 * 6753010 * 2
def baseEnd_6753010 : Nat := 3467539994618729051018479

theorem tailTrace_6753010 : CollatzResearch.WordTrace tailWord_6753010 prefixEnd_6753010 3467539994618729051018479 := by
  unfold tailWord_6753010
  simp only [CollatzResearch.WordTrace]
  refine ⟨61575627316251391783108121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164201672843337044754954989 61575627316251391783108121)
  ·
    refine ⟨46181720487188543837331091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61575627316251391783108121 46181720487188543837331091)
    ·
      refine ⟨69272580730782815755996637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46181720487188543837331091 69272580730782815755996637)
      ·
        refine ⟨25977217774043555908498739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69272580730782815755996637 25977217774043555908498739)
        ·
          refine ⟨38965826661065333862748109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25977217774043555908498739 38965826661065333862748109)
          ·
            refine ⟨14612184997899500198530541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38965826661065333862748109 14612184997899500198530541)
            ·
              refine ⟨5479569374212312574448953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14612184997899500198530541 5479569374212312574448953)
              ·
                refine ⟨4109677030659234430836715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5479569374212312574448953 4109677030659234430836715)
                ·
                  refine ⟨6164515545988851646255073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4109677030659234430836715 6164515545988851646255073)
                  ·
                    refine ⟨4623386659491638734691305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6164515545988851646255073 4623386659491638734691305)
                    ·
                      refine ⟨3467539994618729051018479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623386659491638734691305 3467539994618729051018479)
                      ·
                        rfl

theorem cell23_6753010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_6753010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753010 prefixEnd_6753010 := by exact prefixLift 6753010
  have htrace : WordTrace (prefixWord ++ tailWord_6753010) baseStart_6753010 baseEnd_6753010 := by
    simpa [prefixWord, tailWord_6753010, baseEnd_6753010] using wordTrace_append hprefix tailTrace_6753010
  have hstable : (prefixWord ++ tailWord_6753010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753010).length < 2 ^ (prefixWord ++ tailWord_6753010).sum := by decide
  have hdescent : baseEnd_6753010 < baseStart_6753010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753015 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_6753015 : Nat := 118140960795 + 6753015 * 2 ^ 59
def prefixEnd_6753015 : Nat := 4983230072969 + 3 ^ 40 * 6753015 * 2
def baseEnd_6753015 : Nat := 3467542562022001531455955

theorem tailTrace_6753015 : CollatzResearch.WordTrace tailWord_6753015 prefixEnd_6753015 3467542562022001531455955 := by
  unfold tailWord_6753015
  simp only [CollatzResearch.WordTrace]
  refine ⟨246302691629987452986364499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164201794419991635324242999 246302691629987452986364499)
  ·
    refine ⟨369454037444981179479546749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246302691629987452986364499 369454037444981179479546749)
    ·
      refine ⟨138545264041867942304830031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369454037444981179479546749 138545264041867942304830031)
      ·
        refine ⟨207817896062801913457245047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138545264041867942304830031 207817896062801913457245047)
        ·
          refine ⟨311726844094202870185867571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207817896062801913457245047 311726844094202870185867571)
          ·
            refine ⟨467590266141304305278801357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311726844094202870185867571 467590266141304305278801357)
            ·
              refine ⟨175346349802989114479550509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 467590266141304305278801357 175346349802989114479550509)
              ·
                refine ⟨65754881176120917929831441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175346349802989114479550509 65754881176120917929831441)
                ·
                  refine ⟨49316160882090688447373581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65754881176120917929831441 49316160882090688447373581)
                  ·
                    refine ⟨18493560330784008167765093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49316160882090688447373581 18493560330784008167765093)
                    ·
                      refine ⟨3467542562022001531455955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18493560330784008167765093 3467542562022001531455955)
                      ·
                        rfl

theorem cell23_6753015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_6753015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753015 prefixEnd_6753015 := by exact prefixLift 6753015
  have htrace : WordTrace (prefixWord ++ tailWord_6753015) baseStart_6753015 baseEnd_6753015 := by
    simpa [prefixWord, tailWord_6753015, baseEnd_6753015] using wordTrace_append hprefix tailTrace_6753015
  have hstable : (prefixWord ++ tailWord_6753015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753015).length < 2 ^ (prefixWord ++ tailWord_6753015).sum := by decide
  have hdescent : baseEnd_6753015 < baseStart_6753015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753025 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 1, 8]
def baseStart_6753025 : Nat := 118140960795 + 6753025 * 2 ^ 59
def prefixEnd_6753025 : Nat := 4983230072969 + 3 ^ 40 * 6753025 * 2
def baseEnd_6753025 : Nat := 1155849232276182164110303

theorem tailTrace_6753025 : CollatzResearch.WordTrace tailWord_6753025 prefixEnd_6753025 1155849232276182164110303 := by
  unfold tailWord_6753025
  simp only [CollatzResearch.WordTrace]
  refine ⟨246303056359951224694228529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164202037573300816462819019 246303056359951224694228529)
  ·
    refine ⟨184727292269963418520671397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246303056359951224694228529 184727292269963418520671397)
    ·
      refine ⟨34636367300618140972625887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184727292269963418520671397 34636367300618140972625887)
      ·
        refine ⟨51954550950927211458938831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34636367300618140972625887 51954550950927211458938831)
        ·
          refine ⟨77931826426390817188408247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51954550950927211458938831 77931826426390817188408247)
          ·
            refine ⟨116897739639586225782612371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77931826426390817188408247 116897739639586225782612371)
            ·
              refine ⟨175346609459379338673918557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116897739639586225782612371 175346609459379338673918557)
              ·
                refine ⟨65754978547267252002719459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175346609459379338673918557 65754978547267252002719459)
                ·
                  refine ⟨98632467820900878004079189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65754978547267252002719459 98632467820900878004079189)
                  ·
                    refine ⟨1155849232276182164110303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98632467820900878004079189 1155849232276182164110303)
                    ·
                      rfl

theorem cell23_6753025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_6753025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753025 prefixEnd_6753025 := by exact prefixLift 6753025
  have htrace : WordTrace (prefixWord ++ tailWord_6753025) baseStart_6753025 baseEnd_6753025 := by
    simpa [prefixWord, tailWord_6753025, baseEnd_6753025] using wordTrace_append hprefix tailTrace_6753025
  have hstable : (prefixWord ++ tailWord_6753025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753025).length < 2 ^ (prefixWord ++ tailWord_6753025).sum := by decide
  have hdescent : baseEnd_6753025 < baseStart_6753025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753049 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 4, 2, 2]
def baseStart_6753049 : Nat := 118140960795 + 6753049 * 2 ^ 59
def prefixEnd_6753049 : Nat := 4983230072969 + 3 ^ 40 * 6753049 * 2
def baseEnd_6753049 : Nat := 3467560020364254398430799

theorem tailTrace_6753049 : CollatzResearch.WordTrace tailWord_6753049 prefixEnd_6753049 3467560020364254398430799 := by
  unfold tailWord_6753049
  simp only [CollatzResearch.WordTrace]
  refine ⟨246303931711864276793102201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164202621141242851195401467 246303931711864276793102201)
  ·
    refine ⟨184727948783898207594826651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246303931711864276793102201 184727948783898207594826651)
    ·
      refine ⟨277091923175847311392239977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184727948783898207594826651 277091923175847311392239977)
      ·
        refine ⟨207818942381885483544179983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277091923175847311392239977 207818942381885483544179983)
        ·
          refine ⟨311728413572828225316269975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207818942381885483544179983 311728413572828225316269975)
          ·
            refine ⟨467592620359242337974404963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311728413572828225316269975 467592620359242337974404963)
            ·
              refine ⟨701388930538863506961607445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467592620359242337974404963 701388930538863506961607445)
              ·
                refine ⟨32877606119009226888825349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 701388930538863506961607445 32877606119009226888825349)
                ·
                  refine ⟨6164551147314230041654753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32877606119009226888825349 6164551147314230041654753)
                  ·
                    refine ⟨4623413360485672531241065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6164551147314230041654753 4623413360485672531241065)
                    ·
                      refine ⟨3467560020364254398430799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623413360485672531241065 3467560020364254398430799)
                      ·
                        rfl

theorem cell23_6753049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 2, 2].length) (baseStart_6753049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753049 prefixEnd_6753049 := by exact prefixLift 6753049
  have htrace : WordTrace (prefixWord ++ tailWord_6753049) baseStart_6753049 baseEnd_6753049 := by
    simpa [prefixWord, tailWord_6753049, baseEnd_6753049] using wordTrace_append hprefix tailTrace_6753049
  have hstable : (prefixWord ++ tailWord_6753049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753049).length < 2 ^ (prefixWord ++ tailWord_6753049).sum := by decide
  have hdescent : baseEnd_6753049 < baseStart_6753049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753052 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_6753052 : Nat := 118140960795 + 6753052 * 2 ^ 59
def prefixEnd_6753052 : Nat := 4983230072969 + 3 ^ 40 * 6753052 * 2
def baseEnd_6753052 : Nat := 3467561560806217886693285

theorem tailTrace_6753052 : CollatzResearch.WordTrace tailWord_6753052 prefixEnd_6753052 3467561560806217886693285 := by
  unfold tailWord_6753052
  simp only [CollatzResearch.WordTrace]
  refine ⟨123152020565426704152730705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164202694087235605536974273 123152020565426704152730705)
  ·
    refine ⟨92364015424070028114548029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123152020565426704152730705 92364015424070028114548029)
    ·
      refine ⟨34636505784026260542955511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92364015424070028114548029 34636505784026260542955511)
      ·
        refine ⟨51954758676039390814433267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34636505784026260542955511 51954758676039390814433267)
        ·
          refine ⟨77932138014059086221649901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51954758676039390814433267 77932138014059086221649901)
          ·
            refine ⟨29224551755272157333118713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77932138014059086221649901 29224551755272157333118713)
            ·
              refine ⟨21918413816454117999839035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29224551755272157333118713 21918413816454117999839035)
              ·
                refine ⟨32877620724681176999758553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21918413816454117999839035 32877620724681176999758553)
                ·
                  refine ⟨24658215543510882749818915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32877620724681176999758553 24658215543510882749818915)
                  ·
                    refine ⟨36987323315266324124728373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24658215543510882749818915 36987323315266324124728373)
                    ·
                      refine ⟨3467561560806217886693285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36987323315266324124728373 3467561560806217886693285)
                      ·
                        rfl

theorem cell23_6753052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_6753052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753052 prefixEnd_6753052 := by exact prefixLift 6753052
  have htrace : WordTrace (prefixWord ++ tailWord_6753052) baseStart_6753052 baseEnd_6753052 := by
    simpa [prefixWord, tailWord_6753052, baseEnd_6753052] using wordTrace_append hprefix tailTrace_6753052
  have hstable : (prefixWord ++ tailWord_6753052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753052).length < 2 ^ (prefixWord ++ tailWord_6753052).sum := by decide
  have hdescent : baseEnd_6753052 < baseStart_6753052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753139 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 2, 4, 2]
def baseStart_6753139 : Nat := 118140960795 + 6753139 * 2 ^ 59
def prefixEnd_6753139 : Nat := 4983230072969 + 3 ^ 40 * 6753139 * 2
def baseEnd_6753139 : Nat := 3467606233623159046305385

theorem tailTrace_6753139 : CollatzResearch.WordTrace tailWord_6753139 prefixEnd_6753139 3467606233623159046305385 := by
  unfold tailWord_6753139
  simp only [CollatzResearch.WordTrace]
  refine ⟨246307214281538222163878471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164204809521025481442585647 246307214281538222163878471)
  ·
    refine ⟨369460821422307333245817707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246307214281538222163878471 369460821422307333245817707)
    ·
      refine ⟨554191232133460999868726561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369460821422307333245817707 554191232133460999868726561)
      ·
        refine ⟨415643424100095749901544921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554191232133460999868726561 415643424100095749901544921)
        ·
          refine ⟨311732568075071812426158691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415643424100095749901544921 311732568075071812426158691)
          ·
            refine ⟨467598852112607718639238037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311732568075071812426158691 467598852112607718639238037)
            ·
              refine ⟨21918696192778486811214283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 467598852112607718639238037 21918696192778486811214283)
              ·
                refine ⟨32878044289167730216821425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21918696192778486811214283 32878044289167730216821425)
                ·
                  refine ⟨24658533216875797662616069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32878044289167730216821425 24658533216875797662616069)
                  ·
                    refine ⟨4623474978164212061740513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24658533216875797662616069 4623474978164212061740513)
                    ·
                      refine ⟨3467606233623159046305385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623474978164212061740513 3467606233623159046305385)
                      ·
                        rfl

theorem cell23_6753139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 4, 2].length) (baseStart_6753139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753139 prefixEnd_6753139 := by exact prefixLift 6753139
  have htrace : WordTrace (prefixWord ++ tailWord_6753139) baseStart_6753139 baseEnd_6753139 := by
    simpa [prefixWord, tailWord_6753139, baseEnd_6753139] using wordTrace_append hprefix tailTrace_6753139
  have hstable : (prefixWord ++ tailWord_6753139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753139).length < 2 ^ (prefixWord ++ tailWord_6753139).sum := by decide
  have hdescent : baseEnd_6753139 < baseStart_6753139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753149 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_6753149 : Nat := 118140960795 + 6753149 * 2 ^ 59
def prefixEnd_6753149 : Nat := 4983230072969 + 3 ^ 40 * 6753149 * 2
def baseEnd_6753149 : Nat := 1155870456143234669060113

theorem tailTrace_6753149 : CollatzResearch.WordTrace tailWord_6753149 prefixEnd_6753149 1155870456143234669060113 := by
  unfold tailWord_6753149
  simp only [CollatzResearch.WordTrace]
  refine ⟨246307579011501993871742501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164205052674334662581161667 246307579011501993871742501)
  ·
    refine ⟨46182671064656623850951719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246307579011501993871742501 46182671064656623850951719)
    ·
      refine ⟨69274006596984935776427579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46182671064656623850951719 69274006596984935776427579)
      ·
        refine ⟨103911009895477403664641369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69274006596984935776427579 103911009895477403664641369)
        ·
          refine ⟨77933257421608052748481027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103911009895477403664641369 77933257421608052748481027)
          ·
            refine ⟨116899886132412079122721541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77933257421608052748481027 116899886132412079122721541)
            ·
              refine ⟨21918728649827264835510289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116899886132412079122721541 21918728649827264835510289)
              ·
                refine ⟨16439046487370448626632717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21918728649827264835510289 16439046487370448626632717)
                ·
                  refine ⟨6164642432763918234987269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16439046487370448626632717 6164642432763918234987269)
                  ·
                    refine ⟨1155870456143234669060113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6164642432763918234987269 1155870456143234669060113)
                    ·
                      rfl

theorem cell23_6753149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_6753149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753149 prefixEnd_6753149 := by exact prefixLift 6753149
  have htrace : WordTrace (prefixWord ++ tailWord_6753149) baseStart_6753149 baseEnd_6753149 := by
    simpa [prefixWord, tailWord_6753149, baseEnd_6753149] using wordTrace_append hprefix tailTrace_6753149
  have hstable : (prefixWord ++ tailWord_6753149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753149).length < 2 ^ (prefixWord ++ tailWord_6753149).sum := by decide
  have hdescent : baseEnd_6753149 < baseStart_6753149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753159 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_6753159 : Nat := 118140960795 + 6753159 * 2 ^ 59
def prefixEnd_6753159 : Nat := 4983230072969 + 3 ^ 40 * 6753159 * 2
def baseEnd_6753159 : Nat := 3467616503236248968055293

theorem tailTrace_6753159 : CollatzResearch.WordTrace tailWord_6753159 prefixEnd_6753159 3467616503236248968055293 := by
  unfold tailWord_6753159
  simp only [CollatzResearch.WordTrace]
  refine ⟨246307943741465765579606531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164205295827643843719737687 246307943741465765579606531)
  ·
    refine ⟨369461915612198648369409797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246307943741465765579606531 369461915612198648369409797)
    ·
      refine ⟨69274109177287246569264337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 369461915612198648369409797 69274109177287246569264337)
      ·
        refine ⟨51955581882965434926948253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69274109177287246569264337 51955581882965434926948253)
        ·
          refine ⟨19483343206112038097605595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51955581882965434926948253 19483343206112038097605595)
          ·
            refine ⟨29225014809168057146408393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19483343206112038097605595 29225014809168057146408393)
            ·
              refine ⟨21918761106876042859806295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29225014809168057146408393 21918761106876042859806295)
              ·
                refine ⟨32878141660314064289709443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21918761106876042859806295 32878141660314064289709443)
                ·
                  refine ⟨49317212490471096434564165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32878141660314064289709443 49317212490471096434564165)
                  ·
                    refine ⟨9246977341963330581480781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49317212490471096434564165 9246977341963330581480781)
                    ·
                      refine ⟨3467616503236248968055293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9246977341963330581480781 3467616503236248968055293)
                      ·
                        rfl

theorem cell23_6753159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_6753159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753159 prefixEnd_6753159 := by exact prefixLift 6753159
  have htrace : WordTrace (prefixWord ++ tailWord_6753159) baseStart_6753159 baseEnd_6753159 := by
    simpa [prefixWord, tailWord_6753159, baseEnd_6753159] using wordTrace_append hprefix tailTrace_6753159
  have hstable : (prefixWord ++ tailWord_6753159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753159).length < 2 ^ (prefixWord ++ tailWord_6753159).sum := by decide
  have hdescent : baseEnd_6753159 < baseStart_6753159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753199 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 1, 5, 2]
def baseStart_6753199 : Nat := 118140960795 + 6753199 * 2 ^ 59
def prefixEnd_6753199 : Nat := 4983230072969 + 3 ^ 40 * 6753199 * 2
def baseEnd_6753199 : Nat := 3467637042462428811555109

theorem tailTrace_6753199 : CollatzResearch.WordTrace tailWord_6753199 prefixEnd_6753199 3467637042462428811555109 := by
  unfold tailWord_6753199
  simp only [CollatzResearch.WordTrace]
  refine ⟨246309402661320852411062651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164206268440880568274041767 246309402661320852411062651)
  ·
    refine ⟨369464103991981278616593977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246309402661320852411062651 369464103991981278616593977)
    ·
      refine ⟨277098077993985958962445483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369464103991981278616593977 277098077993985958962445483)
      ·
        refine ⟨415647116990978938443668225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277098077993985958962445483 415647116990978938443668225)
        ·
          refine ⟨311735337743234203832751169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415647116990978938443668225 311735337743234203832751169)
          ·
            refine ⟨233801503307425652874563377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311735337743234203832751169 233801503307425652874563377)
            ·
              refine ⟨175351127480569239655922533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233801503307425652874563377 175351127480569239655922533)
              ·
                refine ⟨32878336402606732435485475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175351127480569239655922533 32878336402606732435485475)
                ·
                  refine ⟨49317504603910098653228213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32878336402606732435485475 49317504603910098653228213)
                  ·
                    refine ⟨4623516056616571748740145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49317504603910098653228213 4623516056616571748740145)
                    ·
                      refine ⟨3467637042462428811555109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623516056616571748740145 3467637042462428811555109)
                      ·
                        rfl

theorem cell23_6753199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 5, 2].length) (baseStart_6753199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753199 prefixEnd_6753199 := by exact prefixLift 6753199
  have htrace : WordTrace (prefixWord ++ tailWord_6753199) baseStart_6753199 baseEnd_6753199 := by
    simpa [prefixWord, tailWord_6753199, baseEnd_6753199] using wordTrace_append hprefix tailTrace_6753199
  have hstable : (prefixWord ++ tailWord_6753199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753199).length < 2 ^ (prefixWord ++ tailWord_6753199).sum := by decide
  have hdescent : baseEnd_6753199 < baseStart_6753199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753209 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 3, 5]
def baseStart_6753209 : Nat := 118140960795 + 6753209 * 2 ^ 59
def prefixEnd_6753209 : Nat := 4983230072969 + 3 ^ 40 * 6753209 * 2
def baseEnd_6753209 : Nat := 1155880725756324590810021

theorem tailTrace_6753209 : CollatzResearch.WordTrace tailWord_6753209 prefixEnd_6753209 1155880725756324590810021 := by
  unfold tailWord_6753209
  simp only [CollatzResearch.WordTrace]
  refine ⟨246309767391284624118926681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164206511594189749412617787 246309767391284624118926681)
  ·
    refine ⟨184732325543463468089195011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246309767391284624118926681 184732325543463468089195011)
    ·
      refine ⟨277098488315195202133792517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184732325543463468089195011 277098488315195202133792517)
      ·
        refine ⟨51955966559099100400086097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277098488315195202133792517 51955966559099100400086097)
        ·
          refine ⟨38966974919324325300064573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51955966559099100400086097 38966974919324325300064573)
          ·
            refine ⟨14612615594746621987524215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38966974919324325300064573 14612615594746621987524215)
            ·
              refine ⟨21918923392119932981286323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14612615594746621987524215 21918923392119932981286323)
              ·
                refine ⟨32878385088179899471929485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21918923392119932981286323 32878385088179899471929485)
                ·
                  refine ⟨12329394408067462301973557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32878385088179899471929485 12329394408067462301973557)
                  ·
                    refine ⟨1155880725756324590810021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12329394408067462301973557 1155880725756324590810021)
                    ·
                      rfl

theorem cell23_6753209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 5].length) (baseStart_6753209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753209 prefixEnd_6753209 := by exact prefixLift 6753209
  have htrace : WordTrace (prefixWord ++ tailWord_6753209) baseStart_6753209 baseEnd_6753209 := by
    simpa [prefixWord, tailWord_6753209, baseEnd_6753209] using wordTrace_append hprefix tailTrace_6753209
  have hstable : (prefixWord ++ tailWord_6753209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753209).length < 2 ^ (prefixWord ++ tailWord_6753209).sum := by decide
  have hdescent : baseEnd_6753209 < baseStart_6753209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753216 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 2, 3, 2]
def baseStart_6753216 : Nat := 118140960795 + 6753216 * 2 ^ 59
def prefixEnd_6753216 : Nat := 4983230072969 + 3 ^ 40 * 6753216 * 2
def baseEnd_6753216 : Nat := 3467645771633555245042531

theorem tailTrace_6753216 : CollatzResearch.WordTrace tailWord_6753216 prefixEnd_6753216 3467645771633555245042531 := by
  unfold tailWord_6753216
  simp only [CollatzResearch.WordTrace]
  refine ⟨123155011351129632157215751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164206681801506176209621001 123155011351129632157215751)
  ·
    refine ⟨184732517026694448235823627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123155011351129632157215751 184732517026694448235823627)
    ·
      refine ⟨277098775540041672353735441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184732517026694448235823627 277098775540041672353735441)
      ·
        refine ⟨207824081655031254265301581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277098775540041672353735441 207824081655031254265301581)
        ·
          refine ⟨77934030620636720349488093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207824081655031254265301581 77934030620636720349488093)
          ·
            refine ⟨29225261482738770131058035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77934030620636720349488093 29225261482738770131058035)
            ·
              refine ⟨43837892224108155196587053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29225261482738770131058035 43837892224108155196587053)
              ·
                refine ⟨16439209584040558198720145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43837892224108155196587053 16439209584040558198720145)
                ·
                  refine ⟨12329407188030418649040109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16439209584040558198720145 12329407188030418649040109)
                  ·
                    refine ⟨4623527695511406993390041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12329407188030418649040109 4623527695511406993390041)
                    ·
                      refine ⟨3467645771633555245042531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623527695511406993390041 3467645771633555245042531)
                      ·
                        rfl

theorem cell23_6753216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2, 3, 2].length) (baseStart_6753216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753216 prefixEnd_6753216 := by exact prefixLift 6753216
  have htrace : WordTrace (prefixWord ++ tailWord_6753216) baseStart_6753216 baseEnd_6753216 := by
    simpa [prefixWord, tailWord_6753216, baseEnd_6753216] using wordTrace_append hprefix tailTrace_6753216
  have hstable : (prefixWord ++ tailWord_6753216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753216).length < 2 ^ (prefixWord ++ tailWord_6753216).sum := by decide
  have hdescent : baseEnd_6753216 < baseStart_6753216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753240 : List Nat := [2, 1, 2, 2, 2, 3, 4, 2, 1, 1, 3]
def baseStart_6753240 : Nat := 118140960795 + 6753240 * 2 ^ 59
def prefixEnd_6753240 : Nat := 4983230072969 + 3 ^ 40 * 6753240 * 2
def baseEnd_6753240 : Nat := 3467658095169263151142421

theorem tailTrace_6753240 : CollatzResearch.WordTrace tailWord_6753240 prefixEnd_6753240 3467658095169263151142421 := by
  unfold tailWord_6753240
  simp only [CollatzResearch.WordTrace]
  refine ⟨123155449027086158206652587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164207265369448210942203449 123155449027086158206652587)
  ·
    refine ⟨184733173540629237309978881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123155449027086158206652587 184733173540629237309978881)
    ·
      refine ⟨138549880155471927982484161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184733173540629237309978881 138549880155471927982484161)
      ·
        refine ⟨103912410116603945986863121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138549880155471927982484161 103912410116603945986863121)
        ·
          refine ⟨77934307587452959490147341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103912410116603945986863121 77934307587452959490147341)
          ·
            refine ⟨29225365345294859808805253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77934307587452959490147341 29225365345294859808805253)
            ·
              refine ⟨5479756002242786214150985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29225365345294859808805253 5479756002242786214150985)
              ·
                refine ⟨4109817001682089660613239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5479756002242786214150985 4109817001682089660613239)
                ·
                  refine ⟨6164725502523134490919859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4109817001682089660613239 6164725502523134490919859)
                  ·
                    refine ⟨9247088253784701736379789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6164725502523134490919859 9247088253784701736379789)
                    ·
                      refine ⟨3467658095169263151142421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9247088253784701736379789 3467658095169263151142421)
                      ·
                        rfl

theorem cell23_6753240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_6753240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753240 prefixEnd_6753240 := by exact prefixLift 6753240
  have htrace : WordTrace (prefixWord ++ tailWord_6753240) baseStart_6753240 baseEnd_6753240 := by
    simpa [prefixWord, tailWord_6753240, baseEnd_6753240] using wordTrace_append hprefix tailTrace_6753240
  have hstable : (prefixWord ++ tailWord_6753240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753240).length < 2 ^ (prefixWord ++ tailWord_6753240).sum := by decide
  have hdescent : baseEnd_6753240 < baseStart_6753240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753252 : List Nat := [2, 3, 1, 1, 1, 1, 2, 12]
def baseStart_6753252 : Nat := 118140960795 + 6753252 * 2 ^ 59
def prefixEnd_6753252 : Nat := 4983230072969 + 3 ^ 40 * 6753252 * 2
def baseEnd_6753252 : Nat := 128432009516189522377495

theorem tailTrace_6753252 : CollatzResearch.WordTrace tailWord_6753252 prefixEnd_6753252 128432009516189522377495 := by
  unfold tailWord_6753252
  simp only [CollatzResearch.WordTrace]
  refine ⟨123155667865064421231371005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164207557153419228308494673 123155667865064421231371005)
  ·
    refine ⟨46183375449399157961764127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123155667865064421231371005 46183375449399157961764127)
    ·
      refine ⟨69275063174098736942646191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46183375449399157961764127 69275063174098736942646191)
      ·
        refine ⟨103912594761148105413969287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69275063174098736942646191 103912594761148105413969287)
        ·
          refine ⟨155868892141722158120953931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103912594761148105413969287 155868892141722158120953931)
          ·
            refine ⟨233803338212583237181430897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155868892141722158120953931 233803338212583237181430897)
            ·
              refine ⟨175352503659437427886073173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233803338212583237181430897 175352503659437427886073173)
              ·
                refine ⟨128432009516189522377495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 175352503659437427886073173 128432009516189522377495)
                ·
                  rfl

theorem cell23_6753252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 12].length) (baseStart_6753252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753252 prefixEnd_6753252 := by exact prefixLift 6753252
  have htrace : WordTrace (prefixWord ++ tailWord_6753252) baseStart_6753252 baseEnd_6753252 := by
    simpa [prefixWord, tailWord_6753252, baseEnd_6753252] using wordTrace_append hprefix tailTrace_6753252
  have hstable : (prefixWord ++ tailWord_6753252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753252).length < 2 ^ (prefixWord ++ tailWord_6753252).sum := by decide
  have hdescent : baseEnd_6753252 < baseStart_6753252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753256 : List Nat := [2, 1, 4, 1, 1, 1, 4, 3, 2, 4]
def baseStart_6753256 : Nat := 118140960795 + 6753256 * 2 ^ 59
def prefixEnd_6753256 : Nat := 4983230072969 + 3 ^ 40 * 6753256 * 2
def baseEnd_6753256 : Nat := 1155888770286578362847449

theorem tailTrace_6753256 : CollatzResearch.WordTrace tailWord_6753256 prefixEnd_6753256 1155888770286578362847449 := by
  unfold tailWord_6753256
  simp only [CollatzResearch.WordTrace]
  refine ⟨123155740811057175572943811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164207654414742900763925081 123155740811057175572943811)
  ·
    refine ⟨184733611216585763359415717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123155740811057175572943811 184733611216585763359415717)
    ·
      refine ⟨34637552103109830629890447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184733611216585763359415717 34637552103109830629890447)
      ·
        refine ⟨51956328154664745944835671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34637552103109830629890447 51956328154664745944835671)
        ·
          refine ⟨77934492231997118917253507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51956328154664745944835671 77934492231997118917253507)
          ·
            refine ⟨116901738347995678375880261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77934492231997118917253507 116901738347995678375880261)
            ·
              refine ⟨21919075940249189695477549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116901738347995678375880261 21919075940249189695477549)
              ·
                refine ⟨8219653477593446135804081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21919075940249189695477549 8219653477593446135804081)
                ·
                  refine ⟨6164740108195084601853061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8219653477593446135804081 6164740108195084601853061)
                  ·
                    refine ⟨1155888770286578362847449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6164740108195084601853061 1155888770286578362847449)
                    ·
                      rfl

theorem cell23_6753256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_6753256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753256 prefixEnd_6753256 := by exact prefixLift 6753256
  have htrace : WordTrace (prefixWord ++ tailWord_6753256) baseStart_6753256 baseEnd_6753256 := by
    simpa [prefixWord, tailWord_6753256, baseEnd_6753256] using wordTrace_append hprefix tailTrace_6753256
  have hstable : (prefixWord ++ tailWord_6753256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753256).length < 2 ^ (prefixWord ++ tailWord_6753256).sum := by decide
  have hdescent : baseEnd_6753256 < baseStart_6753256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753263 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 3, 2, 2]
def baseStart_6753263 : Nat := 118140960795 + 6753263 * 2 ^ 59
def prefixEnd_6753263 : Nat := 4983230072969 + 3 ^ 40 * 6753263 * 2
def baseEnd_6753263 : Nat := 3467669905224316561154815

theorem tailTrace_6753263 : CollatzResearch.WordTrace tailWord_6753263 prefixEnd_6753263 3467669905224316561154815 := by
  unfold tailWord_6753263
  simp only [CollatzResearch.WordTrace]
  refine ⟨246311736933088991341392443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164207824622059327560928295 246311736933088991341392443)
  ·
    refine ⟨369467605399633487012088665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246311736933088991341392443 369467605399633487012088665)
    ·
      refine ⟨277100704049725115259066499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369467605399633487012088665 277100704049725115259066499)
      ·
        refine ⟨415651056074587672888599749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277100704049725115259066499 415651056074587672888599749)
        ·
          refine ⟨77934573013985188666612453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 415651056074587672888599749 77934573013985188666612453)
          ·
            refine ⟨14612732440122222874989835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77934573013985188666612453 14612732440122222874989835)
            ·
              refine ⟨21919098660183334312484753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14612732440122222874989835 21919098660183334312484753)
              ·
                refine ⟨16439323995137500734363565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21919098660183334312484753 16439323995137500734363565)
                ·
                  refine ⟨6164746498176562775386337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16439323995137500734363565 6164746498176562775386337)
                  ·
                    refine ⟨4623559873632422081539753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6164746498176562775386337 4623559873632422081539753)
                    ·
                      refine ⟨3467669905224316561154815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623559873632422081539753 3467669905224316561154815)
                      ·
                        rfl

theorem cell23_6753263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 2, 2].length) (baseStart_6753263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753263 prefixEnd_6753263 := by exact prefixLift 6753263
  have htrace : WordTrace (prefixWord ++ tailWord_6753263) baseStart_6753263 baseEnd_6753263 := by
    simpa [prefixWord, tailWord_6753263, baseEnd_6753263] using wordTrace_append hprefix tailTrace_6753263
  have hstable : (prefixWord ++ tailWord_6753263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753263).length < 2 ^ (prefixWord ++ tailWord_6753263).sum := by decide
  have hdescent : baseEnd_6753263 < baseStart_6753263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753313 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_6753313 : Nat := 118140960795 + 6753313 * 2 ^ 59
def prefixEnd_6753313 : Nat := 4983230072969 + 3 ^ 40 * 6753313 * 2
def baseEnd_6753313 : Nat := 3467695579257041365529585

theorem tailTrace_6753313 : CollatzResearch.WordTrace tailWord_6753313 prefixEnd_6753313 3467695579257041365529585 := by
  unfold tailWord_6753313
  simp only [CollatzResearch.WordTrace]
  refine ⟨246313560582907849880712593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164209040388605233253808395 246313560582907849880712593)
  ·
    refine ⟨184735170437180887410534445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246313560582907849880712593 184735170437180887410534445)
    ·
      refine ⟨69275688913942832778950417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184735170437180887410534445 69275688913942832778950417)
      ·
        refine ⟨51956766685457124584212813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69275688913942832778950417 51956766685457124584212813)
        ·
          refine ⟨19483787507046421719079805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51956766685457124584212813 19483787507046421719079805)
          ·
            refine ⟨7306420315142408144654927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19483787507046421719079805 7306420315142408144654927)
            ·
              refine ⟨10959630472713612216982391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7306420315142408144654927 10959630472713612216982391)
              ·
                refine ⟨16439445709070418325473587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10959630472713612216982391 16439445709070418325473587)
                ·
                  refine ⟨24659168563605627488210381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16439445709070418325473587 24659168563605627488210381)
                  ·
                    refine ⟨9247188211352110308078893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24659168563605627488210381 9247188211352110308078893)
                    ·
                      refine ⟨3467695579257041365529585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9247188211352110308078893 3467695579257041365529585)
                      ·
                        rfl

theorem cell23_6753313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_6753313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753313 prefixEnd_6753313 := by exact prefixLift 6753313
  have htrace : WordTrace (prefixWord ++ tailWord_6753313) baseStart_6753313 baseEnd_6753313 := by
    simpa [prefixWord, tailWord_6753313, baseEnd_6753313] using wordTrace_append hprefix tailTrace_6753313
  have hstable : (prefixWord ++ tailWord_6753313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753313).length < 2 ^ (prefixWord ++ tailWord_6753313).sum := by decide
  have hdescent : baseEnd_6753313 < baseStart_6753313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753323 : List Nat := [1, 1, 1, 1, 2, 1, 8, 2, 1, 3, 2]
def baseStart_6753323 : Nat := 118140960795 + 6753323 * 2 ^ 59
def prefixEnd_6753323 : Nat := 4983230072969 + 3 ^ 40 * 6753323 * 2
def baseEnd_6753323 : Nat := 3467700714063586326404539

theorem tailTrace_6753323 : CollatzResearch.WordTrace tailWord_6753323 prefixEnd_6753323 3467700714063586326404539 := by
  unfold tailWord_6753323
  simp only [CollatzResearch.WordTrace]
  refine ⟨246313925312871621588576623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164209283541914414392384415 246313925312871621588576623)
  ·
    refine ⟨369470887969307432382864935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246313925312871621588576623 369470887969307432382864935)
    ·
      refine ⟨554206331953961148574297403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369470887969307432382864935 554206331953961148574297403)
      ·
        refine ⟨831309497930941722861446105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554206331953961148574297403 831309497930941722861446105)
        ·
          refine ⟨623482123448206292146084579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831309497930941722861446105 623482123448206292146084579)
          ·
            refine ⟨935223185172309438219126869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623482123448206292146084579 935223185172309438219126869)
            ·
              refine ⟨10959646701238001229130393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 935223185172309438219126869 10959646701238001229130393)
              ·
                refine ⟨8219735025928500921847795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10959646701238001229130393 8219735025928500921847795)
                ·
                  refine ⟨12329602538892751382771693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8219735025928500921847795 12329602538892751382771693)
                  ·
                    refine ⟨4623600952084781768539385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12329602538892751382771693 4623600952084781768539385)
                    ·
                      refine ⟨3467700714063586326404539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623600952084781768539385 3467700714063586326404539)
                      ·
                        rfl

theorem cell23_6753323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 3, 2].length) (baseStart_6753323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753323 prefixEnd_6753323 := by exact prefixLift 6753323
  have htrace : WordTrace (prefixWord ++ tailWord_6753323) baseStart_6753323 baseEnd_6753323 := by
    simpa [prefixWord, tailWord_6753323, baseEnd_6753323] using wordTrace_append hprefix tailTrace_6753323
  have hstable : (prefixWord ++ tailWord_6753323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753323).length < 2 ^ (prefixWord ++ tailWord_6753323).sum := by decide
  have hdescent : baseEnd_6753323 < baseStart_6753323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753349 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_6753349 : Nat := 118140960795 + 6753349 * 2 ^ 59
def prefixEnd_6753349 : Nat := 4983230072969 + 3 ^ 40 * 6753349 * 2
def baseEnd_6753349 : Nat := 3467714064560603224679419

theorem tailTrace_6753349 : CollatzResearch.WordTrace tailWord_6753349 prefixEnd_6753349 3467714064560603224679419 := by
  unfold tailWord_6753349
  simp only [CollatzResearch.WordTrace]
  refine ⟨246314873610777428029023101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164209915740518285352682067 246314873610777428029023101)
  ·
    refine ⟨92368077604041535510883663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246314873610777428029023101 92368077604041535510883663)
    ·
      refine ⟨138552116406062303266325495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92368077604041535510883663 138552116406062303266325495)
      ·
        refine ⟨207828174609093454899488243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138552116406062303266325495 207828174609093454899488243)
        ·
          refine ⟨311742261913640182349232365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207828174609093454899488243 311742261913640182349232365)
          ·
            refine ⟨116903348217615068380962137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311742261913640182349232365 116903348217615068380962137)
            ·
              refine ⟨87677511163211301285721603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116903348217615068380962137 87677511163211301285721603)
              ·
                refine ⟨131516266744816951928582405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87677511163211301285721603 131516266744816951928582405)
                ·
                  refine ⟨24659300014653178486609201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131516266744816951928582405 24659300014653178486609201)
                  ·
                    refine ⟨18494475010989883864956901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24659300014653178486609201 18494475010989883864956901)
                    ·
                      refine ⟨3467714064560603224679419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18494475010989883864956901 3467714064560603224679419)
                      ·
                        rfl

theorem cell23_6753349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_6753349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753349 prefixEnd_6753349 := by exact prefixLift 6753349
  have htrace : WordTrace (prefixWord ++ tailWord_6753349) baseStart_6753349 baseEnd_6753349 := by
    simpa [prefixWord, tailWord_6753349, baseEnd_6753349] using wordTrace_append hprefix tailTrace_6753349
  have hstable : (prefixWord ++ tailWord_6753349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753349).length < 2 ^ (prefixWord ++ tailWord_6753349).sum := by decide
  have hdescent : baseEnd_6753349 < baseStart_6753349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753374 : List Nat := [4, 4, 1, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_6753374 : Nat := 118140960795 + 6753374 * 2 ^ 59
def prefixEnd_6753374 : Nat := 4983230072969 + 3 ^ 40 * 6753374 * 2
def baseEnd_6753374 : Nat := 3467726901576965626866805

theorem tailTrace_6753374 : CollatzResearch.WordTrace tailWord_6753374 prefixEnd_6753374 3467726901576965626866805 := by
  unfold tailWord_6753374
  simp only [CollatzResearch.WordTrace]
  refine ⟨30789473179460857162335397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164210523623791238199122117 30789473179460857162335397)
  ·
    refine ⟨5773026221148910717937887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30789473179460857162335397 5773026221148910717937887)
    ·
      refine ⟨8659539331723366076906831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5773026221148910717937887 8659539331723366076906831)
      ·
        refine ⟨12989308997585049115360247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8659539331723366076906831 12989308997585049115360247)
        ·
          refine ⟨19483963496377573673040371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12989308997585049115360247 19483963496377573673040371)
          ·
            refine ⟨29225945244566360509560557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19483963496377573673040371 29225945244566360509560557)
            ·
              refine ⟨10959729466712385191085209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29225945244566360509560557 10959729466712385191085209)
              ·
                refine ⟨8219797100034288893313907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10959729466712385191085209 8219797100034288893313907)
                ·
                  refine ⟨12329695650051433339970861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8219797100034288893313907 12329695650051433339970861)
                  ·
                    refine ⟨4623635868769287502489073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12329695650051433339970861 4623635868769287502489073)
                    ·
                      refine ⟨3467726901576965626866805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623635868769287502489073 3467726901576965626866805)
                      ·
                        rfl

theorem cell23_6753374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_6753374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753374 prefixEnd_6753374 := by exact prefixLift 6753374
  have htrace : WordTrace (prefixWord ++ tailWord_6753374) baseStart_6753374 baseEnd_6753374 := by
    simpa [prefixWord, tailWord_6753374, baseEnd_6753374] using wordTrace_append hprefix tailTrace_6753374
  have hstable : (prefixWord ++ tailWord_6753374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753374).length < 2 ^ (prefixWord ++ tailWord_6753374).sum := by decide
  have hdescent : baseEnd_6753374 < baseStart_6753374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753399 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_6753399 : Nat := 118140960795 + 6753399 * 2 ^ 59
def prefixEnd_6753399 : Nat := 4983230072969 + 3 ^ 40 * 6753399 * 2
def baseEnd_6753399 : Nat := 3467739738593328029054189

theorem tailTrace_6753399 : CollatzResearch.WordTrace tailWord_6753399 prefixEnd_6753399 3467739738593328029054189 := by
  unfold tailWord_6753399
  simp only [CollatzResearch.WordTrace]
  refine ⟨246316697260596286568343251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164211131507064191045562167 246316697260596286568343251)
  ·
    refine ⟨369475045890894429852514877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246316697260596286568343251 369475045890894429852514877)
    ·
      refine ⟨138553142209085411194693079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369475045890894429852514877 138553142209085411194693079)
      ·
        refine ⟨207829713313628116792039619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138553142209085411194693079 207829713313628116792039619)
        ·
          refine ⟨311744569970442175188059429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207829713313628116792039619 311744569970442175188059429)
          ·
            refine ⟨58452106869457907847761143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311744569970442175188059429 58452106869457907847761143)
            ·
              refine ⟨87678160304186861771641715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58452106869457907847761143 87678160304186861771641715)
              ·
                refine ⟨131517240456280292657462573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87678160304186861771641715 131517240456280292657462573)
                ·
                  refine ⟨49318965171105109746548465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131517240456280292657462573 49318965171105109746548465)
                  ·
                    refine ⟨36989223878328832309911349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49318965171105109746548465 36989223878328832309911349)
                    ·
                      refine ⟨3467739738593328029054189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36989223878328832309911349 3467739738593328029054189)
                      ·
                        rfl

theorem cell23_6753399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_6753399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753399 prefixEnd_6753399 := by exact prefixLift 6753399
  have htrace : WordTrace (prefixWord ++ tailWord_6753399) baseStart_6753399 baseEnd_6753399 := by
    simpa [prefixWord, tailWord_6753399, baseEnd_6753399] using wordTrace_append hprefix tailTrace_6753399
  have hstable : (prefixWord ++ tailWord_6753399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753399).length < 2 ^ (prefixWord ++ tailWord_6753399).sum := by decide
  have hdescent : baseEnd_6753399 < baseStart_6753399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753470 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_6753470 : Nat := 118140960795 + 6753470 * 2 ^ 59
def prefixEnd_6753470 : Nat := 4983230072969 + 3 ^ 40 * 6753470 * 2
def baseEnd_6753470 : Nat := 1155925398573265750422121

theorem tailTrace_6753470 : CollatzResearch.WordTrace tailWord_6753470 prefixEnd_6753470 1155925398573265750422121 := by
  unfold tailWord_6753470
  simp only [CollatzResearch.WordTrace]
  refine ⟨30789910855417383211772233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164212857895559377129451909 30789910855417383211772233)
  ·
    refine ⟨23092433141563037408829175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30789910855417383211772233 23092433141563037408829175)
    ·
      refine ⟨34638649712344556113243763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23092433141563037408829175 34638649712344556113243763)
      ·
        refine ⟨51957974568516834169865645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34638649712344556113243763 51957974568516834169865645)
        ·
          refine ⟨19484240463193812813699617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51957974568516834169865645 19484240463193812813699617)
          ·
            refine ⟨14613180347395359610274713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19484240463193812813699617 14613180347395359610274713)
            ·
              refine ⟨10959885260546519707706035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14613180347395359610274713 10959885260546519707706035)
              ·
                refine ⟨16439827890819779561559053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10959885260546519707706035 16439827890819779561559053)
                ·
                  refine ⟨6164935459057417335584645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16439827890819779561559053 6164935459057417335584645)
                  ·
                    refine ⟨1155925398573265750422121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6164935459057417335584645 1155925398573265750422121)
                    ·
                      rfl

theorem cell23_6753470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_6753470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753470 prefixEnd_6753470 := by exact prefixLift 6753470
  have htrace : WordTrace (prefixWord ++ tailWord_6753470) baseStart_6753470 baseEnd_6753470 := by
    simpa [prefixWord, tailWord_6753470, baseEnd_6753470] using wordTrace_append hprefix tailTrace_6753470
  have hstable : (prefixWord ++ tailWord_6753470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753470).length < 2 ^ (prefixWord ++ tailWord_6753470).sum := by decide
  have hdescent : baseEnd_6753470 < baseStart_6753470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753503 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 1, 5, 2]
def baseStart_6753503 : Nat := 118140960795 + 6753503 * 2 ^ 59
def prefixEnd_6753503 : Nat := 4983230072969 + 3 ^ 40 * 6753503 * 2
def baseEnd_6753503 : Nat := 3467793140581395622153711

theorem tailTrace_6753503 : CollatzResearch.WordTrace tailWord_6753503 prefixEnd_6753503 3467793140581395622153711 := by
  unfold tailWord_6753503
  simp only [CollatzResearch.WordTrace]
  refine ⟨246320490452219512330129163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164213660301479674886752775 246320490452219512330129163)
  ·
    refine ⟨369480735678329268495193745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246320490452219512330129163 369480735678329268495193745)
    ·
      refine ⟨277110551758746951371395309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369480735678329268495193745 277110551758746951371395309)
      ·
        refine ⟨103916456909530106764273241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277110551758746951371395309 103916456909530106764273241)
        ·
          refine ⟨77937342682147580073204931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103916456909530106764273241 77937342682147580073204931)
          ·
            refine ⟨116906014023221370109807397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77937342682147580073204931 116906014023221370109807397)
            ·
              refine ⟨21919877629354006895588887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116906014023221370109807397 21919877629354006895588887)
              ·
                refine ⟨32879816444031010343383331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21919877629354006895588887 32879816444031010343383331)
                ·
                  refine ⟨49319724666046515515074997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32879816444031010343383331 49319724666046515515074997)
                  ·
                    refine ⟨4623724187441860829538281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49319724666046515515074997 4623724187441860829538281)
                    ·
                      refine ⟨3467793140581395622153711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623724187441860829538281 3467793140581395622153711)
                      ·
                        rfl

theorem cell23_6753503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_6753503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753503 prefixEnd_6753503 := by exact prefixLift 6753503
  have htrace : WordTrace (prefixWord ++ tailWord_6753503) baseStart_6753503 baseEnd_6753503 := by
    simpa [prefixWord, tailWord_6753503, baseEnd_6753503] using wordTrace_append hprefix tailTrace_6753503
  have hstable : (prefixWord ++ tailWord_6753503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753503).length < 2 ^ (prefixWord ++ tailWord_6753503).sum := by decide
  have hdescent : baseEnd_6753503 < baseStart_6753503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753536 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 3]
def baseStart_6753536 : Nat := 118140960795 + 6753536 * 2 ^ 59
def prefixEnd_6753536 : Nat := 4983230072969 + 3 ^ 40 * 6753536 * 2
def baseEnd_6753536 : Nat := 3467810085442993993041059

theorem tailTrace_6753536 : CollatzResearch.WordTrace tailWord_6753536 prefixEnd_6753536 3467810085442993993041059 := by
  unfold tailWord_6753536
  simp only [CollatzResearch.WordTrace]
  refine ⟨123160847030549979483040231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164214462707399972644053641 123160847030549979483040231)
  ·
    refine ⟨184741270545824969224560347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123160847030549979483040231 184741270545824969224560347)
    ·
      refine ⟨277111905818737453836840521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184741270545824969224560347 277111905818737453836840521)
      ·
        refine ⟨207833929364053090377630391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277111905818737453836840521 207833929364053090377630391)
        ·
          refine ⟨311750894046079635566445587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207833929364053090377630391 311750894046079635566445587)
          ·
            refine ⟨467626341069119453349668381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311750894046079635566445587 467626341069119453349668381)
            ·
              refine ⟨175359877900919795006125643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 467626341069119453349668381 175359877900919795006125643)
              ·
                refine ⟨263039816851379692509188465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175359877900919795006125643 263039816851379692509188465)
                ·
                  refine ⟨197279862638534769381891349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263039816851379692509188465 197279862638534769381891349)
                  ·
                    refine ⟨9247493561181317314776157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 197279862638534769381891349 9247493561181317314776157)
                    ·
                      refine ⟨3467810085442993993041059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9247493561181317314776157 3467810085442993993041059)
                      ·
                        rfl

theorem cell23_6753536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_6753536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753536 prefixEnd_6753536 := by exact prefixLift 6753536
  have htrace : WordTrace (prefixWord ++ tailWord_6753536) baseStart_6753536 baseEnd_6753536 := by
    simpa [prefixWord, tailWord_6753536, baseEnd_6753536] using wordTrace_append hprefix tailTrace_6753536
  have hstable : (prefixWord ++ tailWord_6753536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753536).length < 2 ^ (prefixWord ++ tailWord_6753536).sum := by decide
  have hdescent : baseEnd_6753536 < baseStart_6753536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753550 : List Nat := [4, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_6753550 : Nat := 118140960795 + 6753550 * 2 ^ 59
def prefixEnd_6753550 : Nat := 4983230072969 + 3 ^ 40 * 6753550 * 2
def baseEnd_6753550 : Nat := 3467817274172156938265995

theorem tailTrace_6753550 : CollatzResearch.WordTrace tailWord_6753550 prefixEnd_6753550 3467817274172156938265995 := by
  unfold tailWord_6753550
  simp only [CollatzResearch.WordTrace]
  refine ⟨30790275585381154919636263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164214803122032826238060069 30790275585381154919636263)
  ·
    refine ⟨46185413378071732379454395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30790275585381154919636263 46185413378071732379454395)
    ·
      refine ⟨69278120067107598569181593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46185413378071732379454395 69278120067107598569181593)
      ·
        refine ⟨51958590050330698926886195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69278120067107598569181593 51958590050330698926886195)
        ·
          refine ⟨77937885075496048390329293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51958590050330698926886195 77937885075496048390329293)
          ·
            refine ⟨29226706903311018146373485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77937885075496048390329293 29226706903311018146373485)
            ·
              refine ⟨10960015088741631804890057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29226706903311018146373485 10960015088741631804890057)
              ·
                refine ⟨8220011316556223853667543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10960015088741631804890057 8220011316556223853667543)
                ·
                  refine ⟨12330016974834335780501315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8220011316556223853667543 12330016974834335780501315)
                  ·
                    refine ⟨18495025462251503670751973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12330016974834335780501315 18495025462251503670751973)
                    ·
                      refine ⟨3467817274172156938265995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18495025462251503670751973 3467817274172156938265995)
                      ·
                        rfl

theorem cell23_6753550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_6753550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753550 prefixEnd_6753550 := by exact prefixLift 6753550
  have htrace : WordTrace (prefixWord ++ tailWord_6753550) baseStart_6753550 baseEnd_6753550 := by
    simpa [prefixWord, tailWord_6753550, baseEnd_6753550] using wordTrace_append hprefix tailTrace_6753550
  have hstable : (prefixWord ++ tailWord_6753550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753550).length < 2 ^ (prefixWord ++ tailWord_6753550).sum := by decide
  have hdescent : baseEnd_6753550 < baseStart_6753550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753553 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 3]
def baseStart_6753553 : Nat := 118140960795 + 6753553 * 2 ^ 59
def prefixEnd_6753553 : Nat := 4983230072969 + 3 ^ 40 * 6753553 * 2
def baseEnd_6753553 : Nat := 3467818814614120426528481

theorem tailTrace_6753553 : CollatzResearch.WordTrace tailWord_6753553 prefixEnd_6753553 3467818814614120426528481 := by
  unfold tailWord_6753553
  simp only [CollatzResearch.WordTrace]
  refine ⟨246322314102038370869449313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164214876068025580579632875 246322314102038370869449313)
  ·
    refine ⟨184741735576528778152086985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246322314102038370869449313 184741735576528778152086985)
    ·
      refine ⟨138556301682396583614065239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184741735576528778152086985 138556301682396583614065239)
      ·
        refine ⟨207834452523594875421097859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138556301682396583614065239 207834452523594875421097859)
        ·
          refine ⟨311751678785392313131646789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207834452523594875421097859 311751678785392313131646789)
          ·
            refine ⟨58453439772261058712183773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311751678785392313131646789 58453439772261058712183773)
            ·
              refine ⟨21920039914597897017068915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58453439772261058712183773 21920039914597897017068915)
              ·
                refine ⟨32880059871896845525603373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21920039914597897017068915 32880059871896845525603373)
                ·
                  refine ⟨12330022451961317072101265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32880059871896845525603373 12330022451961317072101265)
                  ·
                    refine ⟨9247516838970987804075949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12330022451961317072101265 9247516838970987804075949)
                    ·
                      refine ⟨3467818814614120426528481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9247516838970987804075949 3467818814614120426528481)
                      ·
                        rfl

theorem cell23_6753553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_6753553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753553 prefixEnd_6753553 := by exact prefixLift 6753553
  have htrace : WordTrace (prefixWord ++ tailWord_6753553) baseStart_6753553 baseEnd_6753553 := by
    simpa [prefixWord, tailWord_6753553, baseEnd_6753553] using wordTrace_append hprefix tailTrace_6753553
  have hstable : (prefixWord ++ tailWord_6753553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753553).length < 2 ^ (prefixWord ++ tailWord_6753553).sum := by decide
  have hdescent : baseEnd_6753553 < baseStart_6753553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753567 : List Nat := [1, 1, 2, 4, 4, 1, 3, 1, 1, 1, 4]
def baseStart_6753567 : Nat := 118140960795 + 6753567 * 2 ^ 59
def prefixEnd_6753567 : Nat := 4983230072969 + 3 ^ 40 * 6753567 * 2
def baseEnd_6753567 : Nat := 3467826003343283371753417

theorem tailTrace_6753567 : CollatzResearch.WordTrace tailWord_6753567 prefixEnd_6753567 3467826003343283371753417 := by
  unfold tailWord_6753567
  simp only [CollatzResearch.WordTrace]
  refine ⟨246322824723987651260458955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164215216482658434173639303 246322824723987651260458955)
  ·
    refine ⟨369484237085981476890688433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246322824723987651260458955 369484237085981476890688433)
    ·
      refine ⟨277113177814486107668016325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369484237085981476890688433 277113177814486107668016325)
      ·
        refine ⟨51958720840216145187753061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277113177814486107668016325 51958720840216145187753061)
        ·
          refine ⟨9742260157540527222703699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51958720840216145187753061 9742260157540527222703699)
          ·
            refine ⟨14613390236310790834055549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9742260157540527222703699 14613390236310790834055549)
            ·
              refine ⟨5480021338616546562770831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14613390236310790834055549 5480021338616546562770831)
              ·
                refine ⟨8220032007924819844156247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5480021338616546562770831 8220032007924819844156247)
                ·
                  refine ⟨12330048011887229766234371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8220032007924819844156247 12330048011887229766234371)
                  ·
                    refine ⟨18495072017830844649351557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12330048011887229766234371 18495072017830844649351557)
                    ·
                      refine ⟨3467826003343283371753417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18495072017830844649351557 3467826003343283371753417)
                      ·
                        rfl

theorem cell23_6753567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_6753567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753567 prefixEnd_6753567 := by exact prefixLift 6753567
  have htrace : WordTrace (prefixWord ++ tailWord_6753567) baseStart_6753567 baseEnd_6753567 := by
    simpa [prefixWord, tailWord_6753567, baseEnd_6753567] using wordTrace_append hprefix tailTrace_6753567
  have hstable : (prefixWord ++ tailWord_6753567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753567).length < 2 ^ (prefixWord ++ tailWord_6753567).sum := by decide
  have hdescent : baseEnd_6753567 < baseStart_6753567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753597 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6753597 : Nat := 118140960795 + 6753597 * 2 ^ 59
def prefixEnd_6753597 : Nat := 4983230072969 + 3 ^ 40 * 6753597 * 2
def baseEnd_6753597 : Nat := 3467841407762918254378279

theorem tailTrace_6753597 : CollatzResearch.WordTrace tailWord_6753597 prefixEnd_6753597 3467841407762918254378279 := by
  unfold tailWord_6753597
  simp only [CollatzResearch.WordTrace]
  refine ⟨246323918913878966384051045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164215945942585977589367363 246323918913878966384051045)
  ·
    refine ⟨46185734796352306197009571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246323918913878966384051045 46185734796352306197009571)
    ·
      refine ⟨69278602194528459295514357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46185734796352306197009571 69278602194528459295514357)
      ·
        refine ⟨6494868955737043058954471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69278602194528459295514357 6494868955737043058954471)
        ·
          refine ⟨9742303433605564588431707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6494868955737043058954471 9742303433605564588431707)
          ·
            refine ⟨14613455150408346882647561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9742303433605564588431707 14613455150408346882647561)
            ·
              refine ⟨10960091362806260161985671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14613455150408346882647561 10960091362806260161985671)
              ·
                refine ⟨16440137044209390242978507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10960091362806260161985671 16440137044209390242978507)
                ·
                  refine ⟨24660205566314085364467761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16440137044209390242978507 24660205566314085364467761)
                  ·
                    refine ⟨18495154174735564023350821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24660205566314085364467761 18495154174735564023350821)
                    ·
                      refine ⟨3467841407762918254378279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18495154174735564023350821 3467841407762918254378279)
                      ·
                        rfl

theorem cell23_6753597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6753597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753597 prefixEnd_6753597 := by exact prefixLift 6753597
  have htrace : WordTrace (prefixWord ++ tailWord_6753597) baseStart_6753597 baseEnd_6753597 := by
    simpa [prefixWord, tailWord_6753597, baseEnd_6753597] using wordTrace_append hprefix tailTrace_6753597
  have hstable : (prefixWord ++ tailWord_6753597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753597).length < 2 ^ (prefixWord ++ tailWord_6753597).sum := by decide
  have hdescent : baseEnd_6753597 < baseStart_6753597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753600 : List Nat := [2, 1, 1, 2, 2, 1, 3, 5, 2, 1, 3]
def baseStart_6753600 : Nat := 118140960795 + 6753600 * 2 ^ 59
def prefixEnd_6753600 : Nat := 4983230072969 + 3 ^ 40 * 6753600 * 2
def baseEnd_6753600 : Nat := 3467842948204881742640765

theorem tailTrace_6753600 : CollatzResearch.WordTrace tailWord_6753600 prefixEnd_6753600 3467842948204881742640765 := by
  unfold tailWord_6753600
  simp only [CollatzResearch.WordTrace]
  refine ⟨123162014166434048948205127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164216018888578731930940169 123162014166434048948205127)
  ·
    refine ⟨184743021249651073422307691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123162014166434048948205127 184743021249651073422307691)
    ·
      refine ⟨277114531874476610133461537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184743021249651073422307691 277114531874476610133461537)
      ·
        refine ⟨207835898905857457600096153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277114531874476610133461537 207835898905857457600096153)
        ·
          refine ⟨155876924179393093200072115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207835898905857457600096153 155876924179393093200072115)
          ·
            refine ⟨233815386269089639800108173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155876924179393093200072115 233815386269089639800108173)
            ·
              refine ⟨87680769850908614925040565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233815386269089639800108173 87680769850908614925040565)
              ·
                refine ⟨8220072173522682649222553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87680769850908614925040565 8220072173522682649222553)
                ·
                  refine ⟨6165054130142011986916915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8220072173522682649222553 6165054130142011986916915)
                  ·
                    refine ⟨9247581195213017980375373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6165054130142011986916915 9247581195213017980375373)
                    ·
                      refine ⟨3467842948204881742640765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9247581195213017980375373 3467842948204881742640765)
                      ·
                        rfl

theorem cell23_6753600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_6753600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753600 prefixEnd_6753600 := by exact prefixLift 6753600
  have htrace : WordTrace (prefixWord ++ tailWord_6753600) baseStart_6753600 baseEnd_6753600 := by
    simpa [prefixWord, tailWord_6753600, baseEnd_6753600] using wordTrace_append hprefix tailTrace_6753600
  have hstable : (prefixWord ++ tailWord_6753600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753600).length < 2 ^ (prefixWord ++ tailWord_6753600).sum := by decide
  have hdescent : baseEnd_6753600 < baseStart_6753600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753616 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 1, 8]
def baseStart_6753616 : Nat := 118140960795 + 6753616 * 2 ^ 59
def prefixEnd_6753616 : Nat := 4983230072969 + 3 ^ 40 * 6753616 * 2
def baseEnd_6753616 : Nat := 1155950387965117893346897

theorem tailTrace_6753616 : CollatzResearch.WordTrace tailWord_6753616 prefixEnd_6753616 1155950387965117893346897 := by
  unfold tailWord_6753616
  simp only [CollatzResearch.WordTrace]
  refine ⟨123162305950405066314496351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164216407933873421752661801 123162305950405066314496351)
  ·
    refine ⟨184743458925607599471744527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123162305950405066314496351 184743458925607599471744527)
    ·
      refine ⟨277115188388411399207616791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184743458925607599471744527 277115188388411399207616791)
      ·
        refine ⟨415672782582617098811425187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277115188388411399207616791 415672782582617098811425187)
        ·
          refine ⟨623509173873925648217137781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415672782582617098811425187 623509173873925648217137781)
          ·
            refine ⟨58453985050680529520356667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 623509173873925648217137781 58453985050680529520356667)
            ·
              refine ⟨87680977576020794280535001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58453985050680529520356667 87680977576020794280535001)
              ·
                refine ⟨65760733182015595710401251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87680977576020794280535001 65760733182015595710401251)
                ·
                  refine ⟨98641099773023393565601877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65760733182015595710401251 98641099773023393565601877)
                  ·
                    refine ⟨1155950387965117893346897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98641099773023393565601877 1155950387965117893346897)
                    ·
                      rfl

theorem cell23_6753616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_6753616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753616 prefixEnd_6753616 := by exact prefixLift 6753616
  have htrace : WordTrace (prefixWord ++ tailWord_6753616) baseStart_6753616 baseEnd_6753616 := by
    simpa [prefixWord, tailWord_6753616, baseEnd_6753616] using wordTrace_append hprefix tailTrace_6753616
  have hstable : (prefixWord ++ tailWord_6753616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753616).length < 2 ^ (prefixWord ++ tailWord_6753616).sum := by decide
  have hdescent : baseEnd_6753616 < baseStart_6753616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753656 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_6753656 : Nat := 118140960795 + 6753656 * 2 ^ 59
def prefixEnd_6753656 : Nat := 4983230072969 + 3 ^ 40 * 6753656 * 2
def baseEnd_6753656 : Nat := 3467871703121533523540507

theorem tailTrace_6753656 : CollatzResearch.WordTrace tailWord_6753656 prefixEnd_6753656 3467871703121533523540507 := by
  unfold tailWord_6753656
  simp only [CollatzResearch.WordTrace]
  refine ⟨123163035410332609730224411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164217380547110146306965881 123163035410332609730224411)
  ·
    refine ⟨184744553115498914595336617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123163035410332609730224411 184744553115498914595336617)
    ·
      refine ⟨138558414836624185946502463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184744553115498914595336617 138558414836624185946502463)
      ·
        refine ⟨207837622254936278919753695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138558414836624185946502463 207837622254936278919753695)
        ·
          refine ⟨311756433382404418379630543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207837622254936278919753695 311756433382404418379630543)
          ·
            refine ⟨467634650073606627569445815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311756433382404418379630543 467634650073606627569445815)
            ·
              refine ⟨701451975110409941354168723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467634650073606627569445815 701451975110409941354168723)
              ·
                refine ⟨1052177962665614912031253085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701451975110409941354168723 1052177962665614912031253085)
                ·
                  refine ⟨394566735999605592011719907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052177962665614912031253085 394566735999605592011719907)
                  ·
                    refine ⟨591850103999408388017579861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 394566735999605592011719907 591850103999408388017579861)
                    ·
                      refine ⟨3467871703121533523540507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 591850103999408388017579861 3467871703121533523540507)
                      ·
                        rfl

theorem cell23_6753656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_6753656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753656 prefixEnd_6753656 := by exact prefixLift 6753656
  have htrace : WordTrace (prefixWord ++ tailWord_6753656) baseStart_6753656 baseEnd_6753656 := by
    simpa [prefixWord, tailWord_6753656, baseEnd_6753656] using wordTrace_append hprefix tailTrace_6753656
  have hstable : (prefixWord ++ tailWord_6753656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753656).length < 2 ^ (prefixWord ++ tailWord_6753656).sum := by decide
  have hdescent : baseEnd_6753656 < baseStart_6753656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753657 : List Nat := [1, 2, 1, 3, 2, 1, 2, 5, 2, 2, 2]
def baseStart_6753657 : Nat := 118140960795 + 6753657 * 2 ^ 59
def prefixEnd_6753657 : Nat := 4983230072969 + 3 ^ 40 * 6753657 * 2
def baseEnd_6753657 : Nat := 3467872216602188019628003

theorem tailTrace_6753657 : CollatzResearch.WordTrace tailWord_6753657 prefixEnd_6753657 3467872216602188019628003 := by
  unfold tailWord_6753657
  simp only [CollatzResearch.WordTrace]
  refine ⟨246326107293661596631235225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164217404862441064420823483 246326107293661596631235225)
  ·
    refine ⟨184744580470246197473426419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246326107293661596631235225 184744580470246197473426419)
    ·
      refine ⟨277116870705369296210139629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184744580470246197473426419 277116870705369296210139629)
      ·
        refine ⟨103918826514513486078802361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277116870705369296210139629 103918826514513486078802361)
        ·
          refine ⟨77939119885885114559101771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103918826514513486078802361 77939119885885114559101771)
          ·
            refine ⟨116908679828827671838652657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77939119885885114559101771 116908679828827671838652657)
            ·
              refine ⟨87681509871620753878989493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116908679828827671838652657 87681509871620753878989493)
              ·
                refine ⟨8220141550464445676155265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87681509871620753878989493 8220141550464445676155265)
                ·
                  refine ⟨6165106162848334257116449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8220141550464445676155265 6165106162848334257116449)
                  ·
                    refine ⟨4623829622136250692837337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6165106162848334257116449 4623829622136250692837337)
                    ·
                      refine ⟨3467872216602188019628003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623829622136250692837337 3467872216602188019628003)
                      ·
                        rfl

theorem cell23_6753657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_6753657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753657 prefixEnd_6753657 := by exact prefixLift 6753657
  have htrace : WordTrace (prefixWord ++ tailWord_6753657) baseStart_6753657 baseEnd_6753657 := by
    simpa [prefixWord, tailWord_6753657, baseEnd_6753657] using wordTrace_append hprefix tailTrace_6753657
  have hstable : (prefixWord ++ tailWord_6753657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753657).length < 2 ^ (prefixWord ++ tailWord_6753657).sum := by decide
  have hdescent : baseEnd_6753657 < baseStart_6753657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753700 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 2, 5, 2]
def baseStart_6753700 : Nat := 118140960795 + 6753700 * 2 ^ 59
def prefixEnd_6753700 : Nat := 4983230072969 + 3 ^ 40 * 6753700 * 2
def baseEnd_6753700 : Nat := 3467894296270331351390305

theorem tailTrace_6753700 : CollatzResearch.WordTrace tailWord_6753700 prefixEnd_6753700 3467894296270331351390305 := by
  unfold tailWord_6753700
  simp only [CollatzResearch.WordTrace]
  refine ⟨123163837816252907487525277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164218450421670543316700369 123163837816252907487525277)
  ·
    refine ⟨46186439181094840307821979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123163837816252907487525277 46186439181094840307821979)
    ·
      refine ⟨69279658771642260461732969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46186439181094840307821979 69279658771642260461732969)
      ·
        refine ⟨51959744078731695346299727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69279658771642260461732969 51959744078731695346299727)
        ·
          refine ⟨77939616118097543019449591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51959744078731695346299727 77939616118097543019449591)
          ·
            refine ⟨116909424177146314529174387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77939616118097543019449591 116909424177146314529174387)
            ·
              refine ⟨175364136265719471793761581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116909424177146314529174387 175364136265719471793761581)
              ·
                refine ⟨65761551099644801922660593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175364136265719471793761581 65761551099644801922660593)
                ·
                  refine ⟨49321163324733601441995445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65761551099644801922660593 49321163324733601441995445)
                  ·
                    refine ⟨4623859061693775135187073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49321163324733601441995445 4623859061693775135187073)
                    ·
                      refine ⟨3467894296270331351390305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4623859061693775135187073 3467894296270331351390305)
                      ·
                        rfl

theorem cell23_6753700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_6753700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753700 prefixEnd_6753700 := by exact prefixLift 6753700
  have htrace : WordTrace (prefixWord ++ tailWord_6753700) baseStart_6753700 baseEnd_6753700 := by
    simpa [prefixWord, tailWord_6753700, baseEnd_6753700] using wordTrace_append hprefix tailTrace_6753700
  have hstable : (prefixWord ++ tailWord_6753700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753700).length < 2 ^ (prefixWord ++ tailWord_6753700).sum := by decide
  have hdescent : baseEnd_6753700 < baseStart_6753700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753804 : List Nat := [2, 2, 1, 2, 6, 1, 1, 2, 6]
def baseStart_6753804 : Nat := 118140960795 + 6753804 * 2 ^ 59
def prefixEnd_6753804 : Nat := 4983230072969 + 3 ^ 40 * 6753804 * 2
def baseEnd_6753804 : Nat := 385327522028710993832203

theorem tailTrace_6753804 : CollatzResearch.WordTrace tailWord_6753804 prefixEnd_6753804 385327522028710993832203 := by
  unfold tailWord_6753804
  simp only [CollatzResearch.WordTrace]
  refine ⟨123165734412064520368418233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164220979216086027157890977 123165734412064520368418233)
  ·
    refine ⟨92374300809048390276313675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123165734412064520368418233 92374300809048390276313675)
    ·
      refine ⟨138561451213572585414470513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92374300809048390276313675 138561451213572585414470513)
      ·
        refine ⟨103921088410179439060852885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138561451213572585414470513 103921088410179439060852885)
        ·
          refine ⟨4871301019227161205977479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103921088410179439060852885 4871301019227161205977479)
          ·
            refine ⟨7306951528840741808966219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4871301019227161205977479 7306951528840741808966219)
            ·
              refine ⟨10960427293261112713449329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7306951528840741808966219 10960427293261112713449329)
              ·
                refine ⟨8220320469945834535086997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10960427293261112713449329 8220320469945834535086997)
                ·
                  refine ⟨385327522028710993832203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8220320469945834535086997 385327522028710993832203)
                  ·
                    rfl

theorem cell23_6753804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 6].length) (baseStart_6753804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753804 prefixEnd_6753804 := by exact prefixLift 6753804
  have htrace : WordTrace (prefixWord ++ tailWord_6753804) baseStart_6753804 baseEnd_6753804 := by
    simpa [prefixWord, tailWord_6753804, baseEnd_6753804] using wordTrace_append hprefix tailTrace_6753804
  have hstable : (prefixWord ++ tailWord_6753804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753804).length < 2 ^ (prefixWord ++ tailWord_6753804).sum := by decide
  have hdescent : baseEnd_6753804 < baseStart_6753804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753850 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_6753850 : Nat := 118140960795 + 6753850 * 2 ^ 59
def prefixEnd_6753850 : Nat := 4983230072969 + 3 ^ 40 * 6753850 * 2
def baseEnd_6753850 : Nat := 3467971318368505764514615

theorem tailTrace_6753850 : CollatzResearch.WordTrace tailWord_6753850 prefixEnd_6753850 3467971318368505764514615 := by
  unfold tailWord_6753850
  simp only [CollatzResearch.WordTrace]
  refine ⟨61583286645490597648252751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164222097721308260395340669 61583286645490597648252751)
  ·
    refine ⟨92374929968235896472379127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61583286645490597648252751 92374929968235896472379127)
    ·
      refine ⟨138562394952353844708568691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92374929968235896472379127 138562394952353844708568691)
      ·
        refine ⟨207843592428530767062853037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138562394952353844708568691 207843592428530767062853037)
        ·
          refine ⟨77941347160699037648569889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207843592428530767062853037 77941347160699037648569889)
          ·
            refine ⟨58456010370524278236427417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77941347160699037648569889 58456010370524278236427417)
            ·
              refine ⟨43842007777893208677320563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58456010370524278236427417 43842007777893208677320563)
              ·
                refine ⟨65763011666839813015980845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43842007777893208677320563 65763011666839813015980845)
                ·
                  refine ⟨24661129375064929880992817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65763011666839813015980845 24661129375064929880992817)
                  ·
                    refine ⟨18495847031298697410744613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24661129375064929880992817 18495847031298697410744613)
                    ·
                      refine ⟨3467971318368505764514615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18495847031298697410744613 3467971318368505764514615)
                      ·
                        rfl

theorem cell23_6753850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_6753850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753850 prefixEnd_6753850 := by exact prefixLift 6753850
  have htrace : WordTrace (prefixWord ++ tailWord_6753850) baseStart_6753850 baseEnd_6753850 := by
    simpa [prefixWord, tailWord_6753850, baseEnd_6753850] using wordTrace_append hprefix tailTrace_6753850
  have hstable : (prefixWord ++ tailWord_6753850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753850).length < 2 ^ (prefixWord ++ tailWord_6753850).sum := by decide
  have hdescent : baseEnd_6753850 < baseStart_6753850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753857 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_6753857 : Nat := 118140960795 + 6753857 * 2 ^ 59
def prefixEnd_6753857 : Nat := 4983230072969 + 3 ^ 40 * 6753857 * 2
def baseEnd_6753857 : Nat := 3467974912733087237127083

theorem tailTrace_6753857 : CollatzResearch.WordTrace tailWord_6753857 prefixEnd_6753857 3467974912733087237127083 := by
  unfold tailWord_6753857
  simp only [CollatzResearch.WordTrace]
  refine ⟨246333401892937030788515825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164222267928624687192343883 246333401892937030788515825)
  ·
    refine ⟨184750051419702773091386869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246333401892937030788515825 184750051419702773091386869)
    ·
      refine ⟨17320317320597134977317519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184750051419702773091386869 17320317320597134977317519)
      ·
        refine ⟨25980475980895702465976279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17320317320597134977317519 25980475980895702465976279)
        ·
          refine ⟨38970713971343553698964419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25980475980895702465976279 38970713971343553698964419)
          ·
            refine ⟨58456070957015330548446629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38970713971343553698964419 58456070957015330548446629)
            ·
              refine ⟨10960513304440374477833743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58456070957015330548446629 10960513304440374477833743)
              ·
                refine ⟨16440769956660561716750615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10960513304440374477833743 16440769956660561716750615)
                ·
                  refine ⟨24661154934990842575125923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16440769956660561716750615 24661154934990842575125923)
                  ·
                    refine ⟨36991732402486263862688885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24661154934990842575125923 36991732402486263862688885)
                    ·
                      refine ⟨3467974912733087237127083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36991732402486263862688885 3467974912733087237127083)
                      ·
                        rfl

theorem cell23_6753857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_6753857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753857 prefixEnd_6753857 := by exact prefixLift 6753857
  have htrace : WordTrace (prefixWord ++ tailWord_6753857) baseStart_6753857 baseEnd_6753857 := by
    simpa [prefixWord, tailWord_6753857, baseEnd_6753857] using wordTrace_append hprefix tailTrace_6753857
  have hstable : (prefixWord ++ tailWord_6753857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753857).length < 2 ^ (prefixWord ++ tailWord_6753857).sum := by decide
  have hdescent : baseEnd_6753857 < baseStart_6753857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753920 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 2, 6]
def baseStart_6753920 : Nat := 118140960795 + 6753920 * 2 ^ 59
def prefixEnd_6753920 : Nat := 4983230072969 + 3 ^ 40 * 6753920 * 2
def baseEnd_6753920 : Nat := 1156002420671440163546431

theorem tailTrace_6753920 : CollatzResearch.WordTrace tailWord_6753920 prefixEnd_6753920 1156002420671440163546431 := by
  unfold tailWord_6753920
  simp only [CollatzResearch.WordTrace]
  refine ⟨123167849845854396274029607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164223799794472528365372809 123167849845854396274029607)
  ·
    refine ⟨184751774768781594411044411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123167849845854396274029607 184751774768781594411044411)
    ·
      refine ⟨277127662153172391616566617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184751774768781594411044411 277127662153172391616566617)
      ·
        refine ⟨207845746614879293712424963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277127662153172391616566617 207845746614879293712424963)
        ·
          refine ⟨311768619922318940568637445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207845746614879293712424963 311768619922318940568637445)
          ·
            refine ⟨58456616235434801356619521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311768619922318940568637445 58456616235434801356619521)
            ·
              refine ⟨43842462176576101017464641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58456616235434801356619521 43842462176576101017464641)
              ·
                refine ⟨32881846632432075763098481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43842462176576101017464641 32881846632432075763098481)
                ·
                  refine ⟨24661384974324056822323861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32881846632432075763098481 24661384974324056822323861)
                  ·
                    refine ⟨1156002420671440163546431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24661384974324056822323861 1156002420671440163546431)
                    ·
                      rfl

theorem cell23_6753920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_6753920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753920 prefixEnd_6753920 := by exact prefixLift 6753920
  have htrace : WordTrace (prefixWord ++ tailWord_6753920) baseStart_6753920 baseEnd_6753920 := by
    simpa [prefixWord, tailWord_6753920, baseEnd_6753920] using wordTrace_append hprefix tailTrace_6753920
  have hstable : (prefixWord ++ tailWord_6753920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753920).length < 2 ^ (prefixWord ++ tailWord_6753920).sum := by decide
  have hdescent : baseEnd_6753920 < baseStart_6753920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753921 : List Nat := [1, 2, 4, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_6753921 : Nat := 118140960795 + 6753921 * 2 ^ 59
def prefixEnd_6753921 : Nat := 4983230072969 + 3 ^ 40 * 6753921 * 2
def baseEnd_6753921 : Nat := 3468007775494974986726789

theorem tailTrace_6753921 : CollatzResearch.WordTrace tailWord_6753921 prefixEnd_6753921 3468007775494974986726789 := by
  unfold tailWord_6753921
  simp only [CollatzResearch.WordTrace]
  refine ⟨246335736164705169718845617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164223824109803446479230411 246335736164705169718845617)
  ·
    refine ⟨184751802123528877289134213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246335736164705169718845617 184751802123528877289134213)
    ·
      refine ⟨34640962898161664491712665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184751802123528877289134213 34640962898161664491712665)
      ·
        refine ⟨25980722173621248368784499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34640962898161664491712665 25980722173621248368784499)
        ·
          refine ⟨38971083260431872553176749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25980722173621248368784499 38971083260431872553176749)
          ·
            refine ⟨14614156222661952207441281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38971083260431872553176749 14614156222661952207441281)
            ·
              refine ⟨10960617166996464155580961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14614156222661952207441281 10960617166996464155580961)
              ·
                refine ⟨8220462875247348116685721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10960617166996464155580961 8220462875247348116685721)
                ·
                  refine ⟨6165347156435511087514291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8220462875247348116685721 6165347156435511087514291)
                  ·
                    refine ⟨9248020734653266631271437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6165347156435511087514291 9248020734653266631271437)
                    ·
                      refine ⟨3468007775494974986726789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9248020734653266631271437 3468007775494974986726789)
                      ·
                        rfl

theorem cell23_6753921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_6753921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753921 prefixEnd_6753921 := by exact prefixLift 6753921
  have htrace : WordTrace (prefixWord ++ tailWord_6753921) baseStart_6753921 baseEnd_6753921 := by
    simpa [prefixWord, tailWord_6753921, baseEnd_6753921] using wordTrace_append hprefix tailTrace_6753921
  have hstable : (prefixWord ++ tailWord_6753921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753921).length < 2 ^ (prefixWord ++ tailWord_6753921).sum := by decide
  have hdescent : baseEnd_6753921 < baseStart_6753921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753944 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 1, 4, 2]
def baseStart_6753944 : Nat := 118140960795 + 6753944 * 2 ^ 59
def prefixEnd_6753944 : Nat := 4983230072969 + 3 ^ 40 * 6753944 * 2
def baseEnd_6753944 : Nat := 3468019585550028396739183

theorem tailTrace_6753944 : CollatzResearch.WordTrace tailWord_6753944 prefixEnd_6753944 3468019585550028396739183 := by
  unfold tailWord_6753944
  simp only [CollatzResearch.WordTrace]
  refine ⟨123168287521810922323466443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164224383362414563097955257 123168287521810922323466443)
  ·
    refine ⟨184752431282716383485199665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123168287521810922323466443 184752431282716383485199665)
    ·
      refine ⟨138564323462037287613899749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184752431282716383485199665 138564323462037287613899749)
      ·
        refine ⟨25980810649131991427606203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138564323462037287613899749 25980810649131991427606203)
        ·
          refine ⟨38971215973697987141409305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25980810649131991427606203 38971215973697987141409305)
          ·
            refine ⟨29228411980273490356056979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38971215973697987141409305 29228411980273490356056979)
            ·
              refine ⟨43842617970410235534085469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29228411980273490356056979 43842617970410235534085469)
              ·
                refine ⟨16440981738903838325282051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43842617970410235534085469 16440981738903838325282051)
                ·
                  refine ⟨24661472608355757487923077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16440981738903838325282051 24661472608355757487923077)
                  ·
                    refine ⟨4624026114066704528985577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24661472608355757487923077 4624026114066704528985577)
                    ·
                      refine ⟨3468019585550028396739183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624026114066704528985577 3468019585550028396739183)
                      ·
                        rfl

theorem cell23_6753944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_6753944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753944 prefixEnd_6753944 := by exact prefixLift 6753944
  have htrace : WordTrace (prefixWord ++ tailWord_6753944) baseStart_6753944 baseEnd_6753944 := by
    simpa [prefixWord, tailWord_6753944, baseEnd_6753944] using wordTrace_append hprefix tailTrace_6753944
  have hstable : (prefixWord ++ tailWord_6753944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753944).length < 2 ^ (prefixWord ++ tailWord_6753944).sum := by decide
  have hdescent : baseEnd_6753944 < baseStart_6753944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753977 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 2, 3, 3]
def baseStart_6753977 : Nat := 118140960795 + 6753977 * 2 ^ 59
def prefixEnd_6753977 : Nat := 4983230072969 + 3 ^ 40 * 6753977 * 2
def baseEnd_6753977 : Nat := 3468036530411626767626531

theorem tailTrace_6753977 : CollatzResearch.WordTrace tailWord_6753977 prefixEnd_6753977 3468036530411626767626531 := by
  unfold tailWord_6753977
  simp only [CollatzResearch.WordTrace]
  refine ⟨246337778652502291282884185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164225185768334860855256123 246337778652502291282884185)
  ·
    refine ⟨184753333989376718462163139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246337778652502291282884185 184753333989376718462163139)
    ·
      refine ⟨277130000984065077693244709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184753333989376718462163139 277130000984065077693244709)
      ·
        refine ⟨51961875184512202067483383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277130000984065077693244709 51961875184512202067483383)
        ·
          refine ⟨77942812776768303101225075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51961875184512202067483383 77942812776768303101225075)
          ·
            refine ⟨116914219165152454651837613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77942812776768303101225075 116914219165152454651837613)
            ·
              refine ⟨43842832186932170494439105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116914219165152454651837613 43842832186932170494439105)
              ·
                refine ⟨32882124140199127870829329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43842832186932170494439105 32882124140199127870829329)
                ·
                  refine ⟨24661593105149345903121997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32882124140199127870829329 24661593105149345903121997)
                  ·
                    refine ⟨9248097414431004713670749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24661593105149345903121997 9248097414431004713670749)
                    ·
                      refine ⟨3468036530411626767626531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9248097414431004713670749 3468036530411626767626531)
                      ·
                        rfl

theorem cell23_6753977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_6753977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753977 prefixEnd_6753977 := by exact prefixLift 6753977
  have htrace : WordTrace (prefixWord ++ tailWord_6753977) baseStart_6753977 baseEnd_6753977 := by
    simpa [prefixWord, tailWord_6753977, baseEnd_6753977] using wordTrace_append hprefix tailTrace_6753977
  have hstable : (prefixWord ++ tailWord_6753977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753977).length < 2 ^ (prefixWord ++ tailWord_6753977).sum := by decide
  have hdescent : baseEnd_6753977 < baseStart_6753977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6753978 : List Nat := [3, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2]
def baseStart_6753978 : Nat := 118140960795 + 6753978 * 2 ^ 59
def prefixEnd_6753978 : Nat := 4983230072969 + 3 ^ 40 * 6753978 * 2
def baseEnd_6753978 : Nat := 3468037043892281263714027

theorem tailTrace_6753978 : CollatzResearch.WordTrace tailWord_6753978 prefixEnd_6753978 3468037043892281263714027 := by
  unfold tailWord_6753978
  simp only [CollatzResearch.WordTrace]
  refine ⟨61584453781374667113417647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164225210083665778969113725 61584453781374667113417647)
  ·
    refine ⟨92376680672062000670126471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61584453781374667113417647 92376680672062000670126471)
    ·
      refine ⟨138565021008093001005189707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92376680672062000670126471 138565021008093001005189707)
      ·
        refine ⟨207847531512139501507784561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138565021008093001005189707 207847531512139501507784561)
        ·
          refine ⟨155885648634104626130838421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207847531512139501507784561 155885648634104626130838421)
          ·
            refine ⟨7307139779723654349883051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155885648634104626130838421 7307139779723654349883051)
            ·
              refine ⟨10960709669585481524824577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7307139779723654349883051 10960709669585481524824577)
              ·
                refine ⟨8220532252189111143618433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10960709669585481524824577 8220532252189111143618433)
                ·
                  refine ⟨6165399189141833357713825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8220532252189111143618433 6165399189141833357713825)
                  ·
                    refine ⟨4624049391856375018285369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6165399189141833357713825 4624049391856375018285369)
                    ·
                      refine ⟨3468037043892281263714027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624049391856375018285369 3468037043892281263714027)
                      ·
                        rfl

theorem cell23_6753978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2].length) (baseStart_6753978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6753978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6753978 prefixEnd_6753978 := by exact prefixLift 6753978
  have htrace : WordTrace (prefixWord ++ tailWord_6753978) baseStart_6753978 baseEnd_6753978 := by
    simpa [prefixWord, tailWord_6753978, baseEnd_6753978] using wordTrace_append hprefix tailTrace_6753978
  have hstable : (prefixWord ++ tailWord_6753978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6753978).length < 2 ^ (prefixWord ++ tailWord_6753978).sum := by decide
  have hdescent : baseEnd_6753978 < baseStart_6753978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6753978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754027 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 5, 4]
def baseStart_6754027 : Nat := 118140960795 + 6754027 * 2 ^ 59
def prefixEnd_6754027 : Nat := 4983230072969 + 3 ^ 40 * 6754027 * 2
def baseEnd_6754027 : Nat := 1156020734814783857333767

theorem tailTrace_6754027 : CollatzResearch.WordTrace tailWord_6754027 prefixEnd_6754027 1156020734814783857333767 := by
  unfold tailWord_6754027
  simp only [CollatzResearch.WordTrace]
  refine ⟨246339602302321149822204335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164226401534880766548136223 246339602302321149822204335)
  ·
    refine ⟨369509403453481724733306503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246339602302321149822204335 369509403453481724733306503)
    ·
      refine ⟨554264105180222587099959755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369509403453481724733306503 554264105180222587099959755)
      ·
        refine ⟨831396157770333880649939633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554264105180222587099959755 831396157770333880649939633)
        ·
          refine ⟨623547118327750410487454725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831396157770333880649939633 623547118327750410487454725)
          ·
            refine ⟨116915084686453201966397761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 623547118327750410487454725 116915084686453201966397761)
            ·
              refine ⟨87686313514839901474798321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116915084686453201966397761 87686313514839901474798321)
              ·
                refine ⟨65764735136129926106098741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87686313514839901474798321 65764735136129926106098741)
                ·
                  refine ⟨6165443919012180572446757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65764735136129926106098741 6165443919012180572446757)
                  ·
                    refine ⟨1156020734814783857333767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6165443919012180572446757 1156020734814783857333767)
                    ·
                      rfl

theorem cell23_6754027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 4].length) (baseStart_6754027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754027 prefixEnd_6754027 := by exact prefixLift 6754027
  have htrace : WordTrace (prefixWord ++ tailWord_6754027) baseStart_6754027 baseEnd_6754027 := by
    simpa [prefixWord, tailWord_6754027, baseEnd_6754027] using wordTrace_append hprefix tailTrace_6754027
  have hstable : (prefixWord ++ tailWord_6754027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754027).length < 2 ^ (prefixWord ++ tailWord_6754027).sum := by decide
  have hdescent : baseEnd_6754027 < baseStart_6754027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754034 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_6754034 : Nat := 118140960795 + 6754034 * 2 ^ 59
def prefixEnd_6754034 : Nat := 4983230072969 + 3 ^ 40 * 6754034 * 2
def baseEnd_6754034 : Nat := 3468065798808933044613769

theorem tailTrace_6754034 : CollatzResearch.WordTrace tailWord_6754034 prefixEnd_6754034 3468065798808933044613769 := by
  unfold tailWord_6754034
  simp only [CollatzResearch.WordTrace]
  refine ⟨61584964403323947504427289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164226571742197193345139437 61584964403323947504427289)
  ·
    refine ⟨46188723302492960628320467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61584964403323947504427289 46188723302492960628320467)
    ·
      refine ⟨69283084953739440942480701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46188723302492960628320467 69283084953739440942480701)
      ·
        refine ⟨25981156857652290353430263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69283084953739440942480701 25981156857652290353430263)
        ·
          refine ⟨38971735286478435530145395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25981156857652290353430263 38971735286478435530145395)
          ·
            refine ⟨58457602929717653295218093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38971735286478435530145395 58457602929717653295218093)
            ·
              refine ⟨21921601098644119985706785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58457602929717653295218093 21921601098644119985706785)
              ·
                refine ⟨16441200823983089989280089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21921601098644119985706785 16441200823983089989280089)
                ·
                  refine ⟨12330900617987317491960067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16441200823983089989280089 12330900617987317491960067)
                  ·
                    refine ⟨18496350926980976237940101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12330900617987317491960067 18496350926980976237940101)
                    ·
                      refine ⟨3468065798808933044613769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18496350926980976237940101 3468065798808933044613769)
                      ·
                        rfl

theorem cell23_6754034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_6754034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754034 prefixEnd_6754034 := by exact prefixLift 6754034
  have htrace : WordTrace (prefixWord ++ tailWord_6754034) baseStart_6754034 baseEnd_6754034 := by
    simpa [prefixWord, tailWord_6754034, baseEnd_6754034] using wordTrace_append hprefix tailTrace_6754034
  have hstable : (prefixWord ++ tailWord_6754034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754034).length < 2 ^ (prefixWord ++ tailWord_6754034).sum := by decide
  have hdescent : baseEnd_6754034 < baseStart_6754034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754071 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 3]
def baseStart_6754071 : Nat := 118140960795 + 6754071 * 2 ^ 59
def prefixEnd_6754071 : Nat := 4983230072969 + 3 ^ 40 * 6754071 * 2
def baseEnd_6754071 : Nat := 3468084797593149399851099

theorem tailTrace_6754071 : CollatzResearch.WordTrace tailWord_6754071 prefixEnd_6754071 3468084797593149399851099 := by
  unfold tailWord_6754071
  simp only [CollatzResearch.WordTrace]
  refine ⟨246341207114161745336806067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164227471409441163557870711 246341207114161745336806067)
  ·
    refine ⟨369511810671242618005209101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246341207114161745336806067 369511810671242618005209101)
    ·
      refine ⟨138566929001715981751953413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369511810671242618005209101 138566929001715981751953413)
      ·
        refine ⟨25981299187821746578491265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138566929001715981751953413 25981299187821746578491265)
        ·
          refine ⟨19485974390866309933868449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25981299187821746578491265 19485974390866309933868449)
          ·
            refine ⟨14614480793149732450401337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19485974390866309933868449 14614480793149732450401337)
            ·
              refine ⟨10960860594862299337801003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14614480793149732450401337 10960860594862299337801003)
              ·
                refine ⟨16441290892293449006701505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10960860594862299337801003 16441290892293449006701505)
                ·
                  refine ⟨12330968169220086755026129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16441290892293449006701505 12330968169220086755026129)
                  ·
                    refine ⟨9248226126915065066269597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12330968169220086755026129 9248226126915065066269597)
                    ·
                      refine ⟨3468084797593149399851099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9248226126915065066269597 3468084797593149399851099)
                      ·
                        rfl

theorem cell23_6754071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_6754071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754071 prefixEnd_6754071 := by exact prefixLift 6754071
  have htrace : WordTrace (prefixWord ++ tailWord_6754071) baseStart_6754071 baseEnd_6754071 := by
    simpa [prefixWord, tailWord_6754071, baseEnd_6754071] using wordTrace_append hprefix tailTrace_6754071
  have hstable : (prefixWord ++ tailWord_6754071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754071).length < 2 ^ (prefixWord ++ tailWord_6754071).sum := by decide
  have hdescent : baseEnd_6754071 < baseStart_6754071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754135 : List Nat := [1, 1, 3, 2, 5, 1, 2, 3, 1, 1, 3]
def baseStart_6754135 : Nat := 118140960795 + 6754135 * 2 ^ 59
def prefixEnd_6754135 : Nat := 4983230072969 + 3 ^ 40 * 6754135 * 2
def baseEnd_6754135 : Nat := 3468117660355037149450805

theorem tailTrace_6754135 : CollatzResearch.WordTrace tailWord_6754135 prefixEnd_6754135 3468117660355037149450805 := by
  unfold tailWord_6754135
  simp only [CollatzResearch.WordTrace]
  refine ⟨246343541385929884267135859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164229027590619922844757239 246343541385929884267135859)
  ·
    refine ⟨369515312078894826400703789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246343541385929884267135859 369515312078894826400703789)
    ·
      refine ⟨138568242029585559900263921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369515312078894826400703789 138568242029585559900263921)
      ·
        refine ⟨103926181522189169925197941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138568242029585559900263921 103926181522189169925197941)
        ·
          refine ⟨9743079517705234680487307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103926181522189169925197941 9743079517705234680487307)
          ·
            refine ⟨14614619276557852020730961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9743079517705234680487307 14614619276557852020730961)
            ·
              refine ⟨10960964457418389015548221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14614619276557852020730961 10960964457418389015548221)
              ·
                refine ⟨4110361671531895880830583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10960964457418389015548221 4110361671531895880830583)
                ·
                  refine ⟨6165542507297843821245875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110361671531895880830583 6165542507297843821245875)
                  ·
                    refine ⟨9248313760946765731868813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6165542507297843821245875 9248313760946765731868813)
                    ·
                      refine ⟨3468117660355037149450805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9248313760946765731868813 3468117660355037149450805)
                      ·
                        rfl

theorem cell23_6754135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_6754135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754135 prefixEnd_6754135 := by exact prefixLift 6754135
  have htrace : WordTrace (prefixWord ++ tailWord_6754135) baseStart_6754135 baseEnd_6754135 := by
    simpa [prefixWord, tailWord_6754135, baseEnd_6754135] using wordTrace_append hprefix tailTrace_6754135
  have hstable : (prefixWord ++ tailWord_6754135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754135).length < 2 ^ (prefixWord ++ tailWord_6754135).sum := by decide
  have hdescent : baseEnd_6754135 < baseStart_6754135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754209 : List Nat := [1, 2, 3, 4, 2, 1, 3, 2, 1, 2, 2]
def baseStart_6754209 : Nat := 118140960795 + 6754209 * 2 ^ 59
def prefixEnd_6754209 : Nat := 4983230072969 + 3 ^ 40 * 6754209 * 2
def baseEnd_6754209 : Nat := 3468155657923469859925465

theorem tailTrace_6754209 : CollatzResearch.WordTrace tailWord_6754209 prefixEnd_6754209 3468155657923469859925465 := by
  unfold tailWord_6754209
  simp only [CollatzResearch.WordTrace]
  refine ⟨246346240387661794905329681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164230826925107863270219787 246346240387661794905329681)
  ·
    refine ⟨184759680290746346178997261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246346240387661794905329681 184759680290746346178997261)
    ·
      refine ⟨69284880109029879817123973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184759680290746346178997261 69284880109029879817123973)
      ·
        refine ⟨12990915020443102465710745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69284880109029879817123973 12990915020443102465710745)
        ·
          refine ⟨9743186265332326849283059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12990915020443102465710745 9743186265332326849283059)
          ·
            refine ⟨14614779397998490273924589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9743186265332326849283059 14614779397998490273924589)
            ·
              refine ⟨5480542274249433852721721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14614779397998490273924589 5480542274249433852721721)
              ·
                refine ⟨4110406705687075389541291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5480542274249433852721721 4110406705687075389541291)
                ·
                  refine ⟨6165610058530613084311937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110406705687075389541291 6165610058530613084311937)
                  ·
                    refine ⟨4624207543897959813233953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6165610058530613084311937 4624207543897959813233953)
                    ·
                      refine ⟨3468155657923469859925465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624207543897959813233953 3468155657923469859925465)
                      ·
                        rfl

theorem cell23_6754209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_6754209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754209 prefixEnd_6754209 := by exact prefixLift 6754209
  have htrace : WordTrace (prefixWord ++ tailWord_6754209) baseStart_6754209 baseEnd_6754209 := by
    simpa [prefixWord, tailWord_6754209, baseEnd_6754209] using wordTrace_append hprefix tailTrace_6754209
  have hstable : (prefixWord ++ tailWord_6754209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754209).length < 2 ^ (prefixWord ++ tailWord_6754209).sum := by decide
  have hdescent : baseEnd_6754209 < baseStart_6754209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754225 : List Nat := [1, 2, 2, 4, 2, 1, 4, 1, 2, 1, 3]
def baseStart_6754225 : Nat := 118140960795 + 6754225 * 2 ^ 59
def prefixEnd_6754225 : Nat := 4983230072969 + 3 ^ 40 * 6754225 * 2
def baseEnd_6754225 : Nat := 3468163873613941797325391

theorem tailTrace_6754225 : CollatzResearch.WordTrace tailWord_6754225 prefixEnd_6754225 3468163873613941797325391 := by
  unfold tailWord_6754225
  simp only [CollatzResearch.WordTrace]
  refine ⟨246346823955603829637912129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164231215970402553091941419 246346823955603829637912129)
  ·
    refine ⟨184760117966702872228434097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246346823955603829637912129 184760117966702872228434097)
    ·
      refine ⟨138570088475027154171325573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184760117966702872228434097 138570088475027154171325573)
      ·
        refine ⟨25981891589067591407123545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138570088475027154171325573 25981891589067591407123545)
        ·
          refine ⟨19486418691800693555342659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25981891589067591407123545 19486418691800693555342659)
          ·
            refine ⟨29229628037701040333013989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19486418691800693555342659 29229628037701040333013989)
            ·
              refine ⟨5480555257068945062440123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29229628037701040333013989 5480555257068945062440123)
              ·
                refine ⟨8220832885603417593660185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5480555257068945062440123 8220832885603417593660185)
                ·
                  refine ⟨6165624664202563195245139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8220832885603417593660185 6165624664202563195245139)
                  ·
                    refine ⟨9248436996303844792867709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6165624664202563195245139 9248436996303844792867709)
                    ·
                      refine ⟨3468163873613941797325391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9248436996303844792867709 3468163873613941797325391)
                      ·
                        rfl

theorem cell23_6754225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_6754225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754225 prefixEnd_6754225 := by exact prefixLift 6754225
  have htrace : WordTrace (prefixWord ++ tailWord_6754225) baseStart_6754225 baseEnd_6754225 := by
    simpa [prefixWord, tailWord_6754225, baseEnd_6754225] using wordTrace_append hprefix tailTrace_6754225
  have hstable : (prefixWord ++ tailWord_6754225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754225).length < 2 ^ (prefixWord ++ tailWord_6754225).sum := by decide
  have hdescent : baseEnd_6754225 < baseStart_6754225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754231 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 1, 4, 2]
def baseStart_6754231 : Nat := 118140960795 + 6754231 * 2 ^ 59
def prefixEnd_6754231 : Nat := 4983230072969 + 3 ^ 40 * 6754231 * 2
def baseEnd_6754231 : Nat := 3468166954497868773850363

theorem tailTrace_6754231 : CollatzResearch.WordTrace tailWord_6754231 prefixEnd_6754231 3468166954497868773850363 := by
  unfold tailWord_6754231
  simp only [CollatzResearch.WordTrace]
  refine ⟨246347042793582092662630547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164231361862388061775087031 246347042793582092662630547)
  ·
    refine ⟨369520564190373138993945821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246347042793582092662630547 369520564190373138993945821)
    ·
      refine ⟨138570211571389927122729683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369520564190373138993945821 138570211571389927122729683)
      ·
        refine ⟨207855317357084890684094525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138570211571389927122729683 207855317357084890684094525)
        ·
          refine ⟨77945744008906834006535447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207855317357084890684094525 77945744008906834006535447)
          ·
            refine ⟨116918616013360251009803171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77945744008906834006535447 116918616013360251009803171)
            ·
              refine ⟨175377924020040376514704757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116918616013360251009803171 175377924020040376514704757)
              ·
                refine ⟨16441680376878785298253571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175377924020040376514704757 16441680376878785298253571)
                ·
                  refine ⟨24662520565318177947380357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16441680376878785298253571 24662520565318177947380357)
                  ·
                    refine ⟨4624222605997158365133817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24662520565318177947380357 4624222605997158365133817)
                    ·
                      refine ⟨3468166954497868773850363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624222605997158365133817 3468166954497868773850363)
                      ·
                        rfl

theorem cell23_6754231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 4, 2].length) (baseStart_6754231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754231 prefixEnd_6754231 := by exact prefixLift 6754231
  have htrace : WordTrace (prefixWord ++ tailWord_6754231) baseStart_6754231 baseEnd_6754231 := by
    simpa [prefixWord, tailWord_6754231, baseEnd_6754231] using wordTrace_append hprefix tailTrace_6754231
  have hstable : (prefixWord ++ tailWord_6754231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754231).length < 2 ^ (prefixWord ++ tailWord_6754231).sum := by decide
  have hdescent : baseEnd_6754231 < baseStart_6754231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754234 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3]
def baseStart_6754234 : Nat := 118140960795 + 6754234 * 2 ^ 59
def prefixEnd_6754234 : Nat := 4983230072969 + 3 ^ 40 * 6754234 * 2
def baseEnd_6754234 : Nat := 3468168494939832262112849

theorem tailTrace_6754234 : CollatzResearch.WordTrace tailWord_6754234 prefixEnd_6754234 3468168494939832262112849 := by
  unfold tailWord_6754234
  simp only [CollatzResearch.WordTrace]
  refine ⟨61586788053142806043747439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164231434808380816116659837 61586788053142806043747439)
  ·
    refine ⟨92380182079714209065621159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61586788053142806043747439 92380182079714209065621159)
    ·
      refine ⟨138570273119571313598431739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92380182079714209065621159 138570273119571313598431739)
      ·
        refine ⟨207855409679356970397647609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138570273119571313598431739 207855409679356970397647609)
        ·
          refine ⟨155891557259517727798235707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207855409679356970397647609 155891557259517727798235707)
          ·
            refine ⟨233837335889276591697353561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155891557259517727798235707 233837335889276591697353561)
            ·
              refine ⟨175378001916957443773015171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233837335889276591697353561 175378001916957443773015171)
              ·
                refine ⟨263067002875436165659522757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175378001916957443773015171 263067002875436165659522757)
                ·
                  refine ⟨49325063039144281061160517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263067002875436165659522757 49325063039144281061160517)
                  ·
                    refine ⟨9248449319839552698967597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49325063039144281061160517 9248449319839552698967597)
                    ·
                      refine ⟨3468168494939832262112849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9248449319839552698967597 3468168494939832262112849)
                      ·
                        rfl

theorem cell23_6754234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_6754234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754234 prefixEnd_6754234 := by exact prefixLift 6754234
  have htrace : WordTrace (prefixWord ++ tailWord_6754234) baseStart_6754234 baseEnd_6754234 := by
    simpa [prefixWord, tailWord_6754234, baseEnd_6754234] using wordTrace_append hprefix tailTrace_6754234
  have hstable : (prefixWord ++ tailWord_6754234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754234).length < 2 ^ (prefixWord ++ tailWord_6754234).sum := by decide
  have hdescent : baseEnd_6754234 < baseStart_6754234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754248 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 1, 4, 2]
def baseStart_6754248 : Nat := 118140960795 + 6754248 * 2 ^ 59
def prefixEnd_6754248 : Nat := 4983230072969 + 3 ^ 40 * 6754248 * 2
def baseEnd_6754248 : Nat := 3468175683668995207337785

theorem tailTrace_6754248 : CollatzResearch.WordTrace tailWord_6754248 prefixEnd_6754248 3468175683668995207337785 := by
  unfold tailWord_6754248
  simp only [CollatzResearch.WordTrace]
  refine ⟨123173831417260252282999699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164231775223013669710666265 123173831417260252282999699)
  ·
    refine ⟨184760747125890378424499549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123173831417260252282999699 184760747125890378424499549)
    ·
      refine ⟨69285280172208891909187331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184760747125890378424499549 69285280172208891909187331)
      ·
        refine ⟨103927920258313337863780997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69285280172208891909187331 103927920258313337863780997)
        ·
          refine ⟨19486485048433750849458937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103927920258313337863780997 19486485048433750849458937)
          ·
            refine ⟨14614863786325313137094203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19486485048433750849458937 14614863786325313137094203)
            ·
              refine ⟨21922295679487969705641305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14614863786325313137094203 21922295679487969705641305)
              ·
                refine ⟨16441721759615977279230979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21922295679487969705641305 16441721759615977279230979)
                ·
                  refine ⟨24662582639423965918846469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16441721759615977279230979 24662582639423965918846469)
                  ·
                    refine ⟨4624234244891993609783713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24662582639423965918846469 4624234244891993609783713)
                    ·
                      refine ⟨3468175683668995207337785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624234244891993609783713 3468175683668995207337785)
                      ·
                        rfl

theorem cell23_6754248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_6754248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754248 prefixEnd_6754248 := by exact prefixLift 6754248
  have htrace : WordTrace (prefixWord ++ tailWord_6754248) baseStart_6754248 baseEnd_6754248 := by
    simpa [prefixWord, tailWord_6754248, baseEnd_6754248] using wordTrace_append hprefix tailTrace_6754248
  have hstable : (prefixWord ++ tailWord_6754248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754248).length < 2 ^ (prefixWord ++ tailWord_6754248).sum := by decide
  have hdescent : baseEnd_6754248 < baseStart_6754248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754284 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 4, 5]
def baseStart_6754284 : Nat := 118140960795 + 6754284 * 2 ^ 59
def prefixEnd_6754284 : Nat := 4983230072969 + 3 ^ 40 * 6754284 * 2
def baseEnd_6754284 : Nat := 1156064722990852355495873

theorem tailTrace_6754284 : CollatzResearch.WordTrace tailWord_6754284 prefixEnd_6754284 1156064722990852355495873 := by
  unfold tailWord_6754284
  simp only [CollatzResearch.WordTrace]
  refine ⟨123174487931195041357154953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164232650574926721809539937 123174487931195041357154953)
  ·
    refine ⟨92380865948396281017866215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123174487931195041357154953 92380865948396281017866215)
    ·
      refine ⟨138571298922594421526799323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92380865948396281017866215 138571298922594421526799323)
      ·
        refine ⟨207856948383891632290198985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138571298922594421526799323 207856948383891632290198985)
        ·
          refine ⟨155892711287918724217649239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207856948383891632290198985 155892711287918724217649239)
          ·
            refine ⟨233839066931878086326473859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155892711287918724217649239 233839066931878086326473859)
            ·
              refine ⟨350758600397817129489710789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233839066931878086326473859 350758600397817129489710789)
              ·
                refine ⟨65767237574590711779320773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350758600397817129489710789 65767237574590711779320773)
                ·
                  refine ⟨12331357045235758458622645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65767237574590711779320773 12331357045235758458622645)
                  ·
                    refine ⟨1156064722990852355495873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12331357045235758458622645 1156064722990852355495873)
                    ·
                      rfl

theorem cell23_6754284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_6754284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754284 prefixEnd_6754284 := by exact prefixLift 6754284
  have htrace : WordTrace (prefixWord ++ tailWord_6754284) baseStart_6754284 baseEnd_6754284 := by
    simpa [prefixWord, tailWord_6754284, baseEnd_6754284] using wordTrace_append hprefix tailTrace_6754284
  have hstable : (prefixWord ++ tailWord_6754284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754284).length < 2 ^ (prefixWord ++ tailWord_6754284).sum := by decide
  have hdescent : baseEnd_6754284 < baseStart_6754284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754301 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_6754301 : Nat := 118140960795 + 6754301 * 2 ^ 59
def prefixEnd_6754301 : Nat := 4983230072969 + 3 ^ 40 * 6754301 * 2
def baseEnd_6754301 : Nat := 1156067632714561166658347

theorem tailTrace_6754301 : CollatzResearch.WordTrace tailWord_6754301 prefixEnd_6754301 1156067632714561166658347 := by
  unfold tailWord_6754301
  simp only [CollatzResearch.WordTrace]
  refine ⟨246349595903328494617678757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164233063935552329745119171 246349595903328494617678757)
  ·
    refine ⟨46190549231874092740814767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246349595903328494617678757 46190549231874092740814767)
    ·
      refine ⟨69285823847811139111222151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46190549231874092740814767 69285823847811139111222151)
      ·
        refine ⟨103928735771716708666833227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69285823847811139111222151 103928735771716708666833227)
        ·
          refine ⟨155893103657575063000249841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103928735771716708666833227 155893103657575063000249841)
          ·
            refine ⟨116919827743181297250187381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155893103657575063000249841 116919827743181297250187381)
            ·
              refine ⟨10961233850923246617205067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116919827743181297250187381 10961233850923246617205067)
              ·
                refine ⟨16441850776384869925807601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10961233850923246617205067 16441850776384869925807601)
                ·
                  refine ⟨12331388082288652444355701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16441850776384869925807601 12331388082288652444355701)
                  ·
                    refine ⟨1156067632714561166658347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12331388082288652444355701 1156067632714561166658347)
                    ·
                      rfl

theorem cell23_6754301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_6754301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754301 prefixEnd_6754301 := by exact prefixLift 6754301
  have htrace : WordTrace (prefixWord ++ tailWord_6754301) baseStart_6754301 baseEnd_6754301 := by
    simpa [prefixWord, tailWord_6754301, baseEnd_6754301] using wordTrace_append hprefix tailTrace_6754301
  have hstable : (prefixWord ++ tailWord_6754301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754301).length < 2 ^ (prefixWord ++ tailWord_6754301).sum := by decide
  have hdescent : baseEnd_6754301 < baseStart_6754301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754338 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_6754338 : Nat := 118140960795 + 6754338 * 2 ^ 59
def prefixEnd_6754338 : Nat := 4983230072969 + 3 ^ 40 * 6754338 * 2
def baseEnd_6754338 : Nat := 3468221896927899855212371

theorem tailTrace_6754338 : CollatzResearch.WordTrace tailWord_6754338 prefixEnd_6754338 3468221896927899855212371 := by
  unfold tailWord_6754338
  simp only [CollatzResearch.WordTrace]
  refine ⟨61587736351048612484193917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164233963602796299957850445 61587736351048612484193917)
  ·
    refine ⟨23095401131643229681572719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61587736351048612484193917 23095401131643229681572719)
    ·
      refine ⟨34643101697464844522359079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23095401131643229681572719 34643101697464844522359079)
      ·
        refine ⟨51964652546197266783538619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34643101697464844522359079 51964652546197266783538619)
        ·
          refine ⟨77946978819295900175307929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51964652546197266783538619 77946978819295900175307929)
          ·
            refine ⟨58460234114471925131480947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77946978819295900175307929 58460234114471925131480947)
            ·
              refine ⟨87690351171707887697221421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58460234114471925131480947 87690351171707887697221421)
              ·
                refine ⟨32883881689390457886458033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87690351171707887697221421 32883881689390457886458033)
                ·
                  refine ⟨24662911267042843414843525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32883881689390457886458033 24662911267042843414843525)
                  ·
                    refine ⟨4624295862570533140283161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24662911267042843414843525 4624295862570533140283161)
                    ·
                      refine ⟨3468221896927899855212371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624295862570533140283161 3468221896927899855212371)
                      ·
                        rfl

theorem cell23_6754338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_6754338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754338 prefixEnd_6754338 := by exact prefixLift 6754338
  have htrace : WordTrace (prefixWord ++ tailWord_6754338) baseStart_6754338 baseEnd_6754338 := by
    simpa [prefixWord, tailWord_6754338, baseEnd_6754338] using wordTrace_append hprefix tailTrace_6754338
  have hstable : (prefixWord ++ tailWord_6754338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754338).length < 2 ^ (prefixWord ++ tailWord_6754338).sum := by decide
  have hdescent : baseEnd_6754338 < baseStart_6754338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754341 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 1, 4, 3]
def baseStart_6754341 : Nat := 118140960795 + 6754341 * 2 ^ 59
def prefixEnd_6754341 : Nat := 4983230072969 + 3 ^ 40 * 6754341 * 2
def baseEnd_6754341 : Nat := 3468223437369863343474857

theorem tailTrace_6754341 : CollatzResearch.WordTrace tailWord_6754341 prefixEnd_6754341 3468223437369863343474857 := by
  unfold tailWord_6754341
  simp only [CollatzResearch.WordTrace]
  refine ⟨246351054823183581449134877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164234036548789054299423251 246351054823183581449134877)
  ·
    refine ⟨92381645558693843043425579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246351054823183581449134877 92381645558693843043425579)
    ·
      refine ⟨138572468338040764565138369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92381645558693843043425579 138572468338040764565138369)
      ·
        refine ⟨103929351253530573423853777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138572468338040764565138369 103929351253530573423853777)
        ·
          refine ⟨77947013440147930067890333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103929351253530573423853777 77947013440147930067890333)
          ·
            refine ⟨29230130040055473775458875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77947013440147930067890333 29230130040055473775458875)
            ·
              refine ⟨43845195060083210663188313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29230130040055473775458875 43845195060083210663188313)
              ·
                refine ⟨32883896295062407997391235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43845195060083210663188313 32883896295062407997391235)
                ·
                  refine ⟨49325844442593611996086853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32883896295062407997391235 49325844442593611996086853)
                  ·
                    refine ⟨9248595832986302249266285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49325844442593611996086853 9248595832986302249266285)
                    ·
                      refine ⟨3468223437369863343474857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9248595832986302249266285 3468223437369863343474857)
                      ·
                        rfl

theorem cell23_6754341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_6754341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754341 prefixEnd_6754341 := by exact prefixLift 6754341
  have htrace : WordTrace (prefixWord ++ tailWord_6754341) baseStart_6754341 baseEnd_6754341 := by
    simpa [prefixWord, tailWord_6754341, baseEnd_6754341] using wordTrace_append hprefix tailTrace_6754341
  have hstable : (prefixWord ++ tailWord_6754341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754341).length < 2 ^ (prefixWord ++ tailWord_6754341).sum := by decide
  have hdescent : baseEnd_6754341 < baseStart_6754341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754358 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_6754358 : Nat := 118140960795 + 6754358 * 2 ^ 59
def prefixEnd_6754358 : Nat := 4983230072969 + 3 ^ 40 * 6754358 * 2
def baseEnd_6754358 : Nat := 3468232166540989776962279

theorem tailTrace_6754358 : CollatzResearch.WordTrace tailWord_6754358 prefixEnd_6754358 3468232166540989776962279 := by
  unfold tailWord_6754358
  simp only [CollatzResearch.WordTrace]
  refine ⟨15396979679007624584531483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164234449909414662235002485 15396979679007624584531483)
  ·
    refine ⟨23095469518511436876797225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15396979679007624584531483 23095469518511436876797225)
    ·
      refine ⟨17321602138883577657597919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23095469518511436876797225 17321602138883577657597919)
      ·
        refine ⟨25982403208325366486396879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17321602138883577657597919 25982403208325366486396879)
        ·
          refine ⟨38973604812488049729595319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25982403208325366486396879 38973604812488049729595319)
          ·
            refine ⟨58460407218732074594392979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38973604812488049729595319 58460407218732074594392979)
            ·
              refine ⟨87690610828098111891589469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58460407218732074594392979 87690610828098111891589469)
              ·
                refine ⟨32883979060536791959346051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87690610828098111891589469 32883979060536791959346051)
                ·
                  refine ⟨49325968590805187939019077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32883979060536791959346051 49325968590805187939019077)
                  ·
                    refine ⟨9248619110775972738566077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49325968590805187939019077 9248619110775972738566077)
                    ·
                      refine ⟨3468232166540989776962279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9248619110775972738566077 3468232166540989776962279)
                      ·
                        rfl

theorem cell23_6754358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_6754358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754358 prefixEnd_6754358 := by exact prefixLift 6754358
  have htrace : WordTrace (prefixWord ++ tailWord_6754358) baseStart_6754358 baseEnd_6754358 := by
    simpa [prefixWord, tailWord_6754358, baseEnd_6754358] using wordTrace_append hprefix tailTrace_6754358
  have hstable : (prefixWord ++ tailWord_6754358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754358).length < 2 ^ (prefixWord ++ tailWord_6754358).sum := by decide
  have hdescent : baseEnd_6754358 < baseStart_6754358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754382 : List Nat := [4, 1, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_6754382 : Nat := 118140960795 + 6754382 * 2 ^ 59
def prefixEnd_6754382 : Nat := 4983230072969 + 3 ^ 40 * 6754382 * 2
def baseEnd_6754382 : Nat := 1156081496692232561020723

theorem tailTrace_6754382 : CollatzResearch.WordTrace tailWord_6754382 prefixEnd_6754382 1156081496692232561020723 := by
  unfold tailWord_6754382
  simp only [CollatzResearch.WordTrace]
  refine ⟨30794068777004380681422175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164235033477356696967584933 30794068777004380681422175)
  ·
    refine ⟨46191103165506571022133263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30794068777004380681422175 46191103165506571022133263)
    ·
      refine ⟨69286654748259856533199895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46191103165506571022133263 69286654748259856533199895)
      ·
        refine ⟨103929982122389784799799843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69286654748259856533199895 103929982122389784799799843)
        ·
          refine ⟨155894973183584677199699765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103929982122389784799799843 155894973183584677199699765)
          ·
            refine ⟨14615153735961063487471853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155894973183584677199699765 14615153735961063487471853)
            ·
              refine ⟨5480682650985398807801945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14615153735961063487471853 5480682650985398807801945)
              ·
                refine ⟨4110511988239049105851459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5480682650985398807801945 4110511988239049105851459)
                ·
                  refine ⟨6165767982358573658777189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110511988239049105851459 6165767982358573658777189)
                  ·
                    refine ⟨1156081496692232561020723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6165767982358573658777189 1156081496692232561020723)
                    ·
                      rfl

theorem cell23_6754382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_6754382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754382 prefixEnd_6754382 := by exact prefixLift 6754382
  have htrace : WordTrace (prefixWord ++ tailWord_6754382) baseStart_6754382 baseEnd_6754382 := by
    simpa [prefixWord, tailWord_6754382, baseEnd_6754382] using wordTrace_append hprefix tailTrace_6754382
  have hstable : (prefixWord ++ tailWord_6754382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754382).length < 2 ^ (prefixWord ++ tailWord_6754382).sum := by decide
  have hdescent : baseEnd_6754382 < baseStart_6754382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754384 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 7]
def baseStart_6754384 : Nat := 118140960795 + 6754384 * 2 ^ 59
def prefixEnd_6754384 : Nat := 4983230072969 + 3 ^ 40 * 6754384 * 2
def baseEnd_6754384 : Nat := 3468245517038006675237159

theorem tailTrace_6754384 : CollatzResearch.WordTrace tailWord_6754384 prefixEnd_6754384 3468245517038006675237159 := by
  unfold tailWord_6754384
  simp only [CollatzResearch.WordTrace]
  refine ⟨123176311581013899896475103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164235082108018533195300137 123176311581013899896475103)
  ·
    refine ⟨184764467371520849844712655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123176311581013899896475103 184764467371520849844712655)
    ·
      refine ⟨277146701057281274767068983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184764467371520849844712655 277146701057281274767068983)
      ·
        refine ⟨415720051585921912150603475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277146701057281274767068983 415720051585921912150603475)
        ·
          refine ⟨623580077378882868225905213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415720051585921912150603475 623580077378882868225905213)
          ·
            refine ⟨233842529017081075584714455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 623580077378882868225905213 233842529017081075584714455)
            ·
              refine ⟨350763793525621613377071683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233842529017081075584714455 350763793525621613377071683)
              ·
                refine ⟨526145690288432420065607525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350763793525621613377071683 526145690288432420065607525)
                ·
                  refine ⟨98652316929081078762301411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526145690288432420065607525 98652316929081078762301411)
                  ·
                    refine ⟨147978475393621618143452117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98652316929081078762301411 147978475393621618143452117)
                    ·
                      refine ⟨3468245517038006675237159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147978475393621618143452117 3468245517038006675237159)
                      ·
                        rfl

theorem cell23_6754384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_6754384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754384 prefixEnd_6754384 := by exact prefixLift 6754384
  have htrace : WordTrace (prefixWord ++ tailWord_6754384) baseStart_6754384 baseEnd_6754384 := by
    simpa [prefixWord, tailWord_6754384, baseEnd_6754384] using wordTrace_append hprefix tailTrace_6754384
  have hstable : (prefixWord ++ tailWord_6754384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754384).length < 2 ^ (prefixWord ++ tailWord_6754384).sum := by decide
  have hdescent : baseEnd_6754384 < baseStart_6754384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754415 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 2, 3, 2]
def baseStart_6754415 : Nat := 118140960795 + 6754415 * 2 ^ 59
def prefixEnd_6754415 : Nat := 4983230072969 + 3 ^ 40 * 6754415 * 2
def baseEnd_6754415 : Nat := 3468261434938296053949517

theorem tailTrace_6754415 : CollatzResearch.WordTrace tailWord_6754415 prefixEnd_6754415 3468261434938296053949517 := by
  unfold tailWord_6754415
  simp only [CollatzResearch.WordTrace]
  refine ⟨246353753824915492087328699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164235835883276994724885799 246353753824915492087328699)
  ·
    refine ⟨369530630737373238130993049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246353753824915492087328699 369530630737373238130993049)
    ·
      refine ⟨277147973053029928598244787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369530630737373238130993049 277147973053029928598244787)
      ·
        refine ⟨415721959579544892897367181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277147973053029928598244787 415721959579544892897367181)
        ·
          refine ⟨155895734842329334836512693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415721959579544892897367181 155895734842329334836512693)
          ·
            refine ⟨14615225141468375140923065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155895734842329334836512693 14615225141468375140923065)
            ·
              refine ⟨10961418856101281355692299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14615225141468375140923065 10961418856101281355692299)
              ·
                refine ⟨16442128284151922033538449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10961418856101281355692299 16442128284151922033538449)
                ·
                  refine ⟨12331596213113941525153837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16442128284151922033538449 12331596213113941525153837)
                  ·
                    refine ⟨4624348579917728071932689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12331596213113941525153837 4624348579917728071932689)
                    ·
                      refine ⟨3468261434938296053949517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624348579917728071932689 3468261434938296053949517)
                      ·
                        rfl

theorem cell23_6754415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 3, 2].length) (baseStart_6754415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754415 prefixEnd_6754415 := by exact prefixLift 6754415
  have htrace : WordTrace (prefixWord ++ tailWord_6754415) baseStart_6754415 baseEnd_6754415 := by
    simpa [prefixWord, tailWord_6754415, baseEnd_6754415] using wordTrace_append hprefix tailTrace_6754415
  have hstable : (prefixWord ++ tailWord_6754415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754415).length < 2 ^ (prefixWord ++ tailWord_6754415).sum := by decide
  have hdescent : baseEnd_6754415 < baseStart_6754415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754425 : List Nat := [1, 2, 1, 3, 4, 2, 3, 1, 1, 5]
def baseStart_6754425 : Nat := 118140960795 + 6754425 * 2 ^ 59
def prefixEnd_6754425 : Nat := 4983230072969 + 3 ^ 40 * 6754425 * 2
def baseEnd_6754425 : Nat := 1156088856581613671608157

theorem tailTrace_6754425 : CollatzResearch.WordTrace tailWord_6754425 prefixEnd_6754425 1156088856581613671608157 := by
  unfold tailWord_6754425
  simp only [CollatzResearch.WordTrace]
  refine ⟨246354118554879263795192729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164236079036586175863461819 246354118554879263795192729)
  ·
    refine ⟨184765588916159447846394547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246354118554879263795192729 184765588916159447846394547)
    ·
      refine ⟨277148383374239171769591821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184765588916159447846394547 277148383374239171769591821)
      ·
        refine ⟨103930643765339689413596933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277148383374239171769591821 103930643765339689413596933)
        ·
          refine ⟨19486995706001191765049425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103930643765339689413596933 19486995706001191765049425)
          ·
            refine ⟨14615246779500893823787069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19486995706001191765049425 14615246779500893823787069)
            ·
              refine ⟨5480717542312835183920151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14615246779500893823787069 5480717542312835183920151)
              ·
                refine ⟨8221076313469252775880227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5480717542312835183920151 8221076313469252775880227)
                ·
                  refine ⟨12331614470203879163820341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8221076313469252775880227 12331614470203879163820341)
                  ·
                    refine ⟨1156088856581613671608157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12331614470203879163820341 1156088856581613671608157)
                    ·
                      rfl

theorem cell23_6754425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 1, 5].length) (baseStart_6754425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754425 prefixEnd_6754425 := by exact prefixLift 6754425
  have htrace : WordTrace (prefixWord ++ tailWord_6754425) baseStart_6754425 baseEnd_6754425 := by
    simpa [prefixWord, tailWord_6754425, baseEnd_6754425] using wordTrace_append hprefix tailTrace_6754425
  have hstable : (prefixWord ++ tailWord_6754425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754425).length < 2 ^ (prefixWord ++ tailWord_6754425).sum := by decide
  have hdescent : baseEnd_6754425 < baseStart_6754425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754441 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 3, 2, 4]
def baseStart_6754441 : Nat := 118140960795 + 6754441 * 2 ^ 59
def prefixEnd_6754441 : Nat := 4983230072969 + 3 ^ 40 * 6754441 * 2
def baseEnd_6754441 : Nat := 3468274785435312952224397

theorem tailTrace_6754441 : CollatzResearch.WordTrace tailWord_6754441 prefixEnd_6754441 3468274785435312952224397 := by
  unfold tailWord_6754441
  simp only [CollatzResearch.WordTrace]
  refine ⟨246354702122821298527775177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164236468081880865685183451 246354702122821298527775177)
  ·
    refine ⟨184766026592115973895831383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246354702122821298527775177 184766026592115973895831383)
    ·
      refine ⟨277149039888173960843747075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184766026592115973895831383 277149039888173960843747075)
      ·
        refine ⟨415723559832260941265620613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277149039888173960843747075 415723559832260941265620613)
        ·
          refine ⟨77948167468548926487303865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 415723559832260941265620613 77948167468548926487303865)
          ·
            refine ⟨58461125601411694865477899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77948167468548926487303865 58461125601411694865477899)
            ·
              refine ⟨87691688402117542298216849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58461125601411694865477899 87691688402117542298216849)
              ·
                refine ⟨65768766301588156723662637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87691688402117542298216849 65768766301588156723662637)
                ·
                  refine ⟨24663287363095558771373489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65768766301588156723662637 24663287363095558771373489)
                  ·
                    refine ⟨18497465522321669078530117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24663287363095558771373489 18497465522321669078530117)
                    ·
                      refine ⟨3468274785435312952224397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18497465522321669078530117 3468274785435312952224397)
                      ·
                        rfl

theorem cell23_6754441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_6754441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754441 prefixEnd_6754441 := by exact prefixLift 6754441
  have htrace : WordTrace (prefixWord ++ tailWord_6754441) baseStart_6754441 baseEnd_6754441 := by
    simpa [prefixWord, tailWord_6754441, baseEnd_6754441] using wordTrace_append hprefix tailTrace_6754441
  have hstable : (prefixWord ++ tailWord_6754441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754441).length < 2 ^ (prefixWord ++ tailWord_6754441).sum := by decide
  have hdescent : baseEnd_6754441 < baseStart_6754441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754501 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_6754501 : Nat := 118140960795 + 6754501 * 2 ^ 59
def prefixEnd_6754501 : Nat := 4983230072969 + 3 ^ 40 * 6754501 * 2
def baseEnd_6754501 : Nat := 3468305594274582717474121

theorem tailTrace_6754501 : CollatzResearch.WordTrace tailWord_6754501 prefixEnd_6754501 3468305594274582717474121 := by
  unfold tailWord_6754501
  simp only [CollatzResearch.WordTrace]
  refine ⟨246356890502603928774959357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164237927001735952516639571 246356890502603928774959357)
  ·
    refine ⟨92383833938476473290609759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246356890502603928774959357 92383833938476473290609759)
    ·
      refine ⟨138575750907714709935914639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92383833938476473290609759 138575750907714709935914639)
      ·
        refine ⟨207863626361572064903871959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138575750907714709935914639 207863626361572064903871959)
        ·
          refine ⟨311795439542358097355807939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207863626361572064903871959 311795439542358097355807939)
          ·
            refine ⟨467693159313537146033711909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311795439542358097355807939 467693159313537146033711909)
            ·
              refine ⟨87692467371288214881320983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 467693159313537146033711909 87692467371288214881320983)
              ·
                refine ⟨131538701056932322321981475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87692467371288214881320983 131538701056932322321981475)
                ·
                  refine ⟨197308051585398483482972213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131538701056932322321981475 197308051585398483482972213)
                  ·
                    refine ⟨18497629836131107826528645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 197308051585398483482972213 18497629836131107826528645)
                    ·
                      refine ⟨3468305594274582717474121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18497629836131107826528645 3468305594274582717474121)
                      ·
                        rfl

theorem cell23_6754501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_6754501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754501 prefixEnd_6754501 := by exact prefixLift 6754501
  have htrace : WordTrace (prefixWord ++ tailWord_6754501) baseStart_6754501 baseEnd_6754501 := by
    simpa [prefixWord, tailWord_6754501, baseEnd_6754501] using wordTrace_append hprefix tailTrace_6754501
  have hstable : (prefixWord ++ tailWord_6754501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754501).length < 2 ^ (prefixWord ++ tailWord_6754501).sum := by decide
  have hdescent : baseEnd_6754501 < baseStart_6754501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754511 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 2, 6]
def baseStart_6754511 : Nat := 118140960795 + 6754511 * 2 ^ 59
def prefixEnd_6754511 : Nat := 4983230072969 + 3 ^ 40 * 6754511 * 2
def baseEnd_6754511 : Nat := 1156103576360375892783025

theorem tailTrace_6754511 : CollatzResearch.WordTrace tailWord_6754511 prefixEnd_6754511 1156103576360375892783025 := by
  unfold tailWord_6754511
  simp only [CollatzResearch.WordTrace]
  refine ⟨246357255232567700482823387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164238170155045133655215591 246357255232567700482823387)
  ·
    refine ⟨369535882848851550724235081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246357255232567700482823387 369535882848851550724235081)
    ·
      refine ⟨277151912136638663043176311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369535882848851550724235081 277151912136638663043176311)
      ·
        refine ⟨415727868204957994564764467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277151912136638663043176311 415727868204957994564764467)
        ·
          refine ⟨623591802307436991847146701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415727868204957994564764467 623591802307436991847146701)
          ·
            refine ⟨233846925865288871942680013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 623591802307436991847146701 233846925865288871942680013)
            ·
              refine ⟨87692597199483326978505005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233846925865288871942680013 87692597199483326978505005)
              ·
                refine ⟨32884723949806247616939377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87692597199483326978505005 32884723949806247616939377)
                ·
                  refine ⟨24663542962354685712704533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32884723949806247616939377 24663542962354685712704533)
                  ·
                    refine ⟨1156103576360375892783025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24663542962354685712704533 1156103576360375892783025)
                    ·
                      rfl

theorem cell23_6754511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_6754511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754511 prefixEnd_6754511 := by exact prefixLift 6754511
  have htrace : WordTrace (prefixWord ++ tailWord_6754511) baseStart_6754511 baseEnd_6754511 := by
    simpa [prefixWord, tailWord_6754511, baseEnd_6754511] using wordTrace_append hprefix tailTrace_6754511
  have hstable : (prefixWord ++ tailWord_6754511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754511).length < 2 ^ (prefixWord ++ tailWord_6754511).sum := by decide
  have hdescent : baseEnd_6754511 < baseStart_6754511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754538 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_6754538 : Nat := 118140960795 + 6754538 * 2 ^ 59
def prefixEnd_6754538 : Nat := 4983230072969 + 3 ^ 40 * 6754538 * 2
def baseEnd_6754538 : Nat := 3468324593058799072711451

theorem tailTrace_6754538 : CollatzResearch.WordTrace tailWord_6754538 prefixEnd_6754538 3468324593058799072711451 := by
  unfold tailWord_6754538
  simp only [CollatzResearch.WordTrace]
  refine ⟨61589560000867471023514067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164238826668979922729370845 61589560000867471023514067)
  ·
    refine ⟨92384340001301206535271101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61589560000867471023514067 92384340001301206535271101)
    ·
      refine ⟨34644127500487952450726663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92384340001301206535271101 34644127500487952450726663)
      ·
        refine ⟨51966191250731928676089995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34644127500487952450726663 51966191250731928676089995)
        ·
          refine ⟨77949286876097893014134993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51966191250731928676089995 77949286876097893014134993)
          ·
            refine ⟨58461965157073419760601245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77949286876097893014134993 58461965157073419760601245)
            ·
              refine ⟨21923236933902532410225467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58461965157073419760601245 21923236933902532410225467)
              ·
                refine ⟨32884855400853798615338201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21923236933902532410225467 32884855400853798615338201)
                ·
                  refine ⟨24663641550640348961503651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32884855400853798615338201 24663641550640348961503651)
                  ·
                    refine ⟨36995462325960523442255477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24663641550640348961503651 36995462325960523442255477)
                    ·
                      refine ⟨3468324593058799072711451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36995462325960523442255477 3468324593058799072711451)
                      ·
                        rfl

theorem cell23_6754538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_6754538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754538 prefixEnd_6754538 := by exact prefixLift 6754538
  have htrace : WordTrace (prefixWord ++ tailWord_6754538) baseStart_6754538 baseEnd_6754538 := by
    simpa [prefixWord, tailWord_6754538, baseEnd_6754538] using wordTrace_append hprefix tailTrace_6754538
  have hstable : (prefixWord ++ tailWord_6754538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754538).length < 2 ^ (prefixWord ++ tailWord_6754538).sum := by decide
  have hdescent : baseEnd_6754538 < baseStart_6754538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754569 : List Nat := [1, 2, 1, 1, 3, 4, 4, 1, 2, 2, 2]
def baseStart_6754569 : Nat := 118140960795 + 6754569 * 2 ^ 59
def prefixEnd_6754569 : Nat := 4983230072969 + 3 ^ 40 * 6754569 * 2
def baseEnd_6754569 : Nat := 3468340510959088451423809

theorem tailTrace_6754569 : CollatzResearch.WordTrace tailWord_6754569 prefixEnd_6754569 3468340510959088451423809 := by
  unfold tailWord_6754569
  simp only [CollatzResearch.WordTrace]
  refine ⟨246359370666357576388434761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164239580444238384258956507 246359370666357576388434761)
  ·
    refine ⟨184769527999768182291326071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246359370666357576388434761 184769527999768182291326071)
    ·
      refine ⟨277154291999652273436989107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184769527999768182291326071 277154291999652273436989107)
      ·
        refine ⟨415731437999478410155483661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277154291999652273436989107 415731437999478410155483661)
        ·
          refine ⟨155899289249804403808306373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415731437999478410155483661 155899289249804403808306373)
          ·
            refine ⟨29231116734338325714057445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155899289249804403808306373 29231116734338325714057445)
            ·
              refine ⟨5480834387688436071385771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29231116734338325714057445 5480834387688436071385771)
              ·
                refine ⟨8221251581532654107078657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5480834387688436071385771 8221251581532654107078657)
                ·
                  refine ⟨6165938686149490580308993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8221251581532654107078657 6165938686149490580308993)
                  ·
                    refine ⟨4624454014612117935231745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6165938686149490580308993 4624454014612117935231745)
                    ·
                      refine ⟨3468340510959088451423809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624454014612117935231745 3468340510959088451423809)
                      ·
                        rfl

theorem cell23_6754569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 2, 2, 2].length) (baseStart_6754569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754569 prefixEnd_6754569 := by exact prefixLift 6754569
  have htrace : WordTrace (prefixWord ++ tailWord_6754569) baseStart_6754569 baseEnd_6754569 := by
    simpa [prefixWord, tailWord_6754569, baseEnd_6754569] using wordTrace_append hprefix tailTrace_6754569
  have hstable : (prefixWord ++ tailWord_6754569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754569).length < 2 ^ (prefixWord ++ tailWord_6754569).sum := by decide
  have hdescent : baseEnd_6754569 < baseStart_6754569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754608 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 4]
def baseStart_6754608 : Nat := 118140960795 + 6754608 * 2 ^ 59
def prefixEnd_6754608 : Nat := 4983230072969 + 3 ^ 40 * 6754608 * 2
def baseEnd_6754608 : Nat := 3468360536704613798836129

theorem tailTrace_6754608 : CollatzResearch.WordTrace tailWord_6754608 prefixEnd_6754608 3468360536704613798836129 := by
  unfold tailWord_6754608
  simp only [CollatzResearch.WordTrace]
  refine ⟨123180396556608143024552239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164240528742144190699402985 123180396556608143024552239)
  ·
    refine ⟨184770594834912214536828359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123180396556608143024552239 184770594834912214536828359)
    ·
      refine ⟨277155892252368321805242539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184770594834912214536828359 277155892252368321805242539)
      ·
        refine ⟨415733838378552482707863809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277155892252368321805242539 415733838378552482707863809)
        ·
          refine ⟨311800378783914362030897857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415733838378552482707863809 311800378783914362030897857)
          ·
            refine ⟨233850284087935771523173393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311800378783914362030897857 233850284087935771523173393)
            ·
              refine ⟨175387713065951828642380045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233850284087935771523173393 175387713065951828642380045)
              ·
                refine ⟨65770392399731935740892517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175387713065951828642380045 65770392399731935740892517)
                ·
                  refine ⟨12331948574949737951417347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65770392399731935740892517 12331948574949737951417347)
                  ·
                    refine ⟨18497922862424606927126021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12331948574949737951417347 18497922862424606927126021)
                    ·
                      refine ⟨3468360536704613798836129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18497922862424606927126021 3468360536704613798836129)
                      ·
                        rfl

theorem cell23_6754608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_6754608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754608 prefixEnd_6754608 := by exact prefixLift 6754608
  have htrace : WordTrace (prefixWord ++ tailWord_6754608) baseStart_6754608 baseEnd_6754608 := by
    simpa [prefixWord, tailWord_6754608, baseEnd_6754608] using wordTrace_append hprefix tailTrace_6754608
  have hstable : (prefixWord ++ tailWord_6754608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754608).length < 2 ^ (prefixWord ++ tailWord_6754608).sum := by decide
  have hdescent : baseEnd_6754608 < baseStart_6754608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754609 : List Nat := [1, 2, 2, 3, 4, 2, 2, 2, 5]
def baseStart_6754609 : Nat := 118140960795 + 6754609 * 2 ^ 59
def prefixEnd_6754609 : Nat := 4983230072969 + 3 ^ 40 * 6754609 * 2
def baseEnd_6754609 : Nat := 385373450020585366102625

theorem tailTrace_6754609 : CollatzResearch.WordTrace tailWord_6754609 prefixEnd_6754609 385373450020585366102625 := by
  unfold tailWord_6754609
  simp only [CollatzResearch.WordTrace]
  refine ⟨246360829586212663219890881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164240553057475108813260587 246360829586212663219890881)
  ·
    refine ⟨184770622189659497414918161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246360829586212663219890881 184770622189659497414918161)
    ·
      refine ⟨138577966642244623061188621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184770622189659497414918161 138577966642244623061188621)
      ·
        refine ⟨51966737490841733647945733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138577966642244623061188621 51966737490841733647945733)
        ·
          refine ⟨9743763279532825058989825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51966737490841733647945733 9743763279532825058989825)
          ·
            refine ⟨7307822459649618794242369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9743763279532825058989825 7307822459649618794242369)
            ·
              refine ⟨5480866844737214095681777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7307822459649618794242369 5480866844737214095681777)
              ·
                refine ⟨4110650133552910571761333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5480866844737214095681777 4110650133552910571761333)
                ·
                  refine ⟨385373450020585366102625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4110650133552910571761333 385373450020585366102625)
                  ·
                    rfl

theorem cell23_6754609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 5].length) (baseStart_6754609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754609 prefixEnd_6754609 := by exact prefixLift 6754609
  have htrace : WordTrace (prefixWord ++ tailWord_6754609) baseStart_6754609 baseEnd_6754609 := by
    simpa [prefixWord, tailWord_6754609, baseEnd_6754609] using wordTrace_append hprefix tailTrace_6754609
  have hstable : (prefixWord ++ tailWord_6754609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754609).length < 2 ^ (prefixWord ++ tailWord_6754609).sum := by decide
  have hdescent : baseEnd_6754609 < baseStart_6754609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754612 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_6754612 : Nat := 118140960795 + 6754612 * 2 ^ 59
def prefixEnd_6754612 : Nat := 4983230072969 + 3 ^ 40 * 6754612 * 2
def baseEnd_6754612 : Nat := 3468362590627231783186111

theorem tailTrace_6754612 : CollatzResearch.WordTrace tailWord_6754612 prefixEnd_6754612 3468362590627231783186111 := by
  unfold tailWord_6754612
  simp only [CollatzResearch.WordTrace]
  refine ⟨123180469502600897366125045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164240626003467863154833393 123180469502600897366125045)
  ·
    refine ⟨11548169015868834128074223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123180469502600897366125045 11548169015868834128074223)
    ·
      refine ⟨17322253523803251192111335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11548169015868834128074223 17322253523803251192111335)
      ·
        refine ⟨25983380285704876788167003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17322253523803251192111335 25983380285704876788167003)
        ·
          refine ⟨38975070428557315182250505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25983380285704876788167003 38975070428557315182250505)
          ·
            refine ⟨29231302821417986386687879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38975070428557315182250505 29231302821417986386687879)
            ·
              refine ⟨43846954232126979580031819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29231302821417986386687879 43846954232126979580031819)
              ·
                refine ⟨65770431348190469370047729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43846954232126979580031819 65770431348190469370047729)
                ·
                  refine ⟨49327823511142852027535797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65770431348190469370047729 49327823511142852027535797)
                  ·
                    refine ⟨4624483454169642377581481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49327823511142852027535797 4624483454169642377581481)
                    ·
                      refine ⟨3468362590627231783186111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624483454169642377581481 3468362590627231783186111)
                      ·
                        rfl

theorem cell23_6754612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_6754612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754612 prefixEnd_6754612 := by exact prefixLift 6754612
  have htrace : WordTrace (prefixWord ++ tailWord_6754612) baseStart_6754612 baseEnd_6754612 := by
    simpa [prefixWord, tailWord_6754612, baseEnd_6754612] using wordTrace_append hprefix tailTrace_6754612
  have hstable : (prefixWord ++ tailWord_6754612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754612).length < 2 ^ (prefixWord ++ tailWord_6754612).sum := by decide
  have hdescent : baseEnd_6754612 < baseStart_6754612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754638 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_6754638 : Nat := 118140960795 + 6754638 * 2 ^ 59
def prefixEnd_6754638 : Nat := 4983230072969 + 3 ^ 40 * 6754638 * 2
def baseEnd_6754638 : Nat := 3468375941124248681460991

theorem tailTrace_6754638 : CollatzResearch.WordTrace tailWord_6754638 prefixEnd_6754638 3468375941124248681460991 := by
  unfold tailWord_6754638
  simp only [CollatzResearch.WordTrace]
  refine ⟨30795235912888450146587071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164241258202071734115131045 30795235912888450146587071)
  ·
    refine ⟨46192853869332675219880607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30795235912888450146587071 46192853869332675219880607)
    ·
      refine ⟨69289280803999012829820911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46192853869332675219880607 69289280803999012829820911)
      ·
        refine ⟨103933921205998519244731367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69289280803999012829820911 103933921205998519244731367)
        ·
          refine ⟨155900881808997778867097051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103933921205998519244731367 155900881808997778867097051)
          ·
            refine ⟨233851322713496668300645577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155900881808997778867097051 233851322713496668300645577)
            ·
              refine ⟨175388492035122501225484183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233851322713496668300645577 175388492035122501225484183)
              ·
                refine ⟨263082738052683751838226275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175388492035122501225484183 263082738052683751838226275)
                ·
                  refine ⟨394624107079025627757339413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263082738052683751838226275 394624107079025627757339413)
                  ·
                    refine ⟨18498005019329326301125285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 394624107079025627757339413 18498005019329326301125285)
                    ·
                      refine ⟨3468375941124248681460991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18498005019329326301125285 3468375941124248681460991)
                      ·
                        rfl

theorem cell23_6754638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_6754638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754638 prefixEnd_6754638 := by exact prefixLift 6754638
  have htrace : WordTrace (prefixWord ++ tailWord_6754638) baseStart_6754638 baseEnd_6754638 := by
    simpa [prefixWord, tailWord_6754638, baseEnd_6754638] using wordTrace_append hprefix tailTrace_6754638
  have hstable : (prefixWord ++ tailWord_6754638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754638).length < 2 ^ (prefixWord ++ tailWord_6754638).sum := by decide
  have hdescent : baseEnd_6754638 < baseStart_6754638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754654 : List Nat := [4, 4, 2, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_6754654 : Nat := 118140960795 + 6754654 * 2 ^ 59
def prefixEnd_6754654 : Nat := 4983230072969 + 3 ^ 40 * 6754654 * 2
def baseEnd_6754654 : Nat := 3468384156814720618860919

theorem tailTrace_6754654 : CollatzResearch.WordTrace tailWord_6754654 prefixEnd_6754654 3468384156814720618860919 := by
  unfold tailWord_6754654
  simp only [CollatzResearch.WordTrace]
  refine ⟨30795308858881204488159877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164241647247366423936852677 30795308858881204488159877)
  ·
    refine ⟨5774120411040225841529977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30795308858881204488159877 5774120411040225841529977)
    ·
      refine ⟨4330590308280169381147483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5774120411040225841529977 4330590308280169381147483)
      ·
        refine ⟨6495885462420254071721225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4330590308280169381147483 6495885462420254071721225)
        ·
          refine ⟨4871914096815190553790919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6495885462420254071721225 4871914096815190553790919)
          ·
            refine ⟨7307871145222785830686379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4871914096815190553790919 7307871145222785830686379)
            ·
              refine ⟨10961806717834178746029569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7307871145222785830686379 10961806717834178746029569)
              ·
                refine ⟨8221355038375634059522177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10961806717834178746029569 8221355038375634059522177)
                ·
                  refine ⟨6166016278781725544641633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8221355038375634059522177 6166016278781725544641633)
                  ·
                    refine ⟨4624512209086294158481225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6166016278781725544641633 4624512209086294158481225)
                    ·
                      refine ⟨3468384156814720618860919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624512209086294158481225 3468384156814720618860919)
                      ·
                        rfl

theorem cell23_6754654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_6754654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754654 prefixEnd_6754654 := by exact prefixLift 6754654
  have htrace : WordTrace (prefixWord ++ tailWord_6754654) baseStart_6754654 baseEnd_6754654 := by
    simpa [prefixWord, tailWord_6754654, baseEnd_6754654] using wordTrace_append hprefix tailTrace_6754654
  have hstable : (prefixWord ++ tailWord_6754654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754654).length < 2 ^ (prefixWord ++ tailWord_6754654).sum := by decide
  have hdescent : baseEnd_6754654 < baseStart_6754654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754675 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 7, 1, 3]
def baseStart_6754675 : Nat := 118140960795 + 6754675 * 2 ^ 59
def prefixEnd_6754675 : Nat := 4983230072969 + 3 ^ 40 * 6754675 * 2
def baseEnd_6754675 : Nat := 3468394939908465036698321

theorem tailTrace_6754675 : CollatzResearch.WordTrace tailWord_6754675 prefixEnd_6754675 3468394939908465036698321 := by
  unfold tailWord_6754675
  simp only [CollatzResearch.WordTrace]
  refine ⟨246363236803973556491793479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164242157869315704327862319 246363236803973556491793479)
  ·
    refine ⟨369544855205960334737690219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246363236803973556491793479 369544855205960334737690219)
    ·
      refine ⟨554317282808940502106535329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369544855205960334737690219 554317282808940502106535329)
      ·
        refine ⟨415737962106705376579901497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554317282808940502106535329 415737962106705376579901497)
        ·
          refine ⟨311803471580029032434926123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415737962106705376579901497 311803471580029032434926123)
          ·
            refine ⟨467705207370043548652389185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311803471580029032434926123 467705207370043548652389185)
            ·
              refine ⟨350778905527532661489291889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467705207370043548652389185 350778905527532661489291889)
              ·
                refine ⟨263084179145649496116968917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350778905527532661489291889 263084179145649496116968917)
                ·
                  refine ⟨6166035448726160065241459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 263084179145649496116968917 6166035448726160065241459)
                  ·
                    refine ⟨9249053173089240097862189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6166035448726160065241459 9249053173089240097862189)
                    ·
                      refine ⟨3468394939908465036698321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9249053173089240097862189 3468394939908465036698321)
                      ·
                        rfl

theorem cell23_6754675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 1, 3].length) (baseStart_6754675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754675 prefixEnd_6754675 := by exact prefixLift 6754675
  have htrace : WordTrace (prefixWord ++ tailWord_6754675) baseStart_6754675 baseEnd_6754675 := by
    simpa [prefixWord, tailWord_6754675, baseEnd_6754675] using wordTrace_append hprefix tailTrace_6754675
  have hstable : (prefixWord ++ tailWord_6754675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754675).length < 2 ^ (prefixWord ++ tailWord_6754675).sum := by decide
  have hdescent : baseEnd_6754675 < baseStart_6754675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754692 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_6754692 : Nat := 118140960795 + 6754692 * 2 ^ 59
def prefixEnd_6754692 : Nat := 4983230072969 + 3 ^ 40 * 6754692 * 2
def baseEnd_6754692 : Nat := 3468403669079591470185743

theorem tailTrace_6754692 : CollatzResearch.WordTrace tailWord_6754692 prefixEnd_6754692 3468403669079591470185743 := by
  unfold tailWord_6754692
  simp only [CollatzResearch.WordTrace]
  refine ⟨123181928422455984197581165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164242571229941312263441553 123181928422455984197581165)
  ·
    refine ⟨46193223158420994074092937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123181928422455984197581165 46193223158420994074092937)
    ·
      refine ⟨34644917368815745555569703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46193223158420994074092937 34644917368815745555569703)
      ·
        refine ⟨51967376053223618333354555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34644917368815745555569703 51967376053223618333354555)
        ·
          refine ⟨77951064079835427500031833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51967376053223618333354555 77951064079835427500031833)
          ·
            refine ⟨58463298059876570625023875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77951064079835427500031833 58463298059876570625023875)
            ·
              refine ⟨87694947089814855937535813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58463298059876570625023875 87694947089814855937535813)
              ·
                refine ⟨16442802579340285488287965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87694947089814855937535813 16442802579340285488287965)
                ·
                  refine ⟨6166050967252607058107987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16442802579340285488287965 6166050967252607058107987)
                  ·
                    refine ⟨9249076450878910587161981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6166050967252607058107987 9249076450878910587161981)
                    ·
                      refine ⟨3468403669079591470185743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9249076450878910587161981 3468403669079591470185743)
                      ·
                        rfl

theorem cell23_6754692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_6754692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754692 prefixEnd_6754692 := by exact prefixLift 6754692
  have htrace : WordTrace (prefixWord ++ tailWord_6754692) baseStart_6754692 baseEnd_6754692 := by
    simpa [prefixWord, tailWord_6754692, baseEnd_6754692] using wordTrace_append hprefix tailTrace_6754692
  have hstable : (prefixWord ++ tailWord_6754692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754692).length < 2 ^ (prefixWord ++ tailWord_6754692).sum := by decide
  have hdescent : baseEnd_6754692 < baseStart_6754692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754712 : List Nat := [2, 1, 2, 5, 1, 1, 2, 3, 1, 5]
def baseStart_6754712 : Nat := 118140960795 + 6754712 * 2 ^ 59
def prefixEnd_6754712 : Nat := 4983230072969 + 3 ^ 40 * 6754712 * 2
def baseEnd_6754712 : Nat := 1156137979564227130645217

theorem tailTrace_6754712 : CollatzResearch.WordTrace tailWord_6754712 prefixEnd_6754712 1156137979564227130645217 := by
  unfold tailWord_6754712
  simp only [CollatzResearch.WordTrace]
  refine ⟨123182293152419755905445195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164243057536559674540593593 123182293152419755905445195)
  ·
    refine ⟨184773439728629633858167793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123182293152419755905445195 184773439728629633858167793)
    ·
      refine ⟨138580079796472225393625845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184773439728629633858167793 138580079796472225393625845)
      ·
        refine ⟨12991882480919271130652423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138580079796472225393625845 12991882480919271130652423)
        ·
          refine ⟨19487823721378906695978635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12991882480919271130652423 19487823721378906695978635)
          ·
            refine ⟨29231735582068360043967953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19487823721378906695978635 29231735582068360043967953)
            ·
              refine ⟨21923801686551270032975965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29231735582068360043967953 21923801686551270032975965)
              ·
                refine ⟨8221425632456726262365987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21923801686551270032975965 8221425632456726262365987)
                ·
                  refine ⟨12332138448685089393548981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8221425632456726262365987 12332138448685089393548981)
                  ·
                    refine ⟨1156137979564227130645217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12332138448685089393548981 1156137979564227130645217)
                    ·
                      rfl

theorem cell23_6754712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_6754712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754712 prefixEnd_6754712 := by exact prefixLift 6754712
  have htrace : WordTrace (prefixWord ++ tailWord_6754712) baseStart_6754712 baseEnd_6754712 := by
    simpa [prefixWord, tailWord_6754712, baseEnd_6754712] using wordTrace_append hprefix tailTrace_6754712
  have hstable : (prefixWord ++ tailWord_6754712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754712).length < 2 ^ (prefixWord ++ tailWord_6754712).sum := by decide
  have hdescent : baseEnd_6754712 < baseStart_6754712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754725 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 4, 4]
def baseStart_6754725 : Nat := 118140960795 + 6754725 * 2 ^ 59
def prefixEnd_6754725 : Nat := 4983230072969 + 3 ^ 40 * 6754725 * 2
def baseEnd_6754725 : Nat := 1156140204647063280357697

theorem tailTrace_6754725 : CollatzResearch.WordTrace tailWord_6754725 prefixEnd_6754725 1156140204647063280357697 := by
  unfold tailWord_6754725
  simp only [CollatzResearch.WordTrace]
  refine ⟨246365060453792415031113629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164243373635861610020742419 246365060453792415031113629)
  ·
    refine ⟨92386897670172155636667611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246365060453792415031113629 92386897670172155636667611)
    ·
      refine ⟨138580346505258233455001417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92386897670172155636667611 138580346505258233455001417)
      ·
        refine ⟨103935259878943675091251063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138580346505258233455001417 103935259878943675091251063)
        ·
          refine ⟨155902889818415512636876595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103935259878943675091251063 155902889818415512636876595)
          ·
            refine ⟨233854334727623268955314893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155902889818415512636876595 233854334727623268955314893)
            ·
              refine ⟨87695375522858725858243085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233854334727623268955314893 87695375522858725858243085)
              ·
                refine ⟨32885765821072022196841157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87695375522858725858243085 32885765821072022196841157)
                ·
                  refine ⟨6166081091451004161907717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32885765821072022196841157 6166081091451004161907717)
                  ·
                    refine ⟨1156140204647063280357697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6166081091451004161907717 1156140204647063280357697)
                    ·
                      rfl

theorem cell23_6754725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_6754725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754725 prefixEnd_6754725 := by exact prefixLift 6754725
  have htrace : WordTrace (prefixWord ++ tailWord_6754725) baseStart_6754725 baseEnd_6754725 := by
    simpa [prefixWord, tailWord_6754725, baseEnd_6754725] using wordTrace_append hprefix tailTrace_6754725
  have hstable : (prefixWord ++ tailWord_6754725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754725).length < 2 ^ (prefixWord ++ tailWord_6754725).sum := by decide
  have hdescent : baseEnd_6754725 < baseStart_6754725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754745 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 6]
def baseStart_6754745 : Nat := 118140960795 + 6754745 * 2 ^ 59
def prefixEnd_6754745 : Nat := 4983230072969 + 3 ^ 40 * 6754745 * 2
def baseEnd_6754745 : Nat := 3468430883554279762822999

theorem tailTrace_6754745 : CollatzResearch.WordTrace tailWord_6754745 prefixEnd_6754745 3468430883554279762822999 := by
  unfold tailWord_6754745
  simp only [CollatzResearch.WordTrace]
  refine ⟨246365789913719958446841689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164243859942479972297894459 246365789913719958446841689)
  ·
    refine ⟨184774342435289968835131267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246365789913719958446841689 184774342435289968835131267)
    ·
      refine ⟨277161513652934953252696901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184774342435289968835131267 277161513652934953252696901)
      ·
        refine ⟨51967783809925303734880669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277161513652934953252696901 51967783809925303734880669)
        ·
          refine ⟨19487918928721988900580251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51967783809925303734880669 19487918928721988900580251)
          ·
            refine ⟨29231878393082983350870377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19487918928721988900580251 29231878393082983350870377)
            ·
              refine ⟨21923908794812237513152783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29231878393082983350870377 21923908794812237513152783)
              ·
                refine ⟨32885863192218356269729175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21923908794812237513152783 32885863192218356269729175)
                ·
                  refine ⟨49328794788327534404593763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32885863192218356269729175 49328794788327534404593763)
                  ·
                    refine ⟨73993192182491301606890645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49328794788327534404593763 73993192182491301606890645)
                    ·
                      refine ⟨3468430883554279762822999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73993192182491301606890645 3468430883554279762822999)
                      ·
                        rfl

theorem cell23_6754745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_6754745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754745 prefixEnd_6754745 := by exact prefixLift 6754745
  have htrace : WordTrace (prefixWord ++ tailWord_6754745) baseStart_6754745 baseEnd_6754745 := by
    simpa [prefixWord, tailWord_6754745, baseEnd_6754745] using wordTrace_append hprefix tailTrace_6754745
  have hstable : (prefixWord ++ tailWord_6754745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754745).length < 2 ^ (prefixWord ++ tailWord_6754745).sum := by decide
  have hdescent : baseEnd_6754745 < baseStart_6754745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754749 : List Nat := [1, 4, 1, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_6754749 : Nat := 118140960795 + 6754749 * 2 ^ 59
def prefixEnd_6754749 : Nat := 4983230072969 + 3 ^ 40 * 6754749 * 2
def baseEnd_6754749 : Nat := 3468432937476897747172981

theorem tailTrace_6754749 : CollatzResearch.WordTrace tailWord_6754749 prefixEnd_6754749 3468432937476897747172981 := by
  unfold tailWord_6754749
  simp only [CollatzResearch.WordTrace]
  refine ⟨246365935805705467129987301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164243957203803644753324867 246365935805705467129987301)
  ·
    refine ⟨46193612963569775086872619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246365935805705467129987301 46193612963569775086872619)
    ·
      refine ⟨69290419445354662630308929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46193612963569775086872619 69290419445354662630308929)
      ·
        refine ⟨51967814584015996972731697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69290419445354662630308929 51967814584015996972731697)
        ·
          refine ⟨38975860938011997729548773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51967814584015996972731697 38975860938011997729548773)
          ·
            refine ⟨7307973925877249574290395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38975860938011997729548773 7307973925877249574290395)
            ·
              refine ⟨10961960888815874361435593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7307973925877249574290395 10961960888815874361435593)
              ·
                refine ⟨8221470666611905771076695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10961960888815874361435593 8221470666611905771076695)
                ·
                  refine ⟨12332205999917858656615043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8221470666611905771076695 12332205999917858656615043)
                  ·
                    refine ⟨18498308999876787984922565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12332205999917858656615043 18498308999876787984922565)
                    ·
                      refine ⟨3468432937476897747172981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18498308999876787984922565 3468432937476897747172981)
                      ·
                        rfl

theorem cell23_6754749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_6754749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754749 prefixEnd_6754749 := by exact prefixLift 6754749
  have htrace : WordTrace (prefixWord ++ tailWord_6754749) baseStart_6754749 baseEnd_6754749 := by
    simpa [prefixWord, tailWord_6754749, baseEnd_6754749] using wordTrace_append hprefix tailTrace_6754749
  have hstable : (prefixWord ++ tailWord_6754749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754749).length < 2 ^ (prefixWord ++ tailWord_6754749).sum := by decide
  have hdescent : baseEnd_6754749 < baseStart_6754749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754766 : List Nat := [4, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2]
def baseStart_6754766 : Nat := 118140960795 + 6754766 * 2 ^ 59
def prefixEnd_6754766 : Nat := 4983230072969 + 3 ^ 40 * 6754766 * 2
def baseEnd_6754766 : Nat := 3468441666648024180660403

theorem tailTrace_6754766 : CollatzResearch.WordTrace tailWord_6754766 prefixEnd_6754766 3468441666648024180660403 := by
  unfold tailWord_6754766
  simp only [CollatzResearch.WordTrace]
  refine ⟨30795819480830484879169519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164244370564429252688904101 30795819480830484879169519)
  ·
    refine ⟨46193729221245727318754279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30795819480830484879169519 46193729221245727318754279)
    ·
      refine ⟨69290593831868590978131419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46193729221245727318754279 69290593831868590978131419)
      ·
        refine ⟨103935890747802886467197129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69290593831868590978131419 103935890747802886467197129)
        ·
          refine ⟨77951918060852164850397847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103935890747802886467197129 77951918060852164850397847)
          ·
            refine ⟨116927877091278247275596771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77951918060852164850397847 116927877091278247275596771)
            ·
              refine ⟨175391815636917370913395157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116927877091278247275596771 175391815636917370913395157)
              ·
                refine ⟨4110745678990250880782699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 175391815636917370913395157 4110745678990250880782699)
                ·
                  refine ⟨6166118518485376321174049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110745678990250880782699 6166118518485376321174049)
                  ·
                    refine ⟨4624588888864032240880537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6166118518485376321174049 4624588888864032240880537)
                    ·
                      refine ⟨3468441666648024180660403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624588888864032240880537 3468441666648024180660403)
                      ·
                        rfl

theorem cell23_6754766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_6754766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754766 prefixEnd_6754766 := by exact prefixLift 6754766
  have htrace : WordTrace (prefixWord ++ tailWord_6754766) baseStart_6754766 baseEnd_6754766 := by
    simpa [prefixWord, tailWord_6754766, baseEnd_6754766] using wordTrace_append hprefix tailTrace_6754766
  have hstable : (prefixWord ++ tailWord_6754766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754766).length < 2 ^ (prefixWord ++ tailWord_6754766).sum := by decide
  have hdescent : baseEnd_6754766 < baseStart_6754766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754768 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 3, 9]
def baseStart_6754768 : Nat := 118140960795 + 6754768 * 2 ^ 59
def prefixEnd_6754768 : Nat := 4983230072969 + 3 ^ 40 * 6754768 * 2
def baseEnd_6754768 : Nat := 1156147564536444390945131

theorem tailTrace_6754768 : CollatzResearch.WordTrace tailWord_6754768 prefixEnd_6754768 1156147564536444390945131 := by
  unfold tailWord_6754768
  simp only [CollatzResearch.WordTrace]
  refine ⟨123183314396318316687464479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164244419195091088916619305 123183314396318316687464479)
  ·
    refine ⟨184774971594477475031196719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123183314396318316687464479 184774971594477475031196719)
    ·
      refine ⟨277162457391716212546795079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184774971594477475031196719 277162457391716212546795079)
      ·
        refine ⟨415743686087574318820192619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277162457391716212546795079 415743686087574318820192619)
        ·
          refine ⟨623615529131361478230288929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415743686087574318820192619 623615529131361478230288929)
          ·
            refine ⟨467711646848521108672716697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623615529131361478230288929 467711646848521108672716697)
            ·
              refine ⟨350783735136390831504537523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467711646848521108672716697 350783735136390831504537523)
              ·
                refine ⟨526175602704586247256806285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350783735136390831504537523 526175602704586247256806285)
                ·
                  refine ⟨197315851014219842721302357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526175602704586247256806285 197315851014219842721302357)
                  ·
                    refine ⟨1156147564536444390945131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 197315851014219842721302357 1156147564536444390945131)
                    ·
                      rfl

theorem cell23_6754768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_6754768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754768 prefixEnd_6754768 := by exact prefixLift 6754768
  have htrace : WordTrace (prefixWord ++ tailWord_6754768) baseStart_6754768 baseEnd_6754768 := by
    simpa [prefixWord, tailWord_6754768, baseEnd_6754768] using wordTrace_append hprefix tailTrace_6754768
  have hstable : (prefixWord ++ tailWord_6754768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754768).length < 2 ^ (prefixWord ++ tailWord_6754768).sum := by decide
  have hdescent : baseEnd_6754768 < baseStart_6754768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754783 : List Nat := [1, 1, 2, 3, 3, 2, 4, 2, 1, 2, 2]
def baseStart_6754783 : Nat := 118140960795 + 6754783 * 2 ^ 59
def prefixEnd_6754783 : Nat := 4983230072969 + 3 ^ 40 * 6754783 * 2
def baseEnd_6754783 : Nat := 3468450395819150614147825

theorem tailTrace_6754783 : CollatzResearch.WordTrace tailWord_6754783 prefixEnd_6754783 3468450395819150614147825 := by
  unfold tailWord_6754783
  simp only [CollatzResearch.WordTrace]
  refine ⟨246367175887582290936725003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164244783925054860624483335 246367175887582290936725003)
  ·
    refine ⟨369550763831373436405087505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246367175887582290936725003 369550763831373436405087505)
    ·
      refine ⟨277163072873530077303815629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369550763831373436405087505 277163072873530077303815629)
      ·
        refine ⟨103936152327573778988930861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277163072873530077303815629 103936152327573778988930861)
        ·
          refine ⟨38976057122840167120849073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103936152327573778988930861 38976057122840167120849073)
          ·
            refine ⟨29232042842130125340636805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38976057122840167120849073 29232042842130125340636805)
            ·
              refine ⟨5481008032899398501369401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29232042842130125340636805 5481008032899398501369401)
              ·
                refine ⟨4110756024674548876027051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5481008032899398501369401 4110756024674548876027051)
                ·
                  refine ⟨6166134037011823314040577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110756024674548876027051 6166134037011823314040577)
                  ·
                    refine ⟨4624600527758867485530433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6166134037011823314040577 4624600527758867485530433)
                    ·
                      refine ⟨3468450395819150614147825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624600527758867485530433 3468450395819150614147825)
                      ·
                        rfl

theorem cell23_6754783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_6754783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754783 prefixEnd_6754783 := by exact prefixLift 6754783
  have htrace : WordTrace (prefixWord ++ tailWord_6754783) baseStart_6754783 baseEnd_6754783 := by
    simpa [prefixWord, tailWord_6754783, baseEnd_6754783] using wordTrace_append hprefix tailTrace_6754783
  have hstable : (prefixWord ++ tailWord_6754783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754783).length < 2 ^ (prefixWord ++ tailWord_6754783).sum := by decide
  have hdescent : baseEnd_6754783 < baseStart_6754783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754789 : List Nat := [1, 3, 1, 5, 3, 1, 1, 8]
def baseStart_6754789 : Nat := 118140960795 + 6754789 * 2 ^ 59
def prefixEnd_6754789 : Nat := 4983230072969 + 3 ^ 40 * 6754789 * 2
def baseEnd_6754789 : Nat := 128461239877891762617511

theorem tailTrace_6754789 : CollatzResearch.WordTrace tailWord_6754789 prefixEnd_6754789 128461239877891762617511 := by
  unfold tailWord_6754789
  simp only [CollatzResearch.WordTrace]
  refine ⟨246367394725560553961443421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164244929817040369307628947 246367394725560553961443421)
  ·
    refine ⟨92387773022085207735541283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246367394725560553961443421 92387773022085207735541283)
    ·
      refine ⟨138581659533127811603311925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92387773022085207735541283 138581659533127811603311925)
      ·
        refine ⟨12992030581230732337810493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138581659533127811603311925 12992030581230732337810493)
        ·
          refine ⟨4872011467961524626678935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12992030581230732337810493 4872011467961524626678935)
          ·
            refine ⟨7308017201942286940018403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4872011467961524626678935 7308017201942286940018403)
            ·
              refine ⟨10962025802913430410027605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7308017201942286940018403 10962025802913430410027605)
              ·
                refine ⟨128461239877891762617511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10962025802913430410027605 128461239877891762617511)
                ·
                  rfl

theorem cell23_6754789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 8].length) (baseStart_6754789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754789 prefixEnd_6754789 := by exact prefixLift 6754789
  have htrace : WordTrace (prefixWord ++ tailWord_6754789) baseStart_6754789 baseEnd_6754789 := by
    simpa [prefixWord, tailWord_6754789, baseEnd_6754789] using wordTrace_append hprefix tailTrace_6754789
  have hstable : (prefixWord ++ tailWord_6754789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754789).length < 2 ^ (prefixWord ++ tailWord_6754789).sum := by decide
  have hdescent : baseEnd_6754789 < baseStart_6754789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754825 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 1, 6, 3]
def baseStart_6754825 : Nat := 118140960795 + 6754825 * 2 ^ 59
def prefixEnd_6754825 : Nat := 4983230072969 + 3 ^ 40 * 6754825 * 2
def baseEnd_6754825 : Nat := 3468471962006639449822631

theorem tailTrace_6754825 : CollatzResearch.WordTrace tailWord_6754825 prefixEnd_6754825 3468471962006639449822631 := by
  unfold tailWord_6754825
  simp only [CollatzResearch.WordTrace]
  refine ⟨246368707753430132109753929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164245805168953421406502619 246368707753430132109753929)
  ·
    refine ⟨184776530815072599082315447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246368707753430132109753929 184776530815072599082315447)
    ·
      refine ⟨277164796222608898623473171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184776530815072599082315447 277164796222608898623473171)
      ·
        refine ⟨415747194333913347935209757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277164796222608898623473171 415747194333913347935209757)
        ·
          refine ⟨155905197875217505475703659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415747194333913347935209757 155905197875217505475703659)
          ·
            refine ⟨233857796812826258213555489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155905197875217505475703659 233857796812826258213555489)
            ·
              refine ⟨175393347609619693660166617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233857796812826258213555489 175393347609619693660166617)
              ·
                refine ⟨131545010707214770245124963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175393347609619693660166617 131545010707214770245124963)
                ·
                  refine ⟨197317516060822155367687445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131545010707214770245124963 197317516060822155367687445)
                  ·
                    refine ⟨9249258565351038532860349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 197317516060822155367687445 9249258565351038532860349)
                    ·
                      refine ⟨3468471962006639449822631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9249258565351038532860349 3468471962006639449822631)
                      ·
                        rfl

theorem cell23_6754825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 6, 3].length) (baseStart_6754825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754825 prefixEnd_6754825 := by exact prefixLift 6754825
  have htrace : WordTrace (prefixWord ++ tailWord_6754825) baseStart_6754825 baseEnd_6754825 := by
    simpa [prefixWord, tailWord_6754825, baseEnd_6754825] using wordTrace_append hprefix tailTrace_6754825
  have hstable : (prefixWord ++ tailWord_6754825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754825).length < 2 ^ (prefixWord ++ tailWord_6754825).sum := by decide
  have hdescent : baseEnd_6754825 < baseStart_6754825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754835 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 4]
def baseStart_6754835 : Nat := 118140960795 + 6754835 * 2 ^ 59
def prefixEnd_6754835 : Nat := 4983230072969 + 3 ^ 40 * 6754835 * 2
def baseEnd_6754835 : Nat := 3468477096813184410697585

theorem tailTrace_6754835 : CollatzResearch.WordTrace tailWord_6754835 prefixEnd_6754835 3468477096813184410697585 := by
  unfold tailWord_6754835
  simp only [CollatzResearch.WordTrace]
  refine ⟨246369072483393903817617959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164246048322262602545078639 246369072483393903817617959)
  ·
    refine ⟨369553608725090855726426939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246369072483393903817617959 369553608725090855726426939)
    ·
      refine ⟨554330413087636283589640409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369553608725090855726426939 554330413087636283589640409)
      ·
        refine ⟨415747809815727212692230307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554330413087636283589640409 415747809815727212692230307)
        ·
          refine ⟨623621714723590819038345461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415747809815727212692230307 623621714723590819038345461)
          ·
            refine ⟨58464535755336639284844887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 623621714723590819038345461 58464535755336639284844887)
            ·
              refine ⟨87696803633004958927267331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58464535755336639284844887 87696803633004958927267331)
              ·
                refine ⟨131545205449507438390900997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87696803633004958927267331 131545205449507438390900997)
                ·
                  refine ⟨24664726021782644698293937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131545205449507438390900997 24664726021782644698293937)
                  ·
                    refine ⟨18498544516336983523720453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24664726021782644698293937 18498544516336983523720453)
                    ·
                      refine ⟨3468477096813184410697585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18498544516336983523720453 3468477096813184410697585)
                      ·
                        rfl

theorem cell23_6754835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_6754835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754835 prefixEnd_6754835 := by exact prefixLift 6754835
  have htrace : WordTrace (prefixWord ++ tailWord_6754835) baseStart_6754835 baseEnd_6754835 := by
    simpa [prefixWord, tailWord_6754835, baseEnd_6754835] using wordTrace_append hprefix tailTrace_6754835
  have hstable : (prefixWord ++ tailWord_6754835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754835).length < 2 ^ (prefixWord ++ tailWord_6754835).sum := by decide
  have hdescent : baseEnd_6754835 < baseStart_6754835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754856 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_6754856 : Nat := 118140960795 + 6754856 * 2 ^ 59
def prefixEnd_6754856 : Nat := 4983230072969 + 3 ^ 40 * 6754856 * 2
def baseEnd_6754856 : Nat := 3468487879906928828534989

theorem tailTrace_6754856 : CollatzResearch.WordTrace tailWord_6754856 prefixEnd_6754856 3468487879906928828534989 := by
  unfold tailWord_6754856
  simp only [CollatzResearch.WordTrace]
  refine ⟨123184919208158912202066211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164246558944211882936088281 123184919208158912202066211)
  ·
    refine ⟨184777378812238368303099317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123184919208158912202066211 184777378812238368303099317)
    ·
      refine ⟨17322879263647347028415561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184777378812238368303099317 17322879263647347028415561)
      ·
        refine ⟨12992159447735510271311671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17322879263647347028415561 12992159447735510271311671)
        ·
          refine ⟨19488239171603265406967507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12992159447735510271311671 19488239171603265406967507)
          ·
            refine ⟨29232358757404898110451261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19488239171603265406967507 29232358757404898110451261)
            ·
              refine ⟨10962134534026836791419223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29232358757404898110451261 10962134534026836791419223)
              ·
                refine ⟨16443201801040255187128835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10962134534026836791419223 16443201801040255187128835)
                ·
                  refine ⟨24664802701560382780693253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16443201801040255187128835 24664802701560382780693253)
                  ·
                    refine ⟨4624650506542571771379985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24664802701560382780693253 4624650506542571771379985)
                    ·
                      refine ⟨3468487879906928828534989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624650506542571771379985 3468487879906928828534989)
                      ·
                        rfl

theorem cell23_6754856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_6754856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754856 prefixEnd_6754856 := by exact prefixLift 6754856
  have htrace : WordTrace (prefixWord ++ tailWord_6754856) baseStart_6754856 baseEnd_6754856 := by
    simpa [prefixWord, tailWord_6754856, baseEnd_6754856] using wordTrace_append hprefix tailTrace_6754856
  have hstable : (prefixWord ++ tailWord_6754856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754856).length < 2 ^ (prefixWord ++ tailWord_6754856).sum := by decide
  have hdescent : baseEnd_6754856 < baseStart_6754856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754892 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 2, 5]
def baseStart_6754892 : Nat := 118140960795 + 6754892 * 2 ^ 59
def prefixEnd_6754892 : Nat := 4983230072969 + 3 ^ 40 * 6754892 * 2
def baseEnd_6754892 : Nat := 1156168788403496895894941

theorem tailTrace_6754892 : CollatzResearch.WordTrace tailWord_6754892 prefixEnd_6754892 1156168788403496895894941 := by
  unfold tailWord_6754892
  simp only [CollatzResearch.WordTrace]
  refine ⟨123185575722093701276221465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164247434296124935034961953 123185575722093701276221465)
  ·
    refine ⟨92389181791570275957166099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123185575722093701276221465 92389181791570275957166099)
    ·
      refine ⟨138583772687355413935749149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92389181791570275957166099 138583772687355413935749149)
      ·
        refine ⟨51968914757758280225905931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138583772687355413935749149 51968914757758280225905931)
        ·
          refine ⟨77953372136637420338858897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51968914757758280225905931 77953372136637420338858897)
          ·
            refine ⟨58465029102478065254144173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77953372136637420338858897 58465029102478065254144173)
            ·
              refine ⟨21924385913429274470304065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58465029102478065254144173 21924385913429274470304065)
              ·
                refine ⟨16443289435071955852728049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21924385913429274470304065 16443289435071955852728049)
                ·
                  refine ⟨12332467076303966889546037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16443289435071955852728049 12332467076303966889546037)
                  ·
                    refine ⟨1156168788403496895894941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12332467076303966889546037 1156168788403496895894941)
                    ·
                      rfl

theorem cell23_6754892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_6754892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754892 prefixEnd_6754892 := by exact prefixLift 6754892
  have htrace : WordTrace (prefixWord ++ tailWord_6754892) baseStart_6754892 baseEnd_6754892 := by
    simpa [prefixWord, tailWord_6754892, baseEnd_6754892] using wordTrace_append hprefix tailTrace_6754892
  have hstable : (prefixWord ++ tailWord_6754892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754892).length < 2 ^ (prefixWord ++ tailWord_6754892).sum := by decide
  have hdescent : baseEnd_6754892 < baseStart_6754892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754935 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 10]
def baseStart_6754935 : Nat := 118140960795 + 6754935 * 2 ^ 59
def prefixEnd_6754935 : Nat := 4983230072969 + 3 ^ 40 * 6754935 * 2
def baseEnd_6754935 : Nat := 385392049430959335494125

theorem tailTrace_6754935 : CollatzResearch.WordTrace tailWord_6754935 prefixEnd_6754935 385392049430959335494125 := by
  unfold tailWord_6754935
  simp only [CollatzResearch.WordTrace]
  refine ⟨246372719783031620896258259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164248479855354413930838839 246372719783031620896258259)
  ·
    refine ⟨369559079674547431344387389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246372719783031620896258259 369559079674547431344387389)
    ·
      refine ⟨138584654877955286754145271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369559079674547431344387389 138584654877955286754145271)
      ·
        refine ⟨207876982316932930131217907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138584654877955286754145271 207876982316932930131217907)
        ·
          refine ⟨311815473475399395196826861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207876982316932930131217907 311815473475399395196826861)
          ·
            refine ⟨116930802553274773198810073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311815473475399395196826861 116930802553274773198810073)
            ·
              refine ⟨87698101914956079899107555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116930802553274773198810073 87698101914956079899107555)
              ·
                refine ⟨131547152872434119848661333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87698101914956079899107555 131547152872434119848661333)
                ·
                  refine ⟨385392049430959335494125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 131547152872434119848661333 385392049430959335494125)
                  ·
                    rfl

theorem cell23_6754935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 10].length) (baseStart_6754935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754935 prefixEnd_6754935 := by exact prefixLift 6754935
  have htrace : WordTrace (prefixWord ++ tailWord_6754935) baseStart_6754935 baseEnd_6754935 := by
    simpa [prefixWord, tailWord_6754935, baseEnd_6754935] using wordTrace_append hprefix tailTrace_6754935
  have hstable : (prefixWord ++ tailWord_6754935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754935).length < 2 ^ (prefixWord ++ tailWord_6754935).sum := by decide
  have hdescent : baseEnd_6754935 < baseStart_6754935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754949 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 2, 2, 3]
def baseStart_6754949 : Nat := 118140960795 + 6754949 * 2 ^ 59
def prefixEnd_6754949 : Nat := 4983230072969 + 3 ^ 40 * 6754949 * 2
def baseEnd_6754949 : Nat := 3468535633607796964672061

theorem tailTrace_6754949 : CollatzResearch.WordTrace tailWord_6754949 prefixEnd_6754949 3468535633607796964672061 := by
  unfold tailWord_6754949
  simp only [CollatzResearch.WordTrace]
  refine ⟨246373230404980901287267901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164248820269987267524845267 246373230404980901287267901)
  ·
    refine ⟨92389961401867837982725463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246373230404980901287267901 92389961401867837982725463)
    ·
      refine ⟨138584942102801756974088195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92389961401867837982725463 138584942102801756974088195)
      ·
        refine ⟨207877413154202635461132293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138584942102801756974088195 207877413154202635461132293)
        ·
          refine ⟨38977014966412994148962305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207877413154202635461132293 38977014966412994148962305)
          ·
            refine ⟨29232761224809745611721729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38977014966412994148962305 29232761224809745611721729)
            ·
              refine ⟨21924570918607309208791297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29232761224809745611721729 21924570918607309208791297)
              ·
                refine ⟨16443428188955481906593473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21924570918607309208791297 16443428188955481906593473)
                ·
                  refine ⟨12332571141716611429945105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16443428188955481906593473 12332571141716611429945105)
                  ·
                    refine ⟨9249428356287458572458829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12332571141716611429945105 9249428356287458572458829)
                    ·
                      refine ⟨3468535633607796964672061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9249428356287458572458829 3468535633607796964672061)
                      ·
                        rfl

theorem cell23_6754949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_6754949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754949 prefixEnd_6754949 := by exact prefixLift 6754949
  have htrace : WordTrace (prefixWord ++ tailWord_6754949) baseStart_6754949 baseEnd_6754949 := by
    simpa [prefixWord, tailWord_6754949, baseEnd_6754949] using wordTrace_append hprefix tailTrace_6754949
  have hstable : (prefixWord ++ tailWord_6754949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754949).length < 2 ^ (prefixWord ++ tailWord_6754949).sum := by decide
  have hdescent : baseEnd_6754949 < baseStart_6754949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6754990 : List Nat := [4, 1, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_6754990 : Nat := 118140960795 + 6754990 * 2 ^ 59
def prefixEnd_6754990 : Nat := 4983230072969 + 3 ^ 40 * 6754990 * 2
def baseEnd_6754990 : Nat := 1156185562104877101419791

theorem tailTrace_6754990 : CollatzResearch.WordTrace tailWord_6754990 prefixEnd_6754990 1156185562104877101419791 := by
  unfold tailWord_6754990
  simp only [CollatzResearch.WordTrace]
  refine ⟨30796840724729045661188803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164249817198554910193006949 30796840724729045661188803)
  ·
    refine ⟨46195261087093568491783205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30796840724729045661188803 46195261087093568491783205)
    ·
      refine ⟨8661611453830044092209351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46195261087093568491783205 8661611453830044092209351)
      ·
        refine ⟨12992417180745066138314027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8661611453830044092209351 12992417180745066138314027)
        ·
          refine ⟨19488625771117599207471041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12992417180745066138314027 19488625771117599207471041)
          ·
            refine ⟨14616469328338199405603281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19488625771117599207471041 14616469328338199405603281)
            ·
              refine ⟨10962351996253649554202461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14616469328338199405603281 10962351996253649554202461)
              ·
                refine ⟨4110881998595118582825923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10962351996253649554202461 4110881998595118582825923)
                ·
                  refine ⟨6166322997892677874238885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110881998595118582825923 6166322997892677874238885)
                  ·
                    refine ⟨1156185562104877101419791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6166322997892677874238885 1156185562104877101419791)
                    ·
                      rfl

theorem cell23_6754990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_6754990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6754990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6754990 prefixEnd_6754990 := by exact prefixLift 6754990
  have htrace : WordTrace (prefixWord ++ tailWord_6754990) baseStart_6754990 baseEnd_6754990 := by
    simpa [prefixWord, tailWord_6754990, baseEnd_6754990] using wordTrace_append hprefix tailTrace_6754990
  have hstable : (prefixWord ++ tailWord_6754990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6754990).length < 2 ^ (prefixWord ++ tailWord_6754990).sum := by decide
  have hdescent : baseEnd_6754990 < baseStart_6754990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6754990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755006 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_6755006 : Nat := 118140960795 + 6755006 * 2 ^ 59
def prefixEnd_6755006 : Nat := 4983230072969 + 3 ^ 40 * 6755006 * 2
def baseEnd_6755006 : Nat := 3468564902005103241659299

theorem tailTrace_6755006 : CollatzResearch.WordTrace tailWord_6755006 prefixEnd_6755006 3468564902005103241659299 := by
  unfold tailWord_6755006
  simp only [CollatzResearch.WordTrace]
  refine ⟨30796913670721800002761609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164250206243849600014728581 30796913670721800002761609)
  ·
    refine ⟨23097685253041350002071207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30796913670721800002761609 23097685253041350002071207)
    ·
      refine ⟨34646527879562025003106811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23097685253041350002071207 34646527879562025003106811)
      ·
        refine ⟨51969791819343037504660217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34646527879562025003106811 51969791819343037504660217)
        ·
          refine ⟨38977343864507278128495163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51969791819343037504660217 38977343864507278128495163)
          ·
            refine ⟨58466015796760917192742745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38977343864507278128495163 58466015796760917192742745)
            ·
              refine ⟨43849511847570687894557059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58466015796760917192742745 43849511847570687894557059)
              ·
                refine ⟨65774267771356031841835589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43849511847570687894557059 65774267771356031841835589)
                ·
                  refine ⟨12332675207129255970344173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65774267771356031841835589 12332675207129255970344173)
                  ·
                    refine ⟨4624753202673470988879065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12332675207129255970344173 4624753202673470988879065)
                    ·
                      refine ⟨3468564902005103241659299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624753202673470988879065 3468564902005103241659299)
                      ·
                        rfl

theorem cell23_6755006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_6755006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755006 prefixEnd_6755006 := by exact prefixLift 6755006
  have htrace : WordTrace (prefixWord ++ tailWord_6755006) baseStart_6755006 baseEnd_6755006 := by
    simpa [prefixWord, tailWord_6755006, baseEnd_6755006] using wordTrace_append hprefix tailTrace_6755006
  have hstable : (prefixWord ++ tailWord_6755006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755006).length < 2 ^ (prefixWord ++ tailWord_6755006).sum := by decide
  have hdescent : baseEnd_6755006 < baseStart_6755006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755070 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_6755070 : Nat := 118140960795 + 6755070 * 2 ^ 59
def prefixEnd_6755070 : Nat := 4983230072969 + 3 ^ 40 * 6755070 * 2
def baseEnd_6755070 : Nat := 3468597764766990991259005

theorem tailTrace_6755070 : CollatzResearch.WordTrace tailWord_6755070 prefixEnd_6755070 3468597764766990991259005 := by
  unfold tailWord_6755070
  simp only [CollatzResearch.WordTrace]
  refine ⟨30797205454692817369052833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164251762425028359301615109 30797205454692817369052833)
  ·
    refine ⟨23097904091019613026789625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30797205454692817369052833 23097904091019613026789625)
    ·
      refine ⟨17323428068264709770092219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23097904091019613026789625 17323428068264709770092219)
      ·
        refine ⟨25985142102397064655138329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17323428068264709770092219 25985142102397064655138329)
        ·
          refine ⟨19488856576797798491353747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25985142102397064655138329 19488856576797798491353747)
          ·
            refine ⟨29233284865196697737030621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19488856576797798491353747 29233284865196697737030621)
            ·
              refine ⟨10962481824448761651386483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29233284865196697737030621 10962481824448761651386483)
              ·
                refine ⟨16443722736673142477079725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10962481824448761651386483 16443722736673142477079725)
                ·
                  refine ⟨6166396026252428428904897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16443722736673142477079725 6166396026252428428904897)
                  ·
                    refine ⟨4624797019689321321678673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6166396026252428428904897 4624797019689321321678673)
                    ·
                      refine ⟨3468597764766990991259005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624797019689321321678673 3468597764766990991259005)
                      ·
                        rfl

theorem cell23_6755070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_6755070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755070 prefixEnd_6755070 := by exact prefixLift 6755070
  have htrace : WordTrace (prefixWord ++ tailWord_6755070) baseStart_6755070 baseEnd_6755070 := by
    simpa [prefixWord, tailWord_6755070, baseEnd_6755070] using wordTrace_append hprefix tailTrace_6755070
  have hstable : (prefixWord ++ tailWord_6755070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755070).length < 2 ^ (prefixWord ++ tailWord_6755070).sum := by decide
  have hdescent : baseEnd_6755070 < baseStart_6755070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755139 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 4]
def baseStart_6755139 : Nat := 118140960795 + 6755139 * 2 ^ 59
def prefixEnd_6755139 : Nat := 4983230072969 + 3 ^ 40 * 6755139 * 2
def baseEnd_6755139 : Nat := 3468633194932151221296187

theorem tailTrace_6755139 : CollatzResearch.WordTrace tailWord_6755139 prefixEnd_6755139 3468633194932151221296187 := by
  unfold tailWord_6755139
  simp only [CollatzResearch.WordTrace]
  refine ⟨246380160274292563736684471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164253440182861709157789647 246380160274292563736684471)
  ·
    refine ⟨369570240411438845605026707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246380160274292563736684471 369570240411438845605026707)
    ·
      refine ⟨554355360617158268407540061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369570240411438845605026707 554355360617158268407540061)
      ·
        refine ⟨207883260231434350652827523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 554355360617158268407540061 207883260231434350652827523)
        ·
          refine ⟨311824890347151525979241285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207883260231434350652827523 311824890347151525979241285)
          ·
            refine ⟨58467166940090911121107741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311824890347151525979241285 58467166940090911121107741)
            ·
              refine ⟨21925187602534091670415403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58467166940090911121107741 21925187602534091670415403)
              ·
                refine ⟨32887781403801137505623105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21925187602534091670415403 32887781403801137505623105)
                ·
                  refine ⟨24665836052850853129217329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32887781403801137505623105 24665836052850853129217329)
                  ·
                    refine ⟨18499377039638139846912997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24665836052850853129217329 18499377039638139846912997)
                    ·
                      refine ⟨3468633194932151221296187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18499377039638139846912997 3468633194932151221296187)
                      ·
                        rfl

theorem cell23_6755139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_6755139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755139 prefixEnd_6755139 := by exact prefixLift 6755139
  have htrace : WordTrace (prefixWord ++ tailWord_6755139) baseStart_6755139 baseEnd_6755139 := by
    simpa [prefixWord, tailWord_6755139, baseEnd_6755139] using wordTrace_append hprefix tailTrace_6755139
  have hstable : (prefixWord ++ tailWord_6755139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755139).length < 2 ^ (prefixWord ++ tailWord_6755139).sum := by decide
  have hdescent : baseEnd_6755139 < baseStart_6755139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755176 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_6755176 : Nat := 118140960795 + 6755176 * 2 ^ 59
def prefixEnd_6755176 : Nat := 4983230072969 + 3 ^ 40 * 6755176 * 2
def baseEnd_6755176 : Nat := 3468652193716367576533517

theorem tailTrace_6755176 : CollatzResearch.WordTrace tailWord_6755176 prefixEnd_6755176 3468652193716367576533517 := by
  unfold tailWord_6755176
  simp only [CollatzResearch.WordTrace]
  refine ⟨123190754887579259527890691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164254339850105679370520921 123190754887579259527890691)
  ·
    refine ⟨184786132331368889291836037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123190754887579259527890691 184786132331368889291836037)
    ·
      refine ⟨34647399812131666742219257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184786132331368889291836037 34647399812131666742219257)
      ·
        refine ⟨25985549859098750056664443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34647399812131666742219257 25985549859098750056664443)
        ·
          refine ⟨38978324788648125084996665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25985549859098750056664443 38978324788648125084996665)
          ·
            refine ⟨29233743591486093813747499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38978324788648125084996665 29233743591486093813747499)
            ·
              refine ⟨43850615387229140720621249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29233743591486093813747499 43850615387229140720621249)
              ·
                refine ⟨32887961540421855540465937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43850615387229140720621249 32887961540421855540465937)
                ·
                  refine ⟨24665971155316391655349453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32887961540421855540465937 24665971155316391655349453)
                  ·
                    refine ⟨9249739183243646870756045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24665971155316391655349453 9249739183243646870756045)
                    ·
                      refine ⟨3468652193716367576533517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9249739183243646870756045 3468652193716367576533517)
                      ·
                        rfl

theorem cell23_6755176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_6755176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755176 prefixEnd_6755176 := by exact prefixLift 6755176
  have htrace : WordTrace (prefixWord ++ tailWord_6755176) baseStart_6755176 baseEnd_6755176 := by
    simpa [prefixWord, tailWord_6755176, baseEnd_6755176] using wordTrace_append hprefix tailTrace_6755176
  have hstable : (prefixWord ++ tailWord_6755176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755176).length < 2 ^ (prefixWord ++ tailWord_6755176).sum := by decide
  have hdescent : baseEnd_6755176 < baseStart_6755176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755179 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 2, 5]
def baseStart_6755179 : Nat := 118140960795 + 6755179 * 2 ^ 59
def prefixEnd_6755179 : Nat := 4983230072969 + 3 ^ 40 * 6755179 * 2
def baseEnd_6755179 : Nat := 1156217911386110354932001

theorem tailTrace_6755179 : CollatzResearch.WordTrace tailWord_6755179 prefixEnd_6755179 1156217911386110354932001 := by
  unfold tailWord_6755179
  simp only [CollatzResearch.WordTrace]
  refine ⟨246381619194147650568140591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164254412796098433712093727 246381619194147650568140591)
  ·
    refine ⟨369572428791221475852210887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246381619194147650568140591 369572428791221475852210887)
    ·
      refine ⟨554358643186832213778316331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369572428791221475852210887 554358643186832213778316331)
      ·
        refine ⟨831537964780248320667474497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554358643186832213778316331 831537964780248320667474497)
        ·
          refine ⟨623653473585186240500605873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831537964780248320667474497 623653473585186240500605873)
          ·
            refine ⟨467740105188889680375454405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623653473585186240500605873 467740105188889680375454405)
            ·
              refine ⟨87701269722916815070397701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 467740105188889680375454405 87701269722916815070397701)
              ·
                refine ⟨16443988073046902825699569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87701269722916815070397701 16443988073046902825699569)
                ·
                  refine ⟨12332991054785177119274677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16443988073046902825699569 12332991054785177119274677)
                  ·
                    refine ⟨1156217911386110354932001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12332991054785177119274677 1156217911386110354932001)
                    ·
                      rfl

theorem cell23_6755179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 5].length) (baseStart_6755179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755179 prefixEnd_6755179 := by exact prefixLift 6755179
  have htrace : WordTrace (prefixWord ++ tailWord_6755179) baseStart_6755179 baseEnd_6755179 := by
    simpa [prefixWord, tailWord_6755179, baseEnd_6755179] using wordTrace_append hprefix tailTrace_6755179
  have hstable : (prefixWord ++ tailWord_6755179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755179).length < 2 ^ (prefixWord ++ tailWord_6755179).sum := by decide
  have hdescent : baseEnd_6755179 < baseStart_6755179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755186 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 1, 7, 2]
def baseStart_6755186 : Nat := 118140960795 + 6755186 * 2 ^ 59
def prefixEnd_6755186 : Nat := 4983230072969 + 3 ^ 40 * 6755186 * 2
def baseEnd_6755186 : Nat := 3468657328522912537408471

theorem tailTrace_6755186 : CollatzResearch.WordTrace tailWord_6755186 prefixEnd_6755186 3468657328522912537408471 := by
  unfold tailWord_6755186
  simp only [CollatzResearch.WordTrace]
  refine ⟨61595468626280572690911353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164254583003414860509096941 61595468626280572690911353)
  ·
    refine ⟨46196601469710429518183515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61595468626280572690911353 46196601469710429518183515)
    ·
      refine ⟨69294902204565644277275273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46196601469710429518183515 69294902204565644277275273)
      ·
        refine ⟨51971176653424233207956455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69294902204565644277275273 51971176653424233207956455)
        ·
          refine ⟨77956764980136349811934683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51971176653424233207956455 77956764980136349811934683)
          ·
            refine ⟨116935147470204524717902025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77956764980136349811934683 116935147470204524717902025)
            ·
              refine ⟨87701360602653393538426519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116935147470204524717902025 87701360602653393538426519)
              ·
                refine ⟨131552040903980090307639779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87701360602653393538426519 131552040903980090307639779)
                ·
                  refine ⟨197328061355970135461459669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131552040903980090307639779 197328061355970135461459669)
                  ·
                    refine ⟨4624876438030550049877961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 197328061355970135461459669 4624876438030550049877961)
                    ·
                      refine ⟨3468657328522912537408471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4624876438030550049877961 3468657328522912537408471)
                      ·
                        rfl

theorem cell23_6755186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_6755186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755186 prefixEnd_6755186 := by exact prefixLift 6755186
  have htrace : WordTrace (prefixWord ++ tailWord_6755186) baseStart_6755186 baseEnd_6755186 := by
    simpa [prefixWord, tailWord_6755186, baseEnd_6755186] using wordTrace_append hprefix tailTrace_6755186
  have hstable : (prefixWord ++ tailWord_6755186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755186).length < 2 ^ (prefixWord ++ tailWord_6755186).sum := by decide
  have hdescent : baseEnd_6755186 < baseStart_6755186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755199 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 4]
def baseStart_6755199 : Nat := 118140960795 + 6755199 * 2 ^ 59
def prefixEnd_6755199 : Nat := 4983230072969 + 3 ^ 40 * 6755199 * 2
def baseEnd_6755199 : Nat := 3468664003771420986545911

theorem tailTrace_6755199 : CollatzResearch.WordTrace tailWord_6755199 prefixEnd_6755199 3468664003771420986545911 := by
  unfold tailWord_6755199
  simp only [CollatzResearch.WordTrace]
  refine ⟨246382348654075193983868651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164254899102716795989245767 246382348654075193983868651)
  ·
    refine ⟨369573522981112790975802977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246382348654075193983868651 369573522981112790975802977)
    ·
      refine ⟨277180142235834593231852233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369573522981112790975802977 277180142235834593231852233)
      ·
        refine ⟨207885106676875944923889175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277180142235834593231852233 207885106676875944923889175)
        ·
          refine ⟨311827660015313917385833763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207885106676875944923889175 311827660015313917385833763)
          ·
            refine ⟨467741490022970876078750645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311827660015313917385833763 467741490022970876078750645)
            ·
              refine ⟨43850764689653519632382873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 467741490022970876078750645 43850764689653519632382873)
              ·
                refine ⟨32888073517240139724287155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43850764689653519632382873 32888073517240139724287155)
                ·
                  refine ⟨49332110275860209586430733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32888073517240139724287155 49332110275860209586430733)
                  ·
                    refine ⟨18499541353447578594911525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49332110275860209586430733 18499541353447578594911525)
                    ·
                      refine ⟨3468664003771420986545911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18499541353447578594911525 3468664003771420986545911)
                      ·
                        rfl

theorem cell23_6755199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_6755199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755199 prefixEnd_6755199 := by exact prefixLift 6755199
  have htrace : WordTrace (prefixWord ++ tailWord_6755199) baseStart_6755199 baseEnd_6755199 := by
    simpa [prefixWord, tailWord_6755199, baseEnd_6755199] using wordTrace_append hprefix tailTrace_6755199
  have hstable : (prefixWord ++ tailWord_6755199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755199).length < 2 ^ (prefixWord ++ tailWord_6755199).sum := by decide
  have hdescent : baseEnd_6755199 < baseStart_6755199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755233 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6755233 : Nat := 118140960795 + 6755233 * 2 ^ 59
def prefixEnd_6755233 : Nat := 4983230072969 + 3 ^ 40 * 6755233 * 2
def baseEnd_6755233 : Nat := 3468681462113673853520755

theorem tailTrace_6755233 : CollatzResearch.WordTrace tailWord_6755233 prefixEnd_6755233 3468681462113673853520755 := by
  unfold tailWord_6755233
  simp only [CollatzResearch.WordTrace]
  refine ⟨246383588735952017790606353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164255725823968011860404235 246383588735952017790606353)
  ·
    refine ⟨184787691551964013342954765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246383588735952017790606353 184787691551964013342954765)
    ·
      refine ⟨69295384331986505003608037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184787691551964013342954765 69295384331986505003608037)
      ·
        refine ⟨12992884562247469688176507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69295384331986505003608037 12992884562247469688176507)
        ·
          refine ⟨19489326843371204532264761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12992884562247469688176507 19489326843371204532264761)
          ·
            refine ⟨14616995132528403399198571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19489326843371204532264761 14616995132528403399198571)
            ·
              refine ⟨21925492698792605098797857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14616995132528403399198571 21925492698792605098797857)
              ·
                refine ⟨16444119524094453824098393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21925492698792605098797857 16444119524094453824098393)
                ·
                  refine ⟨12333089643070840368073795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16444119524094453824098393 12333089643070840368073795)
                  ·
                    refine ⟨18499634464606260552110693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12333089643070840368073795 18499634464606260552110693)
                    ·
                      refine ⟨3468681462113673853520755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18499634464606260552110693 3468681462113673853520755)
                      ·
                        rfl

theorem cell23_6755233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6755233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755233 prefixEnd_6755233 := by exact prefixLift 6755233
  have htrace : WordTrace (prefixWord ++ tailWord_6755233) baseStart_6755233 baseEnd_6755233 := by
    simpa [prefixWord, tailWord_6755233, baseEnd_6755233] using wordTrace_append hprefix tailTrace_6755233
  have hstable : (prefixWord ++ tailWord_6755233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755233).length < 2 ^ (prefixWord ++ tailWord_6755233).sum := by decide
  have hdescent : baseEnd_6755233 < baseStart_6755233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755256 : List Nat := [2, 1, 2, 1, 2, 5, 1, 3, 6]
def baseStart_6755256 : Nat := 118140960795 + 6755256 * 2 ^ 59
def prefixEnd_6755256 : Nat := 4983230072969 + 3 ^ 40 * 6755256 * 2
def baseEnd_6755256 : Nat := 385410363574303029281461

theorem tailTrace_6755256 : CollatzResearch.WordTrace tailWord_6755256 prefixEnd_6755256 385410363574303029281461 := by
  unfold tailWord_6755256
  simp only [CollatzResearch.WordTrace]
  refine ⟨123192213807434346359346811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164256285076579128479129081 123192213807434346359346811)
  ·
    refine ⟨184788320711151519539020217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123192213807434346359346811 184788320711151519539020217)
    ·
      refine ⟨138591240533363639654265163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184788320711151519539020217 138591240533363639654265163)
      ·
        refine ⟨207886860800045459481397745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138591240533363639654265163 207886860800045459481397745)
        ·
          refine ⟨155915145600034094611048309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207886860800045459481397745 155915145600034094611048309)
          ·
            refine ⟨14617044900003196369785779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155915145600034094611048309 14617044900003196369785779)
            ·
              refine ⟨21925567350004794554678669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14617044900003196369785779 21925567350004794554678669)
              ·
                refine ⟨8222087756251797958004501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21925567350004794554678669 8222087756251797958004501)
                ·
                  refine ⟨385410363574303029281461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8222087756251797958004501 385410363574303029281461)
                  ·
                    rfl

theorem cell23_6755256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 6].length) (baseStart_6755256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755256 prefixEnd_6755256 := by exact prefixLift 6755256
  have htrace : WordTrace (prefixWord ++ tailWord_6755256) baseStart_6755256 baseEnd_6755256 := by
    simpa [prefixWord, tailWord_6755256, baseEnd_6755256] using wordTrace_append hprefix tailTrace_6755256
  have hstable : (prefixWord ++ tailWord_6755256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755256).length < 2 ^ (prefixWord ++ tailWord_6755256).sum := by decide
  have hdescent : baseEnd_6755256 < baseStart_6755256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755340 : List Nat := [2, 2, 1, 2, 3, 2, 4, 1, 1, 1, 4]
def baseStart_6755340 : Nat := 118140960795 + 6755340 * 2 ^ 59
def prefixEnd_6755340 : Nat := 4983230072969 + 3 ^ 40 * 6755340 * 2
def baseEnd_6755340 : Nat := 3468736404543704934882763

theorem tailTrace_6755340 : CollatzResearch.WordTrace tailWord_6755340 prefixEnd_6755340 3468736404543704934882763 := by
  unfold tailWord_6755340
  simp only [CollatzResearch.WordTrace]
  refine ⟨123193745673282187532375737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164258327564376250043167649 123193745673282187532375737)
  ·
    refine ⟨92395309254961640649281803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123193745673282187532375737 92395309254961640649281803)
    ·
      refine ⟨138592963882442460973922705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92395309254961640649281803 138592963882442460973922705)
      ·
        refine ⟨103944722911831845730442029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138592963882442460973922705 103944722911831845730442029)
        ·
          refine ⟨38979271091936942148915761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103944722911831845730442029 38979271091936942148915761)
          ·
            refine ⟨29234453318952706611686821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38979271091936942148915761 29234453318952706611686821)
            ·
              refine ⟨5481459997303632489691279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29234453318952706611686821 5481459997303632489691279)
              ·
                refine ⟨8222189995955448734536919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5481459997303632489691279 8222189995955448734536919)
                ·
                  refine ⟨12333284993933173101805379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8222189995955448734536919 12333284993933173101805379)
                  ·
                    refine ⟨18499927490899759652708069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12333284993933173101805379 18499927490899759652708069)
                    ·
                      refine ⟨3468736404543704934882763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18499927490899759652708069 3468736404543704934882763)
                      ·
                        rfl

theorem cell23_6755340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_6755340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755340 prefixEnd_6755340 := by exact prefixLift 6755340
  have htrace : WordTrace (prefixWord ++ tailWord_6755340) baseStart_6755340 baseEnd_6755340 := by
    simpa [prefixWord, tailWord_6755340, baseEnd_6755340] using wordTrace_append hprefix tailTrace_6755340
  have hstable : (prefixWord ++ tailWord_6755340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755340).length < 2 ^ (prefixWord ++ tailWord_6755340).sum := by decide
  have hdescent : baseEnd_6755340 < baseStart_6755340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755360 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6755360 : Nat := 118140960795 + 6755360 * 2 ^ 59
def prefixEnd_6755360 : Nat := 4983230072969 + 3 ^ 40 * 6755360 * 2
def baseEnd_6755360 : Nat := 3468746674156794856632671

theorem tailTrace_6755360 : CollatzResearch.WordTrace tailWord_6755360 prefixEnd_6755360 3468746674156794856632671 := by
  unfold tailWord_6755360
  simp only [CollatzResearch.WordTrace]
  refine ⟨123194110403245959240239767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164258813870994612320319689 123194110403245959240239767)
  ·
    refine ⟨184791165604868938860359651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123194110403245959240239767 184791165604868938860359651)
    ·
      refine ⟨277186748407303408290539477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184791165604868938860359651 277186748407303408290539477)
      ·
        refine ⟨6496564415796173631809519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 277186748407303408290539477 6496564415796173631809519)
        ·
          refine ⟨9744846623694260447714279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6496564415796173631809519 9744846623694260447714279)
          ·
            refine ⟨14617269935541390671571419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9744846623694260447714279 14617269935541390671571419)
            ·
              refine ⟨21925904903312086007357129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14617269935541390671571419 21925904903312086007357129)
              ·
                refine ⟨16444428677484064505517847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21925904903312086007357129 16444428677484064505517847)
                ·
                  refine ⟨24666643016226096758276771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16444428677484064505517847 24666643016226096758276771)
                  ·
                    refine ⟨36999964524339145137415157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24666643016226096758276771 36999964524339145137415157)
                    ·
                      refine ⟨3468746674156794856632671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36999964524339145137415157 3468746674156794856632671)
                      ·
                        rfl

theorem cell23_6755360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6755360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755360 prefixEnd_6755360 := by exact prefixLift 6755360
  have htrace : WordTrace (prefixWord ++ tailWord_6755360) baseStart_6755360 baseEnd_6755360 := by
    simpa [prefixWord, tailWord_6755360, baseEnd_6755360] using wordTrace_append hprefix tailTrace_6755360
  have hstable : (prefixWord ++ tailWord_6755360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755360).length < 2 ^ (prefixWord ++ tailWord_6755360).sum := by decide
  have hdescent : baseEnd_6755360 < baseStart_6755360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755380 : List Nat := [2, 5, 1, 2, 1, 1, 4, 7]
def baseStart_6755380 : Nat := 118140960795 + 6755380 * 2 ^ 59
def prefixEnd_6755380 : Nat := 4983230072969 + 3 ^ 40 * 6755380 * 2
def baseEnd_6755380 : Nat := 128472479398884621421577

theorem tailTrace_6755380 : CollatzResearch.WordTrace tailWord_6755380 prefixEnd_6755380 128472479398884621421577 := by
  unfold tailWord_6755380
  simp only [CollatzResearch.WordTrace]
  refine ⟨123194475133209730948103797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164259300177612974597471729 123194475133209730948103797)
  ·
    refine ⟨11549482043738412276384731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123194475133209730948103797 11549482043738412276384731)
    ·
      refine ⟨17324223065607618414577097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11549482043738412276384731 17324223065607618414577097)
      ·
        refine ⟨12993167299205713810932823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17324223065607618414577097 12993167299205713810932823)
        ·
          refine ⟨19489750948808570716399235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12993167299205713810932823 19489750948808570716399235)
          ·
            refine ⟨29234626423212856074598853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19489750948808570716399235 29234626423212856074598853)
            ·
              refine ⟨5481492454352410513987285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29234626423212856074598853 5481492454352410513987285)
              ·
                refine ⟨128472479398884621421577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5481492454352410513987285 128472479398884621421577)
                ·
                  rfl

theorem cell23_6755380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 7].length) (baseStart_6755380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755380 prefixEnd_6755380 := by exact prefixLift 6755380
  have htrace : WordTrace (prefixWord ++ tailWord_6755380) baseStart_6755380 baseEnd_6755380 := by
    simpa [prefixWord, tailWord_6755380, baseEnd_6755380] using wordTrace_append hprefix tailTrace_6755380
  have hstable : (prefixWord ++ tailWord_6755380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755380).length < 2 ^ (prefixWord ++ tailWord_6755380).sum := by decide
  have hdescent : baseEnd_6755380 < baseStart_6755380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755386 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_6755386 : Nat := 118140960795 + 6755386 * 2 ^ 59
def prefixEnd_6755386 : Nat := 4983230072969 + 3 ^ 40 * 6755386 * 2
def baseEnd_6755386 : Nat := 3468760024653811754907551

theorem tailTrace_6755386 : CollatzResearch.WordTrace tailWord_6755386 prefixEnd_6755386 3468760024653811754907551 := by
  unfold tailWord_6755386
  simp only [CollatzResearch.WordTrace]
  refine ⟨61597292276099431230231503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164259446069598483280617341 61597292276099431230231503)
  ·
    refine ⟨92395938414149146845347255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61597292276099431230231503 92395938414149146845347255)
    ·
      refine ⟨138593907621223720268020883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92395938414149146845347255 138593907621223720268020883)
      ·
        refine ⟨207890861431835580402031325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138593907621223720268020883 207890861431835580402031325)
        ·
          refine ⟨77959073036938342650761747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207890861431835580402031325 77959073036938342650761747)
          ·
            refine ⟨116938609555407513976142621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77959073036938342650761747 116938609555407513976142621)
            ·
              refine ⟨43851978583277817741053483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116938609555407513976142621 43851978583277817741053483)
              ·
                refine ⟨65777967874916726611580225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43851978583277817741053483 65777967874916726611580225)
                ·
                  refine ⟨49333475906187544958685169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65777967874916726611580225 49333475906187544958685169)
                  ·
                    refine ⟨37000106929640658719013877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49333475906187544958685169 37000106929640658719013877)
                    ·
                      refine ⟨3468760024653811754907551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37000106929640658719013877 3468760024653811754907551)
                      ·
                        rfl

theorem cell23_6755386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_6755386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755386 prefixEnd_6755386 := by exact prefixLift 6755386
  have htrace : WordTrace (prefixWord ++ tailWord_6755386) baseStart_6755386 baseEnd_6755386 := by
    simpa [prefixWord, tailWord_6755386, baseEnd_6755386] using wordTrace_append hprefix tailTrace_6755386
  have hstable : (prefixWord ++ tailWord_6755386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755386).length < 2 ^ (prefixWord ++ tailWord_6755386).sum := by decide
  have hdescent : baseEnd_6755386 < baseStart_6755386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755400 : List Nat := [2, 1, 3, 1, 1, 1, 3, 5, 1, 3, 2]
def baseStart_6755400 : Nat := 118140960795 + 6755400 * 2 ^ 59
def prefixEnd_6755400 : Nat := 4983230072969 + 3 ^ 40 * 6755400 * 2
def baseEnd_6755400 : Nat := 3468767213382974700132487

theorem tailTrace_6755400 : CollatzResearch.WordTrace tailWord_6755400 prefixEnd_6755400 3468767213382974700132487 := by
  unfold tailWord_6755400
  simp only [CollatzResearch.WordTrace]
  refine ⟨123194839863173502655967827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164259786484231336874623769 123194839863173502655967827)
  ·
    refine ⟨184792259794760253983951741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123194839863173502655967827 184792259794760253983951741)
    ·
      refine ⟨69297097423035095243981903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184792259794760253983951741 69297097423035095243981903)
      ·
        refine ⟨103945646134552642865972855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69297097423035095243981903 103945646134552642865972855)
        ·
          refine ⟨155918469201828964298959283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103945646134552642865972855 155918469201828964298959283)
          ·
            refine ⟨233877703802743446448438925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155918469201828964298959283 233877703802743446448438925)
            ·
              refine ⟨87704138926028792418164597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233877703802743446448438925 87704138926028792418164597)
              ·
                refine ⟨8222263024315199289202931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87704138926028792418164597 8222263024315199289202931)
                ·
                  refine ⟨12333394536472798933804397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8222263024315199289202931 12333394536472798933804397)
                  ·
                    refine ⟨4625022951177299600176649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12333394536472798933804397 4625022951177299600176649)
                    ·
                      refine ⟨3468767213382974700132487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4625022951177299600176649 3468767213382974700132487)
                      ·
                        rfl

theorem cell23_6755400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_6755400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755400 prefixEnd_6755400 := by exact prefixLift 6755400
  have htrace : WordTrace (prefixWord ++ tailWord_6755400) baseStart_6755400 baseEnd_6755400 := by
    simpa [prefixWord, tailWord_6755400, baseEnd_6755400] using wordTrace_append hprefix tailTrace_6755400
  have hstable : (prefixWord ++ tailWord_6755400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755400).length < 2 ^ (prefixWord ++ tailWord_6755400).sum := by decide
  have hdescent : baseEnd_6755400 < baseStart_6755400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755416 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_6755416 : Nat := 118140960795 + 6755416 * 2 ^ 59
def prefixEnd_6755416 : Nat := 4983230072969 + 3 ^ 40 * 6755416 * 2
def baseEnd_6755416 : Nat := 3468775429073446637532413

theorem tailTrace_6755416 : CollatzResearch.WordTrace tailWord_6755416 prefixEnd_6755416 3468775429073446637532413 := by
  unfold tailWord_6755416
  simp only [CollatzResearch.WordTrace]
  refine ⟨123195131647144520022259051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164260175529526026696345401 123195131647144520022259051)
  ·
    refine ⟨184792697470716780033388577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123195131647144520022259051 184792697470716780033388577)
    ·
      refine ⟨138594523103037585025041433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184792697470716780033388577 138594523103037585025041433)
      ·
        refine ⟨103945892327278188768781075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138594523103037585025041433 103945892327278188768781075)
        ·
          refine ⟨155918838490917283153171613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103945892327278188768781075 155918838490917283153171613)
          ·
            refine ⟨58469564434093981182439355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155918838490917283153171613 58469564434093981182439355)
            ·
              refine ⟨87704346651140971773659033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58469564434093981182439355 87704346651140971773659033)
              ·
                refine ⟨65778259988355728830244275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87704346651140971773659033 65778259988355728830244275)
                ·
                  refine ⟨98667389982533593245366413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65778259988355728830244275 98667389982533593245366413)
                  ·
                    refine ⟨37000271243450097467012405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98667389982533593245366413 37000271243450097467012405)
                    ·
                      refine ⟨3468775429073446637532413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37000271243450097467012405 3468775429073446637532413)
                      ·
                        rfl

theorem cell23_6755416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_6755416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755416 prefixEnd_6755416 := by exact prefixLift 6755416
  have htrace : WordTrace (prefixWord ++ tailWord_6755416) baseStart_6755416 baseEnd_6755416 := by
    simpa [prefixWord, tailWord_6755416, baseEnd_6755416] using wordTrace_append hprefix tailTrace_6755416
  have hstable : (prefixWord ++ tailWord_6755416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755416).length < 2 ^ (prefixWord ++ tailWord_6755416).sum := by decide
  have hdescent : baseEnd_6755416 < baseStart_6755416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755434 : List Nat := [3, 1, 3, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_6755434 : Nat := 118140960795 + 6755434 * 2 ^ 59
def prefixEnd_6755434 : Nat := 4983230072969 + 3 ^ 40 * 6755434 * 2
def baseEnd_6755434 : Nat := 3468784671725227567107331

theorem tailTrace_6755434 : CollatzResearch.WordTrace tailWord_6755434 prefixEnd_6755434 3468784671725227567107331 := by
  unfold tailWord_6755434
  simp only [CollatzResearch.WordTrace]
  refine ⟨61597729952055957279668339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164260613205482552745782237 61597729952055957279668339)
  ·
    refine ⟨92396594928083935919502509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61597729952055957279668339 92396594928083935919502509)
    ·
      refine ⟨34648723098031475969813441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92396594928083935919502509 34648723098031475969813441)
      ·
        refine ⟨25986542323523606977360081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34648723098031475969813441 25986542323523606977360081)
        ·
          refine ⟨19489906742642705233020061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25986542323523606977360081 19489906742642705233020061)
          ·
            refine ⟨7308715028491014462382523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19489906742642705233020061 7308715028491014462382523)
            ·
              refine ⟨10963072542736521693573785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7308715028491014462382523 10963072542736521693573785)
              ·
                refine ⟨8222304407052391270180339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10963072542736521693573785 8222304407052391270180339)
                ·
                  refine ⟨12333456610578586905270509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8222304407052391270180339 12333456610578586905270509)
                  ·
                    refine ⟨4625046228966970089476441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12333456610578586905270509 4625046228966970089476441)
                    ·
                      refine ⟨3468784671725227567107331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4625046228966970089476441 3468784671725227567107331)
                      ·
                        rfl

theorem cell23_6755434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_6755434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755434 prefixEnd_6755434 := by exact prefixLift 6755434
  have htrace : WordTrace (prefixWord ++ tailWord_6755434) baseStart_6755434 baseEnd_6755434 := by
    simpa [prefixWord, tailWord_6755434, baseEnd_6755434] using wordTrace_append hprefix tailTrace_6755434
  have hstable : (prefixWord ++ tailWord_6755434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755434).length < 2 ^ (prefixWord ++ tailWord_6755434).sum := by decide
  have hdescent : baseEnd_6755434 < baseStart_6755434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755436 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 9]
def baseStart_6755436 : Nat := 118140960795 + 6755436 * 2 ^ 59
def prefixEnd_6755436 : Nat := 4983230072969 + 3 ^ 40 * 6755436 * 2
def baseEnd_6755436 : Nat := 385420633187392951031369

theorem tailTrace_6755436 : CollatzResearch.WordTrace tailWord_6755436 prefixEnd_6755436 385420633187392951031369 := by
  unfold tailWord_6755436
  simp only [CollatzResearch.WordTrace]
  refine ⟨123195496377108291730123081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164260661836144388973497441 123195496377108291730123081)
  ·
    refine ⟨92396622282831218797592311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123195496377108291730123081 92396622282831218797592311)
    ·
      refine ⟨138594933424246828196388467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92396622282831218797592311 138594933424246828196388467)
      ·
        refine ⟨207892400136370242294582701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138594933424246828196388467 207892400136370242294582701)
        ·
          refine ⟨77959650051138840860468513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207892400136370242294582701 77959650051138840860468513)
          ·
            refine ⟨58469737538354130645351385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77959650051138840860468513 58469737538354130645351385)
            ·
              refine ⟨43852303153765597984013539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58469737538354130645351385 43852303153765597984013539)
              ·
                refine ⟨65778454730648396976020309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43852303153765597984013539 65778454730648396976020309)
                ·
                  refine ⟨385420633187392951031369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65778454730648396976020309 385420633187392951031369)
                  ·
                    rfl

theorem cell23_6755436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_6755436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755436 prefixEnd_6755436 := by exact prefixLift 6755436
  have htrace : WordTrace (prefixWord ++ tailWord_6755436) baseStart_6755436 baseEnd_6755436 := by
    simpa [prefixWord, tailWord_6755436, baseEnd_6755436] using wordTrace_append hprefix tailTrace_6755436
  have hstable : (prefixWord ++ tailWord_6755436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755436).length < 2 ^ (prefixWord ++ tailWord_6755436).sum := by decide
  have hdescent : baseEnd_6755436 < baseStart_6755436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755463 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_6755463 : Nat := 118140960795 + 6755463 * 2 ^ 59
def prefixEnd_6755463 : Nat := 4983230072969 + 3 ^ 40 * 6755463 * 2
def baseEnd_6755463 : Nat := 3468799562664207953644697

theorem tailTrace_6755463 : CollatzResearch.WordTrace tailWord_6755463 prefixEnd_6755463 3468799562664207953644697 := by
  unfold tailWord_6755463
  simp only [CollatzResearch.WordTrace]
  refine ⟨246391977525118767071479043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164261318350079178047652695 246391977525118767071479043)
  ·
    refine ⟨369587966287678150607218565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246391977525118767071479043 369587966287678150607218565)
    ·
      refine ⟨69297743678939653238853481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 369587966287678150607218565 69297743678939653238853481)
      ·
        refine ⟨51973307759204739929140111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69297743678939653238853481 51973307759204739929140111)
        ·
          refine ⟨77959961638807109893710167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51973307759204739929140111 77959961638807109893710167)
          ·
            refine ⟨116939942458210664840565251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77959961638807109893710167 116939942458210664840565251)
            ·
              refine ⟨175409913687315997260847877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116939942458210664840565251 175409913687315997260847877)
              ·
                refine ⟨32889358816371749486408977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175409913687315997260847877 32889358816371749486408977)
                ·
                  refine ⟨24667019112278812114806733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32889358816371749486408977 24667019112278812114806733)
                  ·
                    refine ⟨9250132167104554543052525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24667019112278812114806733 9250132167104554543052525)
                    ·
                      refine ⟨3468799562664207953644697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9250132167104554543052525 3468799562664207953644697)
                      ·
                        rfl

theorem cell23_6755463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_6755463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755463 prefixEnd_6755463 := by exact prefixLift 6755463
  have htrace : WordTrace (prefixWord ++ tailWord_6755463) baseStart_6755463 baseEnd_6755463 := by
    simpa [prefixWord, tailWord_6755463, baseEnd_6755463] using wordTrace_append hprefix tailTrace_6755463
  have hstable : (prefixWord ++ tailWord_6755463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755463).length < 2 ^ (prefixWord ++ tailWord_6755463).sum := by decide
  have hdescent : baseEnd_6755463 < baseStart_6755463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755480 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 2, 3, 3]
def baseStart_6755480 : Nat := 118140960795 + 6755480 * 2 ^ 59
def prefixEnd_6755480 : Nat := 4983230072969 + 3 ^ 40 * 6755480 * 2
def baseEnd_6755480 : Nat := 3468808291835334387132119

theorem tailTrace_6755480 : CollatzResearch.WordTrace tailWord_6755480 prefixEnd_6755480 3468808291835334387132119 := by
  unfold tailWord_6755480
  simp only [CollatzResearch.WordTrace]
  refine ⟨123196298783028589487423947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164261731710704785983231929 123196298783028589487423947)
  ·
    refine ⟨184794448174542884231135921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123196298783028589487423947 184794448174542884231135921)
    ·
      refine ⟨138595836130907163173351941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184794448174542884231135921 138595836130907163173351941)
      ·
        refine ⟨25986719274545093095003489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138595836130907163173351941 25986719274545093095003489)
        ·
          refine ⟨19490039455908819821252617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25986719274545093095003489 19490039455908819821252617)
          ·
            refine ⟨14617529591931614865939463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19490039455908819821252617 14617529591931614865939463)
            ·
              refine ⟨21926294387897422298909195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14617529591931614865939463 21926294387897422298909195)
              ·
                refine ⟨32889441581846133448363793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21926294387897422298909195 32889441581846133448363793)
                ·
                  refine ⟨24667081186384600086272845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32889441581846133448363793 24667081186384600086272845)
                  ·
                    refine ⟨9250155444894225032352317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24667081186384600086272845 9250155444894225032352317)
                    ·
                      refine ⟨3468808291835334387132119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9250155444894225032352317 3468808291835334387132119)
                      ·
                        rfl

theorem cell23_6755480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_6755480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755480 prefixEnd_6755480 := by exact prefixLift 6755480
  have htrace : WordTrace (prefixWord ++ tailWord_6755480) baseStart_6755480 baseEnd_6755480 := by
    simpa [prefixWord, tailWord_6755480, baseEnd_6755480] using wordTrace_append hprefix tailTrace_6755480
  have hstable : (prefixWord ++ tailWord_6755480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755480).length < 2 ^ (prefixWord ++ tailWord_6755480).sum := by decide
  have hdescent : baseEnd_6755480 < baseStart_6755480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755530 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 3, 4]
def baseStart_6755530 : Nat := 118140960795 + 6755530 * 2 ^ 59
def prefixEnd_6755530 : Nat := 4983230072969 + 3 ^ 40 * 6755530 * 2
def baseEnd_6755530 : Nat := 1156277988622686397168963

theorem tailTrace_6755530 : CollatzResearch.WordTrace tailWord_6755530 prefixEnd_6755530 1156277988622686397168963 := by
  unfold tailWord_6755530
  simp only [CollatzResearch.WordTrace]
  refine ⟨61598605303969009378542011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164262947477250691676112029 61598605303969009378542011)
  ·
    refine ⟨92397907955953514067813017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61598605303969009378542011 92397907955953514067813017)
    ·
      refine ⟨69298430966965135550859763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92397907955953514067813017 69298430966965135550859763)
      ·
        refine ⟨103947646450447703326289645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69298430966965135550859763 103947646450447703326289645)
        ·
          refine ⟨38980367418917888747358617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103947646450447703326289645 38980367418917888747358617)
          ·
            refine ⟨29235275564188416560518963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38980367418917888747358617 29235275564188416560518963)
            ·
              refine ⟨43852913346282624840778445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29235275564188416560518963 43852913346282624840778445)
              ·
                refine ⟨16444842504855984315291917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43852913346282624840778445 16444842504855984315291917)
                ·
                  refine ⟨6166815939320994118234469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16444842504855984315291917 6166815939320994118234469)
                  ·
                    refine ⟨1156277988622686397168963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6166815939320994118234469 1156277988622686397168963)
                    ·
                      rfl

theorem cell23_6755530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_6755530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755530 prefixEnd_6755530 := by exact prefixLift 6755530
  have htrace : WordTrace (prefixWord ++ tailWord_6755530) baseStart_6755530 baseEnd_6755530 := by
    simpa [prefixWord, tailWord_6755530, baseEnd_6755530] using wordTrace_append hprefix tailTrace_6755530
  have hstable : (prefixWord ++ tailWord_6755530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755530).length < 2 ^ (prefixWord ++ tailWord_6755530).sum := by decide
  have hdescent : baseEnd_6755530 < baseStart_6755530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755543 : List Nat := [1, 1, 3, 2, 1, 2, 2, 5, 6]
def baseStart_6755543 : Nat := 118140960795 + 6755543 * 2 ^ 59
def prefixEnd_6755543 : Nat := 4983230072969 + 3 ^ 40 * 6755543 * 2
def baseEnd_6755543 : Nat := 385426737901840848960481

theorem tailTrace_6755543 : CollatzResearch.WordTrace tailWord_6755543 prefixEnd_6755543 385426737901840848960481 := by
  unfold tailWord_6755543
  simp only [CollatzResearch.WordTrace]
  refine ⟨246394895364828940734391283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164263263576552627156260855 246394895364828940734391283)
  ·
    refine ⟨369592343047243411101586925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246394895364828940734391283 369592343047243411101586925)
    ·
      refine ⟨138597128642716279163095097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369592343047243411101586925 138597128642716279163095097)
      ·
        refine ⟨103947846482037209372321323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138597128642716279163095097 103947846482037209372321323)
        ·
          refine ⟨155921769723055814058481985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103947846482037209372321323 155921769723055814058481985)
          ·
            refine ⟨116941327292291860543861489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155921769723055814058481985 116941327292291860543861489)
            ·
              refine ⟨87705995469218895407896117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116941327292291860543861489 87705995469218895407896117)
              ·
                refine ⟨8222437075239271444490261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87705995469218895407896117 8222437075239271444490261)
                ·
                  refine ⟨385426737901840848960481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8222437075239271444490261 385426737901840848960481)
                  ·
                    rfl

theorem cell23_6755543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 6].length) (baseStart_6755543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755543 prefixEnd_6755543 := by exact prefixLift 6755543
  have htrace : WordTrace (prefixWord ++ tailWord_6755543) baseStart_6755543 baseEnd_6755543 := by
    simpa [prefixWord, tailWord_6755543, baseEnd_6755543] using wordTrace_append hprefix tailTrace_6755543
  have hstable : (prefixWord ++ tailWord_6755543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755543).length < 2 ^ (prefixWord ++ tailWord_6755543).sum := by decide
  have hdescent : baseEnd_6755543 < baseStart_6755543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755564 : List Nat := [2, 2, 1, 1, 2, 6, 1, 3, 1, 4]
def baseStart_6755564 : Nat := 118140960795 + 6755564 * 2 ^ 59
def prefixEnd_6755564 : Nat := 4983230072969 + 3 ^ 40 * 6755564 * 2
def baseEnd_6755564 : Nat := 1156283808070104019493911

theorem tailTrace_6755564 : CollatzResearch.WordTrace tailWord_6755564 prefixEnd_6755564 1156283808070104019493911 := by
  unfold tailWord_6755564
  simp only [CollatzResearch.WordTrace]
  refine ⟨123197830648876430660452873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164263774198501907547270497 123197830648876430660452873)
  ·
    refine ⟨92398372986657322995339655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123197830648876430660452873 92398372986657322995339655)
    ·
      refine ⟨138597559479985984493009483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92398372986657322995339655 138597559479985984493009483)
      ·
        refine ⟨207896339219978976739514225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138597559479985984493009483 207896339219978976739514225)
        ·
          refine ⟨155922254414984232554635669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207896339219978976739514225 155922254414984232554635669)
          ·
            refine ⟨7308855675702385900998547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155922254414984232554635669 7308855675702385900998547)
            ·
              refine ⟨10963283513553578851497821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7308855675702385900998547 10963283513553578851497821)
              ·
                refine ⟨4111231317582592069311683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10963283513553578851497821 4111231317582592069311683)
                ·
                  refine ⟨6166846976373888103967525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4111231317582592069311683 6166846976373888103967525)
                  ·
                    refine ⟨1156283808070104019493911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6166846976373888103967525 1156283808070104019493911)
                    ·
                      rfl

theorem cell23_6755564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_6755564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755564 prefixEnd_6755564 := by exact prefixLift 6755564
  have htrace : WordTrace (prefixWord ++ tailWord_6755564) baseStart_6755564 baseEnd_6755564 := by
    simpa [prefixWord, tailWord_6755564, baseEnd_6755564] using wordTrace_append hprefix tailTrace_6755564
  have hstable : (prefixWord ++ tailWord_6755564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755564).length < 2 ^ (prefixWord ++ tailWord_6755564).sum := by decide
  have hdescent : baseEnd_6755564 < baseStart_6755564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755587 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 3, 1, 3]
def baseStart_6755587 : Nat := 118140960795 + 6755587 * 2 ^ 59
def prefixEnd_6755587 : Nat := 4983230072969 + 3 ^ 40 * 6755587 * 2
def baseEnd_6755587 : Nat := 3468863234265365468494127

theorem tailTrace_6755587 : CollatzResearch.WordTrace tailWord_6755587 prefixEnd_6755587 3468863234265365468494127 := by
  unfold tailWord_6755587
  simp only [CollatzResearch.WordTrace]
  refine ⟨246396500176669536248993015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164264333451113024165995343 246396500176669536248993015)
  ·
    refine ⟨369594750265004304373489523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246396500176669536248993015 369594750265004304373489523)
    ·
      refine ⟨554392125397506456560234285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369594750265004304373489523 554392125397506456560234285)
      ·
        refine ⟨207897047024064921210087857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 554392125397506456560234285 207897047024064921210087857)
        ·
          refine ⟨155922785268048690907565893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207897047024064921210087857 155922785268048690907565893)
          ·
            refine ⟨29235522237759129545168605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155922785268048690907565893 29235522237759129545168605)
            ·
              refine ⟨10963320839159673579438227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29235522237759129545168605 10963320839159673579438227)
              ·
                refine ⟨16444981258739510369157341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10963320839159673579438227 16444981258739510369157341)
                ·
                  refine ⟨6166867972027316388434003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16444981258739510369157341 6166867972027316388434003)
                  ·
                    refine ⟨9250301958040974582651005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6166867972027316388434003 9250301958040974582651005)
                    ·
                      refine ⟨3468863234265365468494127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9250301958040974582651005 3468863234265365468494127)
                      ·
                        rfl

theorem cell23_6755587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_6755587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755587 prefixEnd_6755587 := by exact prefixLift 6755587
  have htrace : WordTrace (prefixWord ++ tailWord_6755587) baseStart_6755587 baseEnd_6755587 := by
    simpa [prefixWord, tailWord_6755587, baseEnd_6755587] using wordTrace_append hprefix tailTrace_6755587
  have hstable : (prefixWord ++ tailWord_6755587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755587).length < 2 ^ (prefixWord ++ tailWord_6755587).sum := by decide
  have hdescent : baseEnd_6755587 < baseStart_6755587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755620 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_6755620 : Nat := 118140960795 + 6755620 * 2 ^ 59
def prefixEnd_6755620 : Nat := 4983230072969 + 3 ^ 40 * 6755620 * 2
def baseEnd_6755620 : Nat := 1156293393042321279793825

theorem tailTrace_6755620 : CollatzResearch.WordTrace tailWord_6755620 prefixEnd_6755620 1156293393042321279793825 := by
  unfold tailWord_6755620
  simp only [CollatzResearch.WordTrace]
  refine ⟨123198851892774991442472157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164265135857033321923296209 123198851892774991442472157)
  ·
    refine ⟨46199569459790621790927059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123198851892774991442472157 46199569459790621790927059)
    ·
      refine ⟨69299354189685932686390589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46199569459790621790927059 69299354189685932686390589)
      ·
        refine ⟨25987257821132224757396471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69299354189685932686390589 25987257821132224757396471)
        ·
          refine ⟨38980886731698337136094707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25987257821132224757396471 38980886731698337136094707)
          ·
            refine ⟨58471330097547505704142061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38980886731698337136094707 58471330097547505704142061)
            ·
              refine ⟨21926748786580314639053273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58471330097547505704142061 21926748786580314639053273)
              ·
                refine ⟨16445061589935235979289955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21926748786580314639053273 16445061589935235979289955)
                ·
                  refine ⟨24667592384902853968934933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16445061589935235979289955 24667592384902853968934933)
                  ·
                    refine ⟨1156293393042321279793825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24667592384902853968934933 1156293393042321279793825)
                    ·
                      rfl

theorem cell23_6755620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_6755620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755620 prefixEnd_6755620 := by exact prefixLift 6755620
  have htrace : WordTrace (prefixWord ++ tailWord_6755620) baseStart_6755620 baseEnd_6755620 := by
    simpa [prefixWord, tailWord_6755620, baseEnd_6755620] using wordTrace_append hprefix tailTrace_6755620
  have hstable : (prefixWord ++ tailWord_6755620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755620).length < 2 ^ (prefixWord ++ tailWord_6755620).sum := by decide
  have hdescent : baseEnd_6755620 < baseStart_6755620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755624 : List Nat := [2, 1, 5, 1, 2, 2, 3, 1, 1, 5]
def baseStart_6755624 : Nat := 118140960795 + 6755624 * 2 ^ 59
def prefixEnd_6755624 : Nat := 4983230072969 + 3 ^ 40 * 6755624 * 2
def baseEnd_6755624 : Nat := 1156294077683193941243819

theorem tailTrace_6755624 : CollatzResearch.WordTrace tailWord_6755624 prefixEnd_6755624 1156294077683193941243819 := by
  unfold tailWord_6755624
  simp only [CollatzResearch.WordTrace]
  refine ⟨123198924838767745784044963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164265233118356994378726617 123198924838767745784044963)
  ·
    refine ⟨184798387258151618676067445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123198924838767745784044963 184798387258151618676067445)
    ·
      refine ⟨17324848805451714250881323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184798387258151618676067445 17324848805451714250881323)
      ·
        refine ⟨25987273208177571376321985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17324848805451714250881323 25987273208177571376321985)
        ·
          refine ⟨19490454906133178532241489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25987273208177571376321985 19490454906133178532241489)
          ·
            refine ⟨14617841179599883899181117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19490454906133178532241489 14617841179599883899181117)
            ·
              refine ⟨5481690442349956462192919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14617841179599883899181117 5481690442349956462192919)
              ·
                refine ⟨8222535663524934693289379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5481690442349956462192919 8222535663524934693289379)
                ·
                  refine ⟨12333803495287402039934069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8222535663524934693289379 12333803495287402039934069)
                  ·
                    refine ⟨1156294077683193941243819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12333803495287402039934069 1156294077683193941243819)
                    ·
                      rfl

theorem cell23_6755624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_6755624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755624 prefixEnd_6755624 := by exact prefixLift 6755624
  have htrace : WordTrace (prefixWord ++ tailWord_6755624) baseStart_6755624 baseEnd_6755624 := by
    simpa [prefixWord, tailWord_6755624, baseEnd_6755624] using wordTrace_append hprefix tailTrace_6755624
  have hstable : (prefixWord ++ tailWord_6755624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755624).length < 2 ^ (prefixWord ++ tailWord_6755624).sum := by decide
  have hdescent : baseEnd_6755624 < baseStart_6755624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755633 : List Nat := [1, 2, 2, 3, 3, 12]
def baseStart_6755633 : Nat := 118140960795 + 6755633 * 2 ^ 59
def prefixEnd_6755633 : Nat := 4983230072969 + 3 ^ 40 * 6755633 * 2
def baseEnd_6755633 : Nat := 14275254544755029993905

theorem tailTrace_6755633 : CollatzResearch.WordTrace tailWord_6755633 prefixEnd_6755633 14275254544755029993905 := by
  unfold tailWord_6755633
  simp only [CollatzResearch.WordTrace]
  refine ⟨246398177934502886105167553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164265451956335257403445035 246398177934502886105167553)
  ·
    refine ⟨184798633450877164578875665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246398177934502886105167553 184798633450877164578875665)
    ·
      refine ⟨138598975088157873434156749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184798633450877164578875665 138598975088157873434156749)
      ·
        refine ⟨51974615658059202537808781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138598975088157873434156749 51974615658059202537808781)
        ·
          refine ⟨19490480871772200951678293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51974615658059202537808781 19490480871772200951678293)
          ·
            refine ⟨14275254544755029993905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19490480871772200951678293 14275254544755029993905)
            ·
              rfl

theorem cell23_6755633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 12].length) (baseStart_6755633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755633 prefixEnd_6755633 := by exact prefixLift 6755633
  have htrace : WordTrace (prefixWord ++ tailWord_6755633) baseStart_6755633 baseEnd_6755633 := by
    simpa [prefixWord, tailWord_6755633, baseEnd_6755633] using wordTrace_append hprefix tailTrace_6755633
  have hstable : (prefixWord ++ tailWord_6755633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755633).length < 2 ^ (prefixWord ++ tailWord_6755633).sum := by decide
  have hdescent : baseEnd_6755633 < baseStart_6755633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755637 : List Nat := [1, 3, 3, 1, 2, 2, 1, 4, 2, 4]
def baseStart_6755637 : Nat := 118140960795 + 6755637 * 2 ^ 59
def prefixEnd_6755637 : Nat := 4983230072969 + 3 ^ 40 * 6755637 * 2
def baseEnd_6755637 : Nat := 1156296302766030090956299

theorem tailTrace_6755637 : CollatzResearch.WordTrace tailWord_6755637 prefixEnd_6755637 1156296302766030090956299 := by
  unfold tailWord_6755637
  simp only [CollatzResearch.WordTrace]
  refine ⟨246398323826488394788313165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164265549217658929858875443 246398323826488394788313165)
  ·
    refine ⟨92399371434933148045617437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246398323826488394788313165 92399371434933148045617437)
    ·
      refine ⟨34649764288099930517106539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92399371434933148045617437 34649764288099930517106539)
      ·
        refine ⟨51974646432149895775659809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34649764288099930517106539 51974646432149895775659809)
        ·
          refine ⟨38980984824112421831744857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51974646432149895775659809 38980984824112421831744857)
          ·
            refine ⟨29235738618084316373808643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38980984824112421831744857 29235738618084316373808643)
            ·
              refine ⟨43853607927126474560712965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29235738618084316373808643 43853607927126474560712965)
              ·
                refine ⟨8222551486336213980133681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43853607927126474560712965 8222551486336213980133681)
                ·
                  refine ⟨6166913614752160485100261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8222551486336213980133681 6166913614752160485100261)
                  ·
                    refine ⟨1156296302766030090956299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6166913614752160485100261 1156296302766030090956299)
                    ·
                      rfl

theorem cell23_6755637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_6755637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755637 prefixEnd_6755637 := by exact prefixLift 6755637
  have htrace : WordTrace (prefixWord ++ tailWord_6755637) baseStart_6755637 baseEnd_6755637 := by
    simpa [prefixWord, tailWord_6755637, baseEnd_6755637] using wordTrace_append hprefix tailTrace_6755637
  have hstable : (prefixWord ++ tailWord_6755637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755637).length < 2 ^ (prefixWord ++ tailWord_6755637).sum := by decide
  have hdescent : baseEnd_6755637 < baseStart_6755637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755653 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_6755653 : Nat := 118140960795 + 6755653 * 2 ^ 59
def prefixEnd_6755653 : Nat := 4983230072969 + 3 ^ 40 * 6755653 * 2
def baseEnd_6755653 : Nat := 3468897123988562210268823

theorem tailTrace_6755653 : CollatzResearch.WordTrace tailWord_6755653 prefixEnd_6755653 3468897123988562210268823 := by
  unfold tailWord_6755653
  simp only [CollatzResearch.WordTrace]
  refine ⟨246398907394430429520895613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164265938262953619680597075 246398907394430429520895613)
  ·
    refine ⟨92399590272911411070335855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246398907394430429520895613 92399590272911411070335855)
    ·
      refine ⟨138599385409367116605503783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92399590272911411070335855 138599385409367116605503783)
      ·
        refine ⟨207899078114050674908255675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138599385409367116605503783 207899078114050674908255675)
        ·
          refine ⟨311848617171076012362383513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207899078114050674908255675 311848617171076012362383513)
          ·
            refine ⟨233886462878307009271787635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311848617171076012362383513 233886462878307009271787635)
            ·
              refine ⟨350829694317460513907681453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233886462878307009271787635 350829694317460513907681453)
              ·
                refine ⟨131561135369047692715380545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350829694317460513907681453 131561135369047692715380545)
                ·
                  refine ⟨98670851526785769536535409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131561135369047692715380545 98670851526785769536535409)
                  ·
                    refine ⟨74003138645089327152401557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98670851526785769536535409 74003138645089327152401557)
                    ·
                      refine ⟨3468897123988562210268823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74003138645089327152401557 3468897123988562210268823)
                      ·
                        rfl

theorem cell23_6755653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_6755653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755653 prefixEnd_6755653 := by exact prefixLift 6755653
  have htrace : WordTrace (prefixWord ++ tailWord_6755653) baseStart_6755653 baseEnd_6755653 := by
    simpa [prefixWord, tailWord_6755653, baseEnd_6755653] using wordTrace_append hprefix tailTrace_6755653
  have hstable : (prefixWord ++ tailWord_6755653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755653).length < 2 ^ (prefixWord ++ tailWord_6755653).sum := by decide
  have hdescent : baseEnd_6755653 < baseStart_6755653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755721 : List Nat := [1, 2, 1, 1, 7, 1, 2, 2, 1, 3, 2]
def baseStart_6755721 : Nat := 118140960795 + 6755721 * 2 ^ 59
def prefixEnd_6755721 : Nat := 4983230072969 + 3 ^ 40 * 6755721 * 2
def baseEnd_6755721 : Nat := 3468932040673067944218511

theorem tailTrace_6755721 : CollatzResearch.WordTrace tailWord_6755721 prefixEnd_6755721 3468932040673067944218511 := by
  unfold tailWord_6755721
  simp only [CollatzResearch.WordTrace]
  refine ⟨246401387558184077134371017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164267591705456051422914011 246401387558184077134371017)
  ·
    refine ⟨184801040668638057850778263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246401387558184077134371017 184801040668638057850778263)
    ·
      refine ⟨277201561002957086776167395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184801040668638057850778263 277201561002957086776167395)
      ·
        refine ⟨415802341504435630164251093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277201561002957086776167395 415802341504435630164251093)
        ·
          refine ⟨9745367379010210081974635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 415802341504435630164251093 9745367379010210081974635)
          ·
            refine ⟨14618051068515315122961953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9745367379010210081974635 14618051068515315122961953)
            ·
              refine ⟨10963538301386486342221465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14618051068515315122961953 10963538301386486342221465)
              ·
                refine ⟨8222653726039864756666099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10963538301386486342221465 8222653726039864756666099)
                ·
                  refine ⟨12333980589059797134999149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8222653726039864756666099 12333980589059797134999149)
                  ·
                    refine ⟨4625242720897423925624681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12333980589059797134999149 4625242720897423925624681)
                    ·
                      refine ⟨3468932040673067944218511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4625242720897423925624681 3468932040673067944218511)
                      ·
                        rfl

theorem cell23_6755721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 3, 2].length) (baseStart_6755721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755721 prefixEnd_6755721 := by exact prefixLift 6755721
  have htrace : WordTrace (prefixWord ++ tailWord_6755721) baseStart_6755721 baseEnd_6755721 := by
    simpa [prefixWord, tailWord_6755721, baseEnd_6755721] using wordTrace_append hprefix tailTrace_6755721
  have hstable : (prefixWord ++ tailWord_6755721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755721).length < 2 ^ (prefixWord ++ tailWord_6755721).sum := by decide
  have hdescent : baseEnd_6755721 < baseStart_6755721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755751 : List Nat := [1, 1, 6, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_6755751 : Nat := 118140960795 + 6755751 * 2 ^ 59
def prefixEnd_6755751 : Nat := 4983230072969 + 3 ^ 40 * 6755751 * 2
def baseEnd_6755751 : Nat := 3468947445092702826843373

theorem tailTrace_6755751 : CollatzResearch.WordTrace tailWord_6755751 prefixEnd_6755751 3468947445092702826843373 := by
  unfold tailWord_6755751
  simp only [CollatzResearch.WordTrace]
  refine ⟨246402481748075392257963107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164268321165383594838642071 246402481748075392257963107)
  ·
    refine ⟨369603722622113088386944661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246402481748075392257963107 369603722622113088386944661)
    ·
      refine ⟨17325174497911551018138031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 369603722622113088386944661 17325174497911551018138031)
      ·
        refine ⟨25987761746867326527207047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17325174497911551018138031 25987761746867326527207047)
        ·
          refine ⟨38981642620300989790810571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25987761746867326527207047 38981642620300989790810571)
          ·
            refine ⟨58472463930451484686215857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38981642620300989790810571 58472463930451484686215857)
            ·
              refine ⟨43854347947838613514661893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58472463930451484686215857 43854347947838613514661893)
              ·
                refine ⟨8222690240219740033999105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43854347947838613514661893 8222690240219740033999105)
                ·
                  refine ⟨6167017680164805025499329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8222690240219740033999105 6167017680164805025499329)
                  ·
                    refine ⟨4625263260123603769124497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6167017680164805025499329 4625263260123603769124497)
                    ·
                      refine ⟨3468947445092702826843373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4625263260123603769124497 3468947445092702826843373)
                      ·
                        rfl

theorem cell23_6755751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_6755751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755751 prefixEnd_6755751 := by exact prefixLift 6755751
  have htrace : WordTrace (prefixWord ++ tailWord_6755751) baseStart_6755751 baseEnd_6755751 := by
    simpa [prefixWord, tailWord_6755751, baseEnd_6755751] using wordTrace_append hprefix tailTrace_6755751
  have hstable : (prefixWord ++ tailWord_6755751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755751).length < 2 ^ (prefixWord ++ tailWord_6755751).sum := by decide
  have hdescent : baseEnd_6755751 < baseStart_6755751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755807 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 4]
def baseStart_6755807 : Nat := 118140960795 + 6755807 * 2 ^ 59
def prefixEnd_6755807 : Nat := 4983230072969 + 3 ^ 40 * 6755807 * 2
def baseEnd_6755807 : Nat := 3468976200009354607743115

theorem tailTrace_6755807 : CollatzResearch.WordTrace tailWord_6755807 prefixEnd_6755807 3468976200009354607743115 := by
  unfold tailWord_6755807
  simp only [CollatzResearch.WordTrace]
  refine ⟨246404524235872513822001675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164269682823915009214667783 246404524235872513822001675)
  ·
    refine ⟨369606786353808770733002513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246404524235872513822001675 369606786353808770733002513)
    ·
      refine ⟨277205089765356578049751885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369606786353808770733002513 277205089765356578049751885)
      ·
        refine ⟨103951908662008716768656957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277205089765356578049751885 103951908662008716768656957)
        ·
          refine ⟨38981965748253268788246359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103951908662008716768656957 38981965748253268788246359)
          ·
            refine ⟨58472948622379903182369539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38981965748253268788246359 58472948622379903182369539)
            ·
              refine ⟨87709422933569854773554309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58472948622379903182369539 87709422933569854773554309)
              ·
                refine ⟨16445516800044347770041433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87709422933569854773554309 16445516800044347770041433)
                ·
                  refine ⟨12334137600033260827531075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16445516800044347770041433 12334137600033260827531075)
                  ·
                    refine ⟨18501206400049891241296613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12334137600033260827531075 18501206400049891241296613)
                    ·
                      refine ⟨3468976200009354607743115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18501206400049891241296613 3468976200009354607743115)
                      ·
                        rfl

theorem cell23_6755807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_6755807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755807 prefixEnd_6755807 := by exact prefixLift 6755807
  have htrace : WordTrace (prefixWord ++ tailWord_6755807) baseStart_6755807 baseEnd_6755807 := by
    simpa [prefixWord, tailWord_6755807, baseEnd_6755807] using wordTrace_append hprefix tailTrace_6755807
  have hstable : (prefixWord ++ tailWord_6755807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755807).length < 2 ^ (prefixWord ++ tailWord_6755807).sum := by decide
  have hdescent : baseEnd_6755807 < baseStart_6755807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755820 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_6755820 : Nat := 118140960795 + 6755820 * 2 ^ 59
def prefixEnd_6755820 : Nat := 4983230072969 + 3 ^ 40 * 6755820 * 2
def baseEnd_6755820 : Nat := 3468982875257863056880555

theorem tailTrace_6755820 : CollatzResearch.WordTrace tailWord_6755820 prefixEnd_6755820 3468982875257863056880555 := by
  unfold tailWord_6755820
  simp only [CollatzResearch.WordTrace]
  refine ⟨123202499192412708521112457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164269998923216944694816609 123202499192412708521112457)
  ·
    refine ⟨92401874394309531390834343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123202499192412708521112457 92401874394309531390834343)
    ·
      refine ⟨138602811591464297086251515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92401874394309531390834343 138602811591464297086251515)
      ·
        refine ⟨207904217387196445629377273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138602811591464297086251515 207904217387196445629377273)
        ·
          refine ⟨155928163040397334222032955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207904217387196445629377273 155928163040397334222032955)
          ·
            refine ⟨233892244560596001333049433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155928163040397334222032955 233892244560596001333049433)
            ·
              refine ⟨175419183420447000999787075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233892244560596001333049433 175419183420447000999787075)
              ·
                refine ⟨263128775130670501499680613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175419183420447000999787075 263128775130670501499680613)
                ·
                  refine ⟨49336645337000719031190115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263128775130670501499680613 49336645337000719031190115)
                  ·
                    refine ⟨74004968005501078546785173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49336645337000719031190115 74004968005501078546785173)
                    ·
                      refine ⟨3468982875257863056880555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74004968005501078546785173 3468982875257863056880555)
                      ·
                        rfl

theorem cell23_6755820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_6755820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755820 prefixEnd_6755820 := by exact prefixLift 6755820
  have htrace : WordTrace (prefixWord ++ tailWord_6755820) baseStart_6755820 baseEnd_6755820 := by
    simpa [prefixWord, tailWord_6755820, baseEnd_6755820] using wordTrace_append hprefix tailTrace_6755820
  have hstable : (prefixWord ++ tailWord_6755820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755820).length < 2 ^ (prefixWord ++ tailWord_6755820).sum := by decide
  have hdescent : baseEnd_6755820 < baseStart_6755820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755824 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 2, 4, 2]
def baseStart_6755824 : Nat := 118140960795 + 6755824 * 2 ^ 59
def prefixEnd_6755824 : Nat := 4983230072969 + 3 ^ 40 * 6755824 * 2
def baseEnd_6755824 : Nat := 3468984929180481041230537

theorem tailTrace_6755824 : CollatzResearch.WordTrace tailWord_6755824 prefixEnd_6755824 3468984929180481041230537 := by
  unfold tailWord_6755824
  simp only [CollatzResearch.WordTrace]
  refine ⟨123202572138405462862685263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164270096184540617150247017 123202572138405462862685263)
  ·
    refine ⟨184803858207608194294027895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123202572138405462862685263 184803858207608194294027895)
    ·
      refine ⟨277205787311412291441041843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184803858207608194294027895 277205787311412291441041843)
      ·
        refine ⟨415808680967118437161562765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277205787311412291441041843 415808680967118437161562765)
        ·
          refine ⟨155928255362669413935586037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415808680967118437161562765 155928255362669413935586037)
          ·
            refine ⟨14618273940250257556461191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155928255362669413935586037 14618273940250257556461191)
            ·
              refine ⟨21927410910375386334691787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14618273940250257556461191 21927410910375386334691787)
              ·
                refine ⟨32891116365563079502037681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21927410910375386334691787 32891116365563079502037681)
                ·
                  refine ⟨24668337274172309626528261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32891116365563079502037681 24668337274172309626528261)
                  ·
                    refine ⟨4625313238907308054974049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24668337274172309626528261 4625313238907308054974049)
                    ·
                      refine ⟨3468984929180481041230537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4625313238907308054974049 3468984929180481041230537)
                      ·
                        rfl

theorem cell23_6755824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 4, 2].length) (baseStart_6755824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755824 prefixEnd_6755824 := by exact prefixLift 6755824
  have htrace : WordTrace (prefixWord ++ tailWord_6755824) baseStart_6755824 baseEnd_6755824 := by
    simpa [prefixWord, tailWord_6755824, baseEnd_6755824] using wordTrace_append hprefix tailTrace_6755824
  have hstable : (prefixWord ++ tailWord_6755824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755824).length < 2 ^ (prefixWord ++ tailWord_6755824).sum := by decide
  have hdescent : baseEnd_6755824 < baseStart_6755824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755838 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_6755838 : Nat := 118140960795 + 6755838 * 2 ^ 59
def prefixEnd_6755838 : Nat := 4983230072969 + 3 ^ 40 * 6755838 * 2
def baseEnd_6755838 : Nat := 1156330705969881328818491

theorem tailTrace_6755838 : CollatzResearch.WordTrace tailWord_6755838 prefixEnd_6755838 1156330705969881328818491 := by
  unfold tailWord_6755838
  simp only [CollatzResearch.WordTrace]
  refine ⟨30800706862345025764547521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164270436599173470744253445 30800706862345025764547521)
  ·
    refine ⟨23100530146758769323410641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30800706862345025764547521 23100530146758769323410641)
    ·
      refine ⟨17325397610069076992557981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23100530146758769323410641 17325397610069076992557981)
      ·
        refine ⟨6497024103775903872209243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17325397610069076992557981 6497024103775903872209243)
        ·
          refine ⟨9745536155663855808313865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6497024103775903872209243 9745536155663855808313865)
          ·
            refine ⟨7309152116747891856235399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9745536155663855808313865 7309152116747891856235399)
            ·
              refine ⟨10963728175121837784353099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7309152116747891856235399 10963728175121837784353099)
              ·
                refine ⟨16445592262682756676529649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10963728175121837784353099 16445592262682756676529649)
                ·
                  refine ⟨12334194197012067507397237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16445592262682756676529649 12334194197012067507397237)
                  ·
                    refine ⟨1156330705969881328818491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12334194197012067507397237 1156330705969881328818491)
                    ·
                      rfl

theorem cell23_6755838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_6755838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755838 prefixEnd_6755838 := by exact prefixLift 6755838
  have htrace : WordTrace (prefixWord ++ tailWord_6755838) baseStart_6755838 baseEnd_6755838 := by
    simpa [prefixWord, tailWord_6755838, baseEnd_6755838] using wordTrace_append hprefix tailTrace_6755838
  have hstable : (prefixWord ++ tailWord_6755838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755838).length < 2 ^ (prefixWord ++ tailWord_6755838).sum := by decide
  have hdescent : baseEnd_6755838 < baseStart_6755838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755841 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_6755841 : Nat := 118140960795 + 6755841 * 2 ^ 59
def prefixEnd_6755841 : Nat := 4983230072969 + 3 ^ 40 * 6755841 * 2
def baseEnd_6755841 : Nat := 3468993658351607474717959

theorem tailTrace_6755841 : CollatzResearch.WordTrace tailWord_6755841 prefixEnd_6755841 3468993658351607474717959 := by
  unfold tailWord_6755841
  simp only [CollatzResearch.WordTrace]
  refine ⟨246405764317749337628739377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164270509545166225085826251 246405764317749337628739377)
  ·
    refine ⟨184804323238312003221554533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246405764317749337628739377 184804323238312003221554533)
    ·
      refine ⟨34650810607183500604041475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184804323238312003221554533 34650810607183500604041475)
      ·
        refine ⟨51976215910775250906062213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34650810607183500604041475 51976215910775250906062213)
        ·
          refine ⟨9745540483270359544886665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51976215910775250906062213 9745540483270359544886665)
          ·
            refine ⟨7309155362452769658664999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9745540483270359544886665 7309155362452769658664999)
            ·
              refine ⟨10963733043679154487997499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7309155362452769658664999 10963733043679154487997499)
              ·
                refine ⟨16445599565518731731996249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10963733043679154487997499 16445599565518731731996249)
                ·
                  refine ⟨12334199674139048798997187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16445599565518731731996249 12334199674139048798997187)
                  ·
                    refine ⟨18501299511208573198495781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12334199674139048798997187 18501299511208573198495781)
                    ·
                      refine ⟨3468993658351607474717959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18501299511208573198495781 3468993658351607474717959)
                      ·
                        rfl

theorem cell23_6755841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_6755841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755841 prefixEnd_6755841 := by exact prefixLift 6755841
  have htrace : WordTrace (prefixWord ++ tailWord_6755841) baseStart_6755841 baseEnd_6755841 := by
    simpa [prefixWord, tailWord_6755841, baseEnd_6755841] using wordTrace_append hprefix tailTrace_6755841
  have hstable : (prefixWord ++ tailWord_6755841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755841).length < 2 ^ (prefixWord ++ tailWord_6755841).sum := by decide
  have hdescent : baseEnd_6755841 < baseStart_6755841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755914 : List Nat := [3, 1, 2, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_6755914 : Nat := 118140960795 + 6755914 * 2 ^ 59
def prefixEnd_6755914 : Nat := 4983230072969 + 3 ^ 40 * 6755914 * 2
def baseEnd_6755914 : Nat := 3469031142439385689105123

theorem tailTrace_6755914 : CollatzResearch.WordTrace tailWord_6755914 prefixEnd_6755914 3469031142439385689105123 := by
  unfold tailWord_6755914
  simp only [CollatzResearch.WordTrace]
  refine ⟨61602106711621217774036699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164272284564323247397431197 61602106711621217774036699)
  ·
    refine ⟨92403160067431826661055049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61602106711621217774036699 92403160067431826661055049)
    ·
      refine ⟨69302370050573869995791287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92403160067431826661055049 69302370050573869995791287)
      ·
        refine ⟨103953555075860804993686931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69302370050573869995791287 103953555075860804993686931)
        ·
          refine ⟨155930332613791207490530397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103953555075860804993686931 155930332613791207490530397)
          ·
            refine ⟨58473874730171702808948899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155930332613791207490530397 58473874730171702808948899)
            ·
              refine ⟨87710812095257554213423349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58473874730171702808948899 87710812095257554213423349)
              ·
                refine ⟨8222888633930395707508439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87710812095257554213423349 8222888633930395707508439)
                ·
                  refine ⟨12334332950895593561262659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8222888633930395707508439 12334332950895593561262659)
                  ·
                    refine ⟨18501499426343390341893989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12334332950895593561262659 18501499426343390341893989)
                    ·
                      refine ⟨3469031142439385689105123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18501499426343390341893989 3469031142439385689105123)
                      ·
                        rfl

theorem cell23_6755914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_6755914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755914 prefixEnd_6755914 := by exact prefixLift 6755914
  have htrace : WordTrace (prefixWord ++ tailWord_6755914) baseStart_6755914 baseEnd_6755914 := by
    simpa [prefixWord, tailWord_6755914, baseEnd_6755914] using wordTrace_append hprefix tailTrace_6755914
  have hstable : (prefixWord ++ tailWord_6755914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755914).length < 2 ^ (prefixWord ++ tailWord_6755914).sum := by decide
  have hdescent : baseEnd_6755914 < baseStart_6755914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755924 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_6755924 : Nat := 118140960795 + 6755924 * 2 ^ 59
def prefixEnd_6755924 : Nat := 4983230072969 + 3 ^ 40 * 6755924 * 2
def baseEnd_6755924 : Nat := 1156345425748643549993359

theorem tailTrace_6755924 : CollatzResearch.WordTrace tailWord_6755924 prefixEnd_6755924 1156345425748643549993359 := by
  unfold tailWord_6755924
  simp only [CollatzResearch.WordTrace]
  refine ⟨123204395788224321402005413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164272527717632428536007217 123204395788224321402005413)
  ·
    refine ⟨23100824210292060262876015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123204395788224321402005413 23100824210292060262876015)
    ·
      refine ⟨34651236315438090394314023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23100824210292060262876015 34651236315438090394314023)
      ·
        refine ⟨51976854473157135591471035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34651236315438090394314023 51976854473157135591471035)
        ·
          refine ⟨77965281709735703387206553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51976854473157135591471035 77965281709735703387206553)
          ·
            refine ⟨58473961282301777540404915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77965281709735703387206553 58473961282301777540404915)
            ·
              refine ⟨87710941923452666310607373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58473961282301777540404915 87710941923452666310607373)
              ·
                refine ⟨32891603221294749866477765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87710941923452666310607373 32891603221294749866477765)
                ·
                  refine ⟨6167175603992765599964581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32891603221294749866477765 6167175603992765599964581)
                  ·
                    refine ⟨1156345425748643549993359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6167175603992765599964581 1156345425748643549993359)
                    ·
                      rfl

theorem cell23_6755924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_6755924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755924 prefixEnd_6755924 := by exact prefixLift 6755924
  have htrace : WordTrace (prefixWord ++ tailWord_6755924) baseStart_6755924 baseEnd_6755924 := by
    simpa [prefixWord, tailWord_6755924, baseEnd_6755924] using wordTrace_append hprefix tailTrace_6755924
  have hstable : (prefixWord ++ tailWord_6755924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755924).length < 2 ^ (prefixWord ++ tailWord_6755924).sum := by decide
  have hdescent : baseEnd_6755924 < baseStart_6755924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755927 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_6755927 : Nat := 118140960795 + 6755927 * 2 ^ 59
def prefixEnd_6755927 : Nat := 4983230072969 + 3 ^ 40 * 6755927 * 2
def baseEnd_6755927 : Nat := 3469037817687894138242563

theorem tailTrace_6755927 : CollatzResearch.WordTrace tailWord_6755927 prefixEnd_6755927 3469037817687894138242563 := by
  unfold tailWord_6755927
  simp only [CollatzResearch.WordTrace]
  refine ⟨246408900995437774316370035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164272600663625182877580023 246408900995437774316370035)
  ·
    refine ⟨369613351493156661474555053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246408900995437774316370035 369613351493156661474555053)
    ·
      refine ⟨138605006809933748052958145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369613351493156661474555053 138605006809933748052958145)
      ·
        refine ⟨103953755107450311039718609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138605006809933748052958145 103953755107450311039718609)
        ·
          refine ⟨77965316330587733279788957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103953755107450311039718609 77965316330587733279788957)
          ·
            refine ⟨29236993623970399979920859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77965316330587733279788957 29236993623970399979920859)
            ·
              refine ⟨43855490435955599969881289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29236993623970399979920859 43855490435955599969881289)
              ·
                refine ⟨32891617826966699977410967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43855490435955599969881289 32891617826966699977410967)
                ·
                  refine ⟨49337426740450049966116451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32891617826966699977410967 49337426740450049966116451)
                  ·
                    refine ⟨74006140110675074949174677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49337426740450049966116451 74006140110675074949174677)
                    ·
                      refine ⟨3469037817687894138242563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74006140110675074949174677 3469037817687894138242563)
                      ·
                        rfl

theorem cell23_6755927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_6755927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755927 prefixEnd_6755927 := by exact prefixLift 6755927
  have htrace : WordTrace (prefixWord ++ tailWord_6755927) baseStart_6755927 baseEnd_6755927 := by
    simpa [prefixWord, tailWord_6755927, baseEnd_6755927] using wordTrace_append hprefix tailTrace_6755927
  have hstable : (prefixWord ++ tailWord_6755927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755927).length < 2 ^ (prefixWord ++ tailWord_6755927).sum := by decide
  have hdescent : baseEnd_6755927 < baseStart_6755927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755937 : List Nat := [1, 2, 3, 1, 1, 3, 4, 8]
def baseStart_6755937 : Nat := 118140960795 + 6755937 * 2 ^ 59
def prefixEnd_6755937 : Nat := 4983230072969 + 3 ^ 40 * 6755937 * 2
def baseEnd_6755937 : Nat := 128483072314608855522871

theorem tailTrace_6755937 : CollatzResearch.WordTrace tailWord_6755937 prefixEnd_6755937 128483072314608855522871 := by
  unfold tailWord_6755937
  simp only [CollatzResearch.WordTrace]
  refine ⟨246409265725401546024234065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164272843816934364016156043 246409265725401546024234065)
  ·
    refine ⟨184806949294051159518175549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246409265725401546024234065 184806949294051159518175549)
    ·
      refine ⟨69302605985269184819315831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184806949294051159518175549 69302605985269184819315831)
      ·
        refine ⟨103953908977903777228973747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69302605985269184819315831 103953908977903777228973747)
        ·
          refine ⟨155930863466855665843460621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103953908977903777228973747 155930863466855665843460621)
          ·
            refine ⟨58474073800070874691297733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155930863466855665843460621 58474073800070874691297733)
            ·
              refine ⟨10963888837513289004618325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58474073800070874691297733 10963888837513289004618325)
              ·
                refine ⟨128483072314608855522871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10963888837513289004618325 128483072314608855522871)
                ·
                  rfl

theorem cell23_6755937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 8].length) (baseStart_6755937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755937 prefixEnd_6755937 := by exact prefixLift 6755937
  have htrace : WordTrace (prefixWord ++ tailWord_6755937) baseStart_6755937 baseEnd_6755937 := by
    simpa [prefixWord, tailWord_6755937, baseEnd_6755937] using wordTrace_append hprefix tailTrace_6755937
  have hstable : (prefixWord ++ tailWord_6755937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755937).length < 2 ^ (prefixWord ++ tailWord_6755937).sum := by decide
  have hdescent : baseEnd_6755937 < baseStart_6755937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755941 : List Nat := [1, 3, 1, 3, 3, 2, 1, 3, 2, 4]
def baseStart_6755941 : Nat := 118140960795 + 6755941 * 2 ^ 59
def prefixEnd_6755941 : Nat := 4983230072969 + 3 ^ 40 * 6755941 * 2
def baseEnd_6755941 : Nat := 1156348335472352361155833

theorem tailTrace_6755941 : CollatzResearch.WordTrace tailWord_6755941 prefixEnd_6755941 1156348335472352361155833 := by
  unfold tailWord_6755941
  simp only [CollatzResearch.WordTrace]
  refine ⟨246409411617387054707379677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164272941078258036471586451 246409411617387054707379677)
  ·
    refine ⟨92403529356520145515267379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246409411617387054707379677 92403529356520145515267379)
    ·
      refine ⟨138605294034780218272901069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92403529356520145515267379 138605294034780218272901069)
      ·
        refine ⟨51976985263042581852337901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138605294034780218272901069 51976985263042581852337901)
        ·
          refine ⟨19491369473640968194626713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51976985263042581852337901 19491369473640968194626713)
          ·
            refine ⟨14618527105230726145970035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19491369473640968194626713 14618527105230726145970035)
            ·
              refine ⟨21927790657846089218955053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14618527105230726145970035 21927790657846089218955053)
              ·
                refine ⟨8222921496692283457108145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21927790657846089218955053 8222921496692283457108145)
                ·
                  refine ⟨6167191122519212592831109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8222921496692283457108145 6167191122519212592831109)
                  ·
                    refine ⟨1156348335472352361155833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6167191122519212592831109 1156348335472352361155833)
                    ·
                      rfl

theorem cell23_6755941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_6755941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755941 prefixEnd_6755941 := by exact prefixLift 6755941
  have htrace : WordTrace (prefixWord ++ tailWord_6755941) baseStart_6755941 baseEnd_6755941 := by
    simpa [prefixWord, tailWord_6755941, baseEnd_6755941] using wordTrace_append hprefix tailTrace_6755941
  have hstable : (prefixWord ++ tailWord_6755941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755941).length < 2 ^ (prefixWord ++ tailWord_6755941).sum := by decide
  have hdescent : baseEnd_6755941 < baseStart_6755941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755944 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6755944 : Nat := 118140960795 + 6755944 * 2 ^ 59
def prefixEnd_6755944 : Nat := 4983230072969 + 3 ^ 40 * 6755944 * 2
def baseEnd_6755944 : Nat := 3469046546859020571729985

theorem tailTrace_6755944 : CollatzResearch.WordTrace tailWord_6755944 prefixEnd_6755944 3469046546859020571729985 := by
  unfold tailWord_6755944
  simp only [CollatzResearch.WordTrace]
  refine ⟨123204760518188093109869443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164273014024250790813159257 123204760518188093109869443)
  ·
    refine ⟨184807140777282139664804165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123204760518188093109869443 184807140777282139664804165)
    ·
      refine ⟨34651338895740401187150781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184807140777282139664804165 34651338895740401187150781)
      ·
        refine ⟨12994252085902650445181543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34651338895740401187150781 12994252085902650445181543)
        ·
          refine ⟨19491378128853975667772315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12994252085902650445181543 19491378128853975667772315)
          ·
            refine ⟨29237067193280963501658473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19491378128853975667772315 29237067193280963501658473)
            ·
              refine ⟨21927800394960722626243855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29237067193280963501658473 21927800394960722626243855)
              ·
                refine ⟨32891700592441083939365783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21927800394960722626243855 32891700592441083939365783)
                ·
                  refine ⟨49337550888661625909048675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32891700592441083939365783 49337550888661625909048675)
                  ·
                    refine ⟨74006326332992438863573013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49337550888661625909048675 74006326332992438863573013)
                    ·
                      refine ⟨3469046546859020571729985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74006326332992438863573013 3469046546859020571729985)
                      ·
                        rfl

theorem cell23_6755944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6755944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755944 prefixEnd_6755944 := by exact prefixLift 6755944
  have htrace : WordTrace (prefixWord ++ tailWord_6755944) baseStart_6755944 baseEnd_6755944 := by
    simpa [prefixWord, tailWord_6755944, baseEnd_6755944] using wordTrace_append hprefix tailTrace_6755944
  have hstable : (prefixWord ++ tailWord_6755944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755944).length < 2 ^ (prefixWord ++ tailWord_6755944).sum := by decide
  have hdescent : baseEnd_6755944 < baseStart_6755944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755977 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 5]
def baseStart_6755977 : Nat := 118140960795 + 6755977 * 2 ^ 59
def prefixEnd_6755977 : Nat := 4983230072969 + 3 ^ 40 * 6755977 * 2
def baseEnd_6755977 : Nat := 3469063491720618942617333

theorem tailTrace_6755977 : CollatzResearch.WordTrace tailWord_6755977 prefixEnd_6755977 3469063491720618942617333 := by
  unfold tailWord_6755977
  simp only [CollatzResearch.WordTrace]
  refine ⟨246410724645256632855690185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164273816430171088570460123 246410724645256632855690185)
  ·
    refine ⟨184808043483942474641767639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246410724645256632855690185 184808043483942474641767639)
    ·
      refine ⟨277212065225913711962651459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184808043483942474641767639 277212065225913711962651459)
      ·
        refine ⟨415818097838870567943977189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277212065225913711962651459 415818097838870567943977189)
        ·
          refine ⟨77965893344788231489495723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 415818097838870567943977189 77965893344788231489495723)
          ·
            refine ⟨116948840017182347234243585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77965893344788231489495723 116948840017182347234243585)
            ·
              refine ⟨87711630012886760425682689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116948840017182347234243585 87711630012886760425682689)
              ·
                refine ⟨65783722509665070319262017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87711630012886760425682689 65783722509665070319262017)
                ·
                  refine ⟨49337791882248802739446513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65783722509665070319262017 49337791882248802739446513)
                  ·
                    refine ⟨37003343911686602054584885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49337791882248802739446513 37003343911686602054584885)
                    ·
                      refine ⟨3469063491720618942617333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37003343911686602054584885 3469063491720618942617333)
                      ·
                        rfl

theorem cell23_6755977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_6755977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755977 prefixEnd_6755977 := by exact prefixLift 6755977
  have htrace : WordTrace (prefixWord ++ tailWord_6755977) baseStart_6755977 baseEnd_6755977 := by
    simpa [prefixWord, tailWord_6755977, baseEnd_6755977] using wordTrace_append hprefix tailTrace_6755977
  have hstable : (prefixWord ++ tailWord_6755977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755977).length < 2 ^ (prefixWord ++ tailWord_6755977).sum := by decide
  have hdescent : baseEnd_6755977 < baseStart_6755977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755982 : List Nat := [4, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2]
def baseStart_6755982 : Nat := 118140960795 + 6755982 * 2 ^ 59
def prefixEnd_6755982 : Nat := 4983230072969 + 3 ^ 40 * 6755982 * 2
def baseEnd_6755982 : Nat := 3469066059123891423054811

theorem tailTrace_6755982 : CollatzResearch.WordTrace tailWord_6755982 prefixEnd_6755982 3469066059123891423054811 := by
  unfold tailWord_6755982
  simp only [CollatzResearch.WordTrace]
  refine ⟨30801363376279814838702775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164273938006825679139748133 30801363376279814838702775)
  ·
    refine ⟨46202045064419722258054163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30801363376279814838702775 46202045064419722258054163)
    ·
      refine ⟨69303067596629583387081245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46202045064419722258054163 69303067596629583387081245)
      ·
        refine ⟨25988650348736093770155467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69303067596629583387081245 25988650348736093770155467)
        ·
          refine ⟨38982975523104140655233201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25988650348736093770155467 38982975523104140655233201)
          ·
            refine ⟨29237231642328105491424901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38982975523104140655233201 29237231642328105491424901)
            ·
              refine ⟨5481980932936519779642169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29237231642328105491424901 5481980932936519779642169)
              ·
                refine ⟨4111485699702389834731627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5481980932936519779642169 4111485699702389834731627)
                ·
                  refine ⟨6167228549553584752097441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4111485699702389834731627 6167228549553584752097441)
                  ·
                    refine ⟨4625421412165188564073081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6167228549553584752097441 4625421412165188564073081)
                    ·
                      refine ⟨3469066059123891423054811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4625421412165188564073081 3469066059123891423054811)
                      ·
                        rfl

theorem cell23_6755982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_6755982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755982 prefixEnd_6755982 := by exact prefixLift 6755982
  have htrace : WordTrace (prefixWord ++ tailWord_6755982) baseStart_6755982 baseEnd_6755982 := by
    simpa [prefixWord, tailWord_6755982, baseEnd_6755982] using wordTrace_append hprefix tailTrace_6755982
  have hstable : (prefixWord ++ tailWord_6755982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755982).length < 2 ^ (prefixWord ++ tailWord_6755982).sum := by decide
  have hdescent : baseEnd_6755982 < baseStart_6755982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755988 : List Nat := [2, 4, 2, 2, 3, 1, 1, 8]
def baseStart_6755988 : Nat := 118140960795 + 6755988 * 2 ^ 59
def prefixEnd_6755988 : Nat := 4983230072969 + 3 ^ 40 * 6755988 * 2
def baseEnd_6755988 : Nat := 128484042222511792577029

theorem tailTrace_6755988 : CollatzResearch.WordTrace tailWord_6755988 prefixEnd_6755988 128484042222511792577029 := by
  unfold tailWord_6755988
  simp only [CollatzResearch.WordTrace]
  refine ⟨123205562924108390867170309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164274083898811187822893745 123205562924108390867170309)
  ·
    refine ⟨23101043048270323287594433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123205562924108390867170309 23101043048270323287594433)
    ·
      refine ⟨17325782286202742465695825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23101043048270323287594433 17325782286202742465695825)
      ·
        refine ⟨12994336714652056849271869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17325782286202742465695825 12994336714652056849271869)
        ·
          refine ⟨4872876267994521318476951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12994336714652056849271869 4872876267994521318476951)
          ·
            refine ⟨7309314401991781977715427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4872876267994521318476951 7309314401991781977715427)
            ·
              refine ⟨10963971602987672966573141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7309314401991781977715427 10963971602987672966573141)
              ·
                refine ⟨128484042222511792577029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10963971602987672966573141 128484042222511792577029)
                ·
                  rfl

theorem cell23_6755988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 8].length) (baseStart_6755988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755988 prefixEnd_6755988 := by exact prefixLift 6755988
  have htrace : WordTrace (prefixWord ++ tailWord_6755988) baseStart_6755988 baseEnd_6755988 := by
    simpa [prefixWord, tailWord_6755988, baseEnd_6755988] using wordTrace_append hprefix tailTrace_6755988
  have hstable : (prefixWord ++ tailWord_6755988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755988).length < 2 ^ (prefixWord ++ tailWord_6755988).sum := by decide
  have hdescent : baseEnd_6755988 < baseStart_6755988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755991 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 3, 3, 2]
def baseStart_6755991 : Nat := 118140960795 + 6755991 * 2 ^ 59
def prefixEnd_6755991 : Nat := 4983230072969 + 3 ^ 40 * 6755991 * 2
def baseEnd_6755991 : Nat := 3469070680449781887842269

theorem tailTrace_6755991 : CollatzResearch.WordTrace tailWord_6755991 prefixEnd_6755991 3469070680449781887842269 := by
  unfold tailWord_6755991
  simp only [CollatzResearch.WordTrace]
  refine ⟨246411235267205913246699827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164274156844803942164466551 246411235267205913246699827)
  ·
    refine ⟨369616852900808869870049741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246411235267205913246699827 369616852900808869870049741)
    ·
      refine ⟨138606319837803326201268653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369616852900808869870049741 138606319837803326201268653)
      ·
        refine ⟨51977369939176247325475745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138606319837803326201268653 51977369939176247325475745)
        ·
          refine ⟨38983027454382185494106809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51977369939176247325475745 38983027454382185494106809)
          ·
            refine ⟨29237270590786639120580107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38983027454382185494106809 29237270590786639120580107)
            ·
              refine ⟨43855905886179958680870161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29237270590786639120580107 43855905886179958680870161)
              ·
                refine ⟨32891929414634969010652621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43855905886179958680870161 32891929414634969010652621)
                ·
                  refine ⟨12334473530488113378994733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32891929414634969010652621 12334473530488113378994733)
                  ·
                    refine ⟨4625427573933042517123025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12334473530488113378994733 4625427573933042517123025)
                    ·
                      refine ⟨3469070680449781887842269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4625427573933042517123025 3469070680449781887842269)
                      ·
                        rfl

theorem cell23_6755991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_6755991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755991 prefixEnd_6755991 := by exact prefixLift 6755991
  have htrace : WordTrace (prefixWord ++ tailWord_6755991) baseStart_6755991 baseEnd_6755991 := by
    simpa [prefixWord, tailWord_6755991, baseEnd_6755991] using wordTrace_append hprefix tailTrace_6755991
  have hstable : (prefixWord ++ tailWord_6755991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755991).length < 2 ^ (prefixWord ++ tailWord_6755991).sum := by decide
  have hdescent : baseEnd_6755991 < baseStart_6755991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6755998 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_6755998 : Nat := 118140960795 + 6755998 * 2 ^ 59
def prefixEnd_6755998 : Nat := 4983230072969 + 3 ^ 40 * 6755998 * 2
def baseEnd_6755998 : Nat := 3469074274814363360454737

theorem tailTrace_6755998 : CollatzResearch.WordTrace tailWord_6755998 prefixEnd_6755998 3469074274814363360454737 := by
  unfold tailWord_6755998
  simp only [CollatzResearch.WordTrace]
  refine ⟨30801436322272569180275581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164274327052120368961469765 30801436322272569180275581)
  ·
    refine ⟨11550538620852213442603343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30801436322272569180275581 11550538620852213442603343)
    ·
      refine ⟨17325807931278320163905015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11550538620852213442603343 17325807931278320163905015)
      ·
        refine ⟨25988711896917480245857523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17325807931278320163905015 25988711896917480245857523)
        ·
          refine ⟨38983067845376220368786285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25988711896917480245857523 38983067845376220368786285)
          ·
            refine ⟨14618650442016082638294857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38983067845376220368786285 14618650442016082638294857)
            ·
              refine ⟨10963987831512061978721143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14618650442016082638294857 10963987831512061978721143)
              ·
                refine ⟨16445981747268092968081715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10963987831512061978721143 16445981747268092968081715)
                ·
                  refine ⟨24668972620902139452122573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16445981747268092968081715 24668972620902139452122573)
                  ·
                    refine ⟨9250864732838302294545965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24668972620902139452122573 9250864732838302294545965)
                    ·
                      refine ⟨3469074274814363360454737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9250864732838302294545965 3469074274814363360454737)
                      ·
                        rfl

theorem cell23_6755998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_6755998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6755998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6755998 prefixEnd_6755998 := by exact prefixLift 6755998
  have htrace : WordTrace (prefixWord ++ tailWord_6755998) baseStart_6755998 baseEnd_6755998 := by
    simpa [prefixWord, tailWord_6755998, baseEnd_6755998] using wordTrace_append hprefix tailTrace_6755998
  have hstable : (prefixWord ++ tailWord_6755998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6755998).length < 2 ^ (prefixWord ++ tailWord_6755998).sum := by decide
  have hdescent : baseEnd_6755998 < baseStart_6755998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6755998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756037 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_6756037 : Nat := 118140960795 + 6756037 * 2 ^ 59
def prefixEnd_6756037 : Nat := 4983230072969 + 3 ^ 40 * 6756037 * 2
def baseEnd_6756037 : Nat := 3469094300559888707867057

theorem tailTrace_6756037 : CollatzResearch.WordTrace tailWord_6756037 prefixEnd_6756037 3469094300559888707867057 := by
  unfold tailWord_6756037
  simp only [CollatzResearch.WordTrace]
  refine ⟨246412913025039263102874365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164275275350026175401916243 246412913025039263102874365)
  ·
    refine ⟨92404842384389723663577887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246412913025039263102874365 92404842384389723663577887)
    ·
      refine ⟨138607263576584585495366831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92404842384389723663577887 138607263576584585495366831)
      ·
        refine ⟨207910895364876878243050247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138607263576584585495366831 207910895364876878243050247)
        ·
          refine ⟨311866343047315317364575371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207910895364876878243050247 311866343047315317364575371)
          ·
            refine ⟨467799514570972976046863057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311866343047315317364575371 467799514570972976046863057)
            ·
              refine ⟨350849635928229732035147293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467799514570972976046863057 350849635928229732035147293)
              ·
                refine ⟨131568613473086149513180235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350849635928229732035147293 131568613473086149513180235)
                ·
                  refine ⟨197352920209629224269770353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131568613473086149513180235 197352920209629224269770353)
                  ·
                    refine ⟨148014690157221918202327765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197352920209629224269770353 148014690157221918202327765)
                    ·
                      refine ⟨3469094300559888707867057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148014690157221918202327765 3469094300559888707867057)
                      ·
                        rfl

theorem cell23_6756037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_6756037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756037 prefixEnd_6756037 := by exact prefixLift 6756037
  have htrace : WordTrace (prefixWord ++ tailWord_6756037) baseStart_6756037 baseEnd_6756037 := by
    simpa [prefixWord, tailWord_6756037, baseEnd_6756037] using wordTrace_append hprefix tailTrace_6756037
  have hstable : (prefixWord ++ tailWord_6756037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756037).length < 2 ^ (prefixWord ++ tailWord_6756037).sum := by decide
  have hdescent : baseEnd_6756037 < baseStart_6756037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756055 : List Nat := [1, 1, 3, 2, 1, 3, 5, 1, 2, 2, 2]
def baseStart_6756055 : Nat := 118140960795 + 6756055 * 2 ^ 59
def prefixEnd_6756055 : Nat := 4983230072969 + 3 ^ 40 * 6756055 * 2
def baseEnd_6756055 : Nat := 3469103543211669637441975

theorem tailTrace_6756055 : CollatzResearch.WordTrace tailWord_6756055 prefixEnd_6756055 3469103543211669637441975 := by
  unfold tailWord_6756055
  simp only [CollatzResearch.WordTrace]
  refine ⟨246413569538974052177029619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164275713025982701451353079 246413569538974052177029619)
  ·
    refine ⟨369620354308461078265544429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246413569538974052177029619 369620354308461078265544429)
    ·
      refine ⟨138607632865672904349579161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369620354308461078265544429 138607632865672904349579161)
      ·
        refine ⟨103955724649254678262184371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138607632865672904349579161 103955724649254678262184371)
        ·
          refine ⟨155933586973882017393276557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103955724649254678262184371 155933586973882017393276557)
          ·
            refine ⟨58475095115205756522478709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155933586973882017393276557 58475095115205756522478709)
            ·
              refine ⟨5482040167050539673982379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58475095115205756522478709 5482040167050539673982379)
              ·
                refine ⟨8223060250575809510973569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5482040167050539673982379 8223060250575809510973569)
                ·
                  refine ⟨6167295187931857133230177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8223060250575809510973569 6167295187931857133230177)
                  ·
                    refine ⟨4625471390948892849922633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6167295187931857133230177 4625471390948892849922633)
                    ·
                      refine ⟨3469103543211669637441975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4625471390948892849922633 3469103543211669637441975)
                      ·
                        rfl

theorem cell23_6756055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_6756055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756055 prefixEnd_6756055 := by exact prefixLift 6756055
  have htrace : WordTrace (prefixWord ++ tailWord_6756055) baseStart_6756055 baseEnd_6756055 := by
    simpa [prefixWord, tailWord_6756055, baseEnd_6756055] using wordTrace_append hprefix tailTrace_6756055
  have hstable : (prefixWord ++ tailWord_6756055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756055).length < 2 ^ (prefixWord ++ tailWord_6756055).sum := by decide
  have hdescent : baseEnd_6756055 < baseStart_6756055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756074 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 1, 7]
def baseStart_6756074 : Nat := 118140960795 + 6756074 * 2 ^ 59
def prefixEnd_6756074 : Nat := 4983230072969 + 3 ^ 40 * 6756074 * 2
def baseEnd_6756074 : Nat := 1156371099781368354368129

theorem tailTrace_6756074 : CollatzResearch.WordTrace tailWord_6756074 prefixEnd_6756074 1156371099781368354368129 := by
  unfold tailWord_6756074
  simp only [CollatzResearch.WordTrace]
  refine ⟨61603565631476304605492819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164276175017270145614647517 61603565631476304605492819)
  ·
    refine ⟨92405348447214456908239229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61603565631476304605492819 92405348447214456908239229)
    ·
      refine ⟨34652005667705421340589711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92405348447214456908239229 34652005667705421340589711)
      ·
        refine ⟨51978008501558132010884567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34652005667705421340589711 51978008501558132010884567)
        ·
          refine ⟨77967012752337198016326851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51978008501558132010884567 77967012752337198016326851)
          ·
            refine ⟨116950519128505797024490277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77967012752337198016326851 116950519128505797024490277)
            ·
              refine ⟨21928222336594836942091927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116950519128505797024490277 21928222336594836942091927)
              ·
                refine ⟨32892333504892255413137891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21928222336594836942091927 32892333504892255413137891)
                ·
                  refine ⟨49338500257338383119706837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32892333504892255413137891 49338500257338383119706837)
                  ·
                    refine ⟨1156371099781368354368129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49338500257338383119706837 1156371099781368354368129)
                    ·
                      rfl

theorem cell23_6756074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_6756074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756074 prefixEnd_6756074 := by exact prefixLift 6756074
  have htrace : WordTrace (prefixWord ++ tailWord_6756074) baseStart_6756074 baseEnd_6756074 := by
    simpa [prefixWord, tailWord_6756074, baseEnd_6756074] using wordTrace_append hprefix tailTrace_6756074
  have hstable : (prefixWord ++ tailWord_6756074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756074).length < 2 ^ (prefixWord ++ tailWord_6756074).sum := by decide
  have hdescent : baseEnd_6756074 < baseStart_6756074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756098 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_6756098 : Nat := 118140960795 + 6756098 * 2 ^ 59
def prefixEnd_6756098 : Nat := 4983230072969 + 3 ^ 40 * 6756098 * 2
def baseEnd_6756098 : Nat := 3469125622879812969204277

theorem tailTrace_6756098 : CollatzResearch.WordTrace tailWord_6756098 prefixEnd_6756098 3469125622879812969204277 := by
  unfold tailWord_6756098
  simp only [CollatzResearch.WordTrace]
  refine ⟨61603784469454567630211237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164276758585212180347229965 61603784469454567630211237)
  ·
    refine ⟨11550709588022731430664607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61603784469454567630211237 11550709588022731430664607)
    ·
      refine ⟨17326064382034097145996911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11550709588022731430664607 17326064382034097145996911)
      ·
        refine ⟨25989096573051145718995367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17326064382034097145996911 25989096573051145718995367)
        ·
          refine ⟨38983644859576718578493051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25989096573051145718995367 38983644859576718578493051)
          ·
            refine ⟨58475467289365077867739577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38983644859576718578493051 58475467289365077867739577)
            ·
              refine ⟨43856600467023808400804683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58475467289365077867739577 43856600467023808400804683)
              ·
                refine ⟨65784900700535712601207025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43856600467023808400804683 65784900700535712601207025)
                ·
                  refine ⟨49338675525401784450905269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65784900700535712601207025 49338675525401784450905269)
                  ·
                    refine ⟨4625500830506417292272369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49338675525401784450905269 4625500830506417292272369)
                    ·
                      refine ⟨3469125622879812969204277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4625500830506417292272369 3469125622879812969204277)
                      ·
                        rfl

theorem cell23_6756098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_6756098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756098 prefixEnd_6756098 := by exact prefixLift 6756098
  have htrace : WordTrace (prefixWord ++ tailWord_6756098) baseStart_6756098 baseEnd_6756098 := by
    simpa [prefixWord, tailWord_6756098, baseEnd_6756098] using wordTrace_append hprefix tailTrace_6756098
  have hstable : (prefixWord ++ tailWord_6756098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756098).length < 2 ^ (prefixWord ++ tailWord_6756098).sum := by decide
  have hdescent : baseEnd_6756098 < baseStart_6756098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756131 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 3]
def baseStart_6756131 : Nat := 118140960795 + 6756131 * 2 ^ 59
def prefixEnd_6756131 : Nat := 4983230072969 + 3 ^ 40 * 6756131 * 2
def baseEnd_6756131 : Nat := 3469142567741411340091625

theorem tailTrace_6756131 : CollatzResearch.WordTrace tailWord_6756131 prefixEnd_6756131 3469142567741411340091625 := by
  unfold tailWord_6756131
  simp only [CollatzResearch.WordTrace]
  refine ⟨246416341486698717156796247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164277560991132478104530831 246416341486698717156796247)
  ·
    refine ⟨369624512230048075735194371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246416341486698717156796247 369624512230048075735194371)
    ·
      refine ⟨554436768345072113602791557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369624512230048075735194371 554436768345072113602791557)
      ·
        refine ⟨103956894064701021300523417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 554436768345072113602791557 103956894064701021300523417)
        ·
          refine ⟨77967670548525765975392563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103956894064701021300523417 77967670548525765975392563)
          ·
            refine ⟨116951505822788648963088845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77967670548525765975392563 116951505822788648963088845)
            ·
              refine ⟨43856814683545743361158317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116951505822788648963088845 43856814683545743361158317)
              ·
                refine ⟨16446305506329653760434369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43856814683545743361158317 16446305506329653760434369)
                ·
                  refine ⟨12334729129747240320325777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16446305506329653760434369 12334729129747240320325777)
                  ·
                    refine ⟨9251046847310430240244333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12334729129747240320325777 9251046847310430240244333)
                    ·
                      refine ⟨3469142567741411340091625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9251046847310430240244333 3469142567741411340091625)
                      ·
                        rfl

theorem cell23_6756131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_6756131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756131 prefixEnd_6756131 := by exact prefixLift 6756131
  have htrace : WordTrace (prefixWord ++ tailWord_6756131) baseStart_6756131 baseEnd_6756131 := by
    simpa [prefixWord, tailWord_6756131, baseEnd_6756131] using wordTrace_append hprefix tailTrace_6756131
  have hstable : (prefixWord ++ tailWord_6756131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756131).length < 2 ^ (prefixWord ++ tailWord_6756131).sum := by decide
  have hdescent : baseEnd_6756131 < baseStart_6756131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756178 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_6756178 : Nat := 118140960795 + 6756178 * 2 ^ 59
def prefixEnd_6756178 : Nat := 4983230072969 + 3 ^ 40 * 6756178 * 2
def baseEnd_6756178 : Nat := 3469166701332172656203909

theorem tailTrace_6756178 : CollatzResearch.WordTrace tailWord_6756178 prefixEnd_6756178 3469166701332172656203909 := by
  unfold tailWord_6756178
  simp only [CollatzResearch.WordTrace]
  refine ⟨61604513929382111045939297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164278703811685629455838125 61604513929382111045939297)
  ·
    refine ⟨46203385447036583284454473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61604513929382111045939297 46203385447036583284454473)
    ·
      refine ⟨34652539085277437463340855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46203385447036583284454473 34652539085277437463340855)
      ·
        refine ⟨51978808627916156195011283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34652539085277437463340855 51978808627916156195011283)
        ·
          refine ⟨77968212941874234292516925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51978808627916156195011283 77968212941874234292516925)
          ·
            refine ⟨29238079853202837859693847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77968212941874234292516925 29238079853202837859693847)
            ·
              refine ⟨43857119779804256789540771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29238079853202837859693847 43857119779804256789540771)
              ·
                refine ⟨65785679669706385184311157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43857119779804256789540771 65785679669706385184311157)
                ·
                  refine ⟨6167407469034973611029171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65785679669706385184311157 6167407469034973611029171)
                  ·
                    refine ⟨9251111203552460416543757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6167407469034973611029171 9251111203552460416543757)
                    ·
                      refine ⟨3469166701332172656203909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9251111203552460416543757 3469166701332172656203909)
                      ·
                        rfl

theorem cell23_6756178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_6756178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756178 prefixEnd_6756178 := by exact prefixLift 6756178
  have htrace : WordTrace (prefixWord ++ tailWord_6756178) baseStart_6756178 baseEnd_6756178 := by
    simpa [prefixWord, tailWord_6756178, baseEnd_6756178] using wordTrace_append hprefix tailTrace_6756178
  have hstable : (prefixWord ++ tailWord_6756178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756178).length < 2 ^ (prefixWord ++ tailWord_6756178).sum := by decide
  have hdescent : baseEnd_6756178 < baseStart_6756178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756181 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 3, 5]
def baseStart_6756181 : Nat := 118140960795 + 6756181 * 2 ^ 59
def prefixEnd_6756181 : Nat := 4983230072969 + 3 ^ 40 * 6756181 * 2
def baseEnd_6756181 : Nat := 1156389413924712048155465

theorem tailTrace_6756181 : CollatzResearch.WordTrace tailWord_6756181 prefixEnd_6756181 1156389413924712048155465 := by
  unfold tailWord_6756181
  simp only [CollatzResearch.WordTrace]
  refine ⟨246418165136517575696116397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164278776757678383797410931 246418165136517575696116397)
  ·
    refine ⟨92406811926194090886043649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246418165136517575696116397 92406811926194090886043649)
    ·
      refine ⟨69305108944645568164532737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92406811926194090886043649 69305108944645568164532737)
      ·
        refine ⟨51978831708484176123399553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69305108944645568164532737 51978831708484176123399553)
        ·
          refine ⟨38984123781363132092549665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51978831708484176123399553 38984123781363132092549665)
          ·
            refine ⟨29238092836022349069412249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38984123781363132092549665 29238092836022349069412249)
            ·
              refine ⟨21928569627016761802059187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29238092836022349069412249 21928569627016761802059187)
              ·
                refine ⟨32892854440525142703088781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21928569627016761802059187 32892854440525142703088781)
                ·
                  refine ⟨12334820415196928513658293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32892854440525142703088781 12334820415196928513658293)
                  ·
                    refine ⟨1156389413924712048155465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12334820415196928513658293 1156389413924712048155465)
                    ·
                      rfl

theorem cell23_6756181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_6756181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756181 prefixEnd_6756181 := by exact prefixLift 6756181
  have htrace : WordTrace (prefixWord ++ tailWord_6756181) baseStart_6756181 baseEnd_6756181 := by
    simpa [prefixWord, tailWord_6756181, baseEnd_6756181] using wordTrace_append hprefix tailTrace_6756181
  have hstable : (prefixWord ++ tailWord_6756181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756181).length < 2 ^ (prefixWord ++ tailWord_6756181).sum := by decide
  have hdescent : baseEnd_6756181 < baseStart_6756181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756201 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 1, 8, 2]
def baseStart_6756201 : Nat := 118140960795 + 6756201 * 2 ^ 59
def prefixEnd_6756201 : Nat := 4983230072969 + 3 ^ 40 * 6756201 * 2
def baseEnd_6756201 : Nat := 3469178511387226066216303

theorem tailTrace_6756201 : CollatzResearch.WordTrace tailWord_6756201 prefixEnd_6756201 3469178511387226066216303 := by
  unfold tailWord_6756201
  simp only [CollatzResearch.WordTrace]
  refine ⟨246418894596445119111844457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164279263064296746074562971 246418894596445119111844457)
  ·
    refine ⟨184814170947333839333883343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246418894596445119111844457 184814170947333839333883343)
    ·
      refine ⟨277221256421000759000825015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184814170947333839333883343 277221256421000759000825015)
      ·
        refine ⟨415831884631501138501237523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277221256421000759000825015 415831884631501138501237523)
        ·
          refine ⟨623747826947251707751856285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415831884631501138501237523 623747826947251707751856285)
          ·
            refine ⟨233905435105219390406946107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 623747826947251707751856285 233905435105219390406946107)
            ·
              refine ⟨350858152657829085610419161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233905435105219390406946107 350858152657829085610419161)
              ·
                refine ⟨263143614493371814207814371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350858152657829085610419161 263143614493371814207814371)
                ·
                  refine ⟨394715421740057721311721557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263143614493371814207814371 394715421740057721311721557)
                  ·
                    refine ⟨4625571348516301421621737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 394715421740057721311721557 4625571348516301421621737)
                    ·
                      refine ⟨3469178511387226066216303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4625571348516301421621737 3469178511387226066216303)
                      ·
                        rfl

theorem cell23_6756201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 8, 2].length) (baseStart_6756201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756201 prefixEnd_6756201 := by exact prefixLift 6756201
  have htrace : WordTrace (prefixWord ++ tailWord_6756201) baseStart_6756201 baseEnd_6756201 := by
    simpa [prefixWord, tailWord_6756201, baseEnd_6756201] using wordTrace_append hprefix tailTrace_6756201
  have hstable : (prefixWord ++ tailWord_6756201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756201).length < 2 ^ (prefixWord ++ tailWord_6756201).sum := by decide
  have hdescent : baseEnd_6756201 < baseStart_6756201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756202 : List Nat := [3, 1, 3, 4, 2, 1, 1, 2, 6]
def baseStart_6756202 : Nat := 118140960795 + 6756202 * 2 ^ 59
def prefixEnd_6756202 : Nat := 4983230072969 + 3 ^ 40 * 6756202 * 2
def baseEnd_6756202 : Nat := 385464336096431173589311

theorem tailTrace_6756202 : CollatzResearch.WordTrace tailWord_6756202 prefixEnd_6756202 385464336096431173589311 := by
  unfold tailWord_6756202
  simp only [CollatzResearch.WordTrace]
  refine ⟨61604732767360374070657715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164279287379627664188420573 61604732767360374070657715)
  ·
    refine ⟨92407099151040561105986573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61604732767360374070657715 92407099151040561105986573)
    ·
      refine ⟨34652662181640210414744965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92407099151040561105986573 34652662181640210414744965)
      ·
        refine ⟨6497374159057539452764681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34652662181640210414744965 6497374159057539452764681)
        ·
          refine ⟨4873030619293154589573511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6497374159057539452764681 4873030619293154589573511)
          ·
            refine ⟨7309545928939731884360267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4873030619293154589573511 7309545928939731884360267)
            ·
              refine ⟨10964318893409597826540401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7309545928939731884360267 10964318893409597826540401)
              ·
                refine ⟨8223239170057198369905301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10964318893409597826540401 8223239170057198369905301)
                ·
                  refine ⟨385464336096431173589311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8223239170057198369905301 385464336096431173589311)
                  ·
                    rfl

theorem cell23_6756202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 6].length) (baseStart_6756202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756202 prefixEnd_6756202 := by exact prefixLift 6756202
  have htrace : WordTrace (prefixWord ++ tailWord_6756202) baseStart_6756202 baseEnd_6756202 := by
    simpa [prefixWord, tailWord_6756202, baseEnd_6756202] using wordTrace_append hprefix tailTrace_6756202
  have hstable : (prefixWord ++ tailWord_6756202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756202).length < 2 ^ (prefixWord ++ tailWord_6756202).sum := by decide
  have hdescent : baseEnd_6756202 < baseStart_6756202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756224 : List Nat := [2, 1, 1, 2, 1, 2, 4, 10]
def baseStart_6756224 : Nat := 118140960795 + 6756224 * 2 ^ 59
def prefixEnd_6756224 : Nat := 4983230072969 + 3 ^ 40 * 6756224 * 2
def baseEnd_6756224 : Nat := 128488530423788128749211

theorem tailTrace_6756224 : CollatzResearch.WordTrace tailWord_6756224 prefixEnd_6756224 128488530423788128749211 := by
  unfold tailWord_6756224
  simp only [CollatzResearch.WordTrace]
  refine ⟨123209866737680897019965863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164279822316907862693287817 123209866737680897019965863)
  ·
    refine ⟨184814800106521345529948795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123209866737680897019965863 184814800106521345529948795)
    ·
      refine ⟨277222200159782018294923193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184814800106521345529948795 277222200159782018294923193)
      ·
        refine ⟨207916650119836513721192395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277222200159782018294923193 207916650119836513721192395)
        ·
          refine ⟨311874975179754770581788593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207916650119836513721192395 311874975179754770581788593)
          ·
            refine ⟨233906231384816077936341445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311874975179754770581788593 233906231384816077936341445)
            ·
              refine ⟨43857418384653014613064021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233906231384816077936341445 43857418384653014613064021)
              ·
                refine ⟨128488530423788128749211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43857418384653014613064021 128488530423788128749211)
                ·
                  rfl

theorem cell23_6756224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 10].length) (baseStart_6756224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756224 prefixEnd_6756224 := by exact prefixLift 6756224
  have htrace : WordTrace (prefixWord ++ tailWord_6756224) baseStart_6756224 baseEnd_6756224 := by
    simpa [prefixWord, tailWord_6756224, baseEnd_6756224] using wordTrace_append hprefix tailTrace_6756224
  have hstable : (prefixWord ++ tailWord_6756224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756224).length < 2 ^ (prefixWord ++ tailWord_6756224).sum := by decide
  have hdescent : baseEnd_6756224 < baseStart_6756224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756228 : List Nat := [2, 3, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_6756228 : Nat := 118140960795 + 6756228 * 2 ^ 59
def prefixEnd_6756228 : Nat := 4983230072969 + 3 ^ 40 * 6756228 * 2
def baseEnd_6756228 : Nat := 1156397458454965820192893

theorem tailTrace_6756228 : CollatzResearch.WordTrace tailWord_6756228 prefixEnd_6756228 1156397458454965820192893 := by
  unfold tailWord_6756228
  simp only [CollatzResearch.WordTrace]
  refine ⟨123209939683673651361538669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164279919578231535148718225 123209939683673651361538669)
  ·
    refine ⟨46203727381377619260577001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123209939683673651361538669 46203727381377619260577001)
    ·
      refine ⟨34652795536033214445432751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46203727381377619260577001 34652795536033214445432751)
      ·
        refine ⟨51979193304049821668149127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34652795536033214445432751 51979193304049821668149127)
        ·
          refine ⟨77968789956074732502223691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51979193304049821668149127 77968789956074732502223691)
          ·
            refine ⟨116953184934112098753335537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77968789956074732502223691 116953184934112098753335537)
            ·
              refine ⟨87714888700584074065001653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116953184934112098753335537 87714888700584074065001653)
              ·
                refine ⟨8223270815679756943593905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87714888700584074065001653 8223270815679756943593905)
                ·
                  refine ⟨6167453111759817707695429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8223270815679756943593905 6167453111759817707695429)
                  ·
                    refine ⟨1156397458454965820192893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6167453111759817707695429 1156397458454965820192893)
                    ·
                      rfl

theorem cell23_6756228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_6756228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756228 prefixEnd_6756228 := by exact prefixLift 6756228
  have htrace : WordTrace (prefixWord ++ tailWord_6756228) baseStart_6756228 baseEnd_6756228 := by
    simpa [prefixWord, tailWord_6756228, baseEnd_6756228] using wordTrace_append hprefix tailTrace_6756228
  have hstable : (prefixWord ++ tailWord_6756228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756228).length < 2 ^ (prefixWord ++ tailWord_6756228).sum := by decide
  have hdescent : baseEnd_6756228 < baseStart_6756228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756241 : List Nat := [1, 2, 2, 1, 1, 1, 8, 7]
def baseStart_6756241 : Nat := 118140960795 + 6756241 * 2 ^ 59
def prefixEnd_6756241 : Nat := 4983230072969 + 3 ^ 40 * 6756241 * 2
def baseEnd_6756241 : Nat := 128488853726422441100597

theorem tailTrace_6756241 : CollatzResearch.WordTrace tailWord_6756241 prefixEnd_6756241 128488853726422441100597 := by
  unfold tailWord_6756241
  simp only [CollatzResearch.WordTrace]
  refine ⟨246420353516300205943300577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164280235677533470628867051 246420353516300205943300577)
  ·
    refine ⟨184815265137225154457475433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246420353516300205943300577 184815265137225154457475433)
    ·
      refine ⟨138611448852918865843106575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184815265137225154457475433 138611448852918865843106575)
      ·
        refine ⟨207917173279378298764659863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138611448852918865843106575 207917173279378298764659863)
        ·
          refine ⟨311875759919067448146989795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207917173279378298764659863 311875759919067448146989795)
          ·
            refine ⟨467813639878601172220484693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311875759919067448146989795 467813639878601172220484693)
            ·
              refine ⟨5482191092327357486958805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 467813639878601172220484693 5482191092327357486958805)
              ·
                refine ⟨128488853726422441100597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5482191092327357486958805 128488853726422441100597)
                ·
                  rfl

theorem cell23_6756241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 7].length) (baseStart_6756241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756241 prefixEnd_6756241 := by exact prefixLift 6756241
  have htrace : WordTrace (prefixWord ++ tailWord_6756241) baseStart_6756241 baseEnd_6756241 := by
    simpa [prefixWord, tailWord_6756241, baseEnd_6756241] using wordTrace_append hprefix tailTrace_6756241
  have hstable : (prefixWord ++ tailWord_6756241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756241).length < 2 ^ (prefixWord ++ tailWord_6756241).sum := by decide
  have hdescent : baseEnd_6756241 < baseStart_6756241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756258 : List Nat := [3, 3, 1, 2, 3, 2, 9]
def baseStart_6756258 : Nat := 118140960795 + 6756258 * 2 ^ 59
def prefixEnd_6756258 : Nat := 4983230072969 + 3 ^ 40 * 6756258 * 2
def baseEnd_6756258 : Nat := 42829725676352251150661

theorem tailTrace_6756258 : CollatzResearch.WordTrace tailWord_6756258 prefixEnd_6756258 42829725676352251150661 := by
  unfold tailWord_6756258
  simp only [CollatzResearch.WordTrace]
  refine ⟨61605243389309654461667357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164280649038159078564446285 61605243389309654461667357)
  ·
    refine ⟨23101966270991120423125259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61605243389309654461667357 23101966270991120423125259)
    ·
      refine ⟨34652949406486680634687889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23101966270991120423125259 34652949406486680634687889)
      ·
        refine ⟨25989712054865010476015917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34652949406486680634687889 25989712054865010476015917)
        ·
          refine ⟨9746142020574378928505969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25989712054865010476015917 9746142020574378928505969)
          ·
            refine ⟨7309606515430784196379477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9746142020574378928505969 7309606515430784196379477)
            ·
              refine ⟨42829725676352251150661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7309606515430784196379477 42829725676352251150661)
              ·
                rfl

theorem cell23_6756258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 9].length) (baseStart_6756258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756258 prefixEnd_6756258 := by exact prefixLift 6756258
  have htrace : WordTrace (prefixWord ++ tailWord_6756258) baseStart_6756258 baseEnd_6756258 := by
    simpa [prefixWord, tailWord_6756258, baseEnd_6756258] using wordTrace_append hprefix tailTrace_6756258
  have hstable : (prefixWord ++ tailWord_6756258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756258).length < 2 ^ (prefixWord ++ tailWord_6756258).sum := by decide
  have hdescent : baseEnd_6756258 < baseStart_6756258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756311 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_6756311 : Nat := 118140960795 + 6756311 * 2 ^ 59
def prefixEnd_6756311 : Nat := 4983230072969 + 3 ^ 40 * 6756311 * 2
def baseEnd_6756311 : Nat := 3469234994259220635840797

theorem tailTrace_6756311 : CollatzResearch.WordTrace tailWord_6756311 prefixEnd_6756311 3469234994259220635840797 := by
  unfold tailWord_6756311
  simp only [CollatzResearch.WordTrace]
  refine ⟨246422906626046607898348787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164281937750697738598899191 246422906626046607898348787)
  ·
    refine ⟨369634359939069911847523181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246422906626046607898348787 369634359939069911847523181)
    ·
      refine ⟨138612884977151216942821193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369634359939069911847523181 138612884977151216942821193)
      ·
        refine ⟨103959663732863412707115895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138612884977151216942821193 103959663732863412707115895)
        ·
          refine ⟨155939495599295119060673843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103959663732863412707115895 155939495599295119060673843)
          ·
            refine ⟨233909243398942678591010765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155939495599295119060673843 233909243398942678591010765)
            ·
              refine ⟨87715966274603504471629037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233909243398942678591010765 87715966274603504471629037)
              ·
                refine ⟨32893487352976314176860889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87715966274603504471629037 32893487352976314176860889)
                ·
                  refine ⟨24670115514732235632645667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32893487352976314176860889 24670115514732235632645667)
                  ·
                    refine ⟨37005173272098353448968501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24670115514732235632645667 37005173272098353448968501)
                    ·
                      refine ⟨3469234994259220635840797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37005173272098353448968501 3469234994259220635840797)
                      ·
                        rfl

theorem cell23_6756311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_6756311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756311 prefixEnd_6756311 := by exact prefixLift 6756311
  have htrace : WordTrace (prefixWord ++ tailWord_6756311) baseStart_6756311 baseEnd_6756311 := by
    simpa [prefixWord, tailWord_6756311, baseEnd_6756311] using wordTrace_append hprefix tailTrace_6756311
  have hstable : (prefixWord ++ tailWord_6756311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756311).length < 2 ^ (prefixWord ++ tailWord_6756311).sum := by decide
  have hdescent : baseEnd_6756311 < baseStart_6756311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756312 : List Nat := [2, 1, 2, 2, 2, 2, 5, 1, 1, 3, 2]
def baseStart_6756312 : Nat := 118140960795 + 6756312 * 2 ^ 59
def prefixEnd_6756312 : Nat := 4983230072969 + 3 ^ 40 * 6756312 * 2
def baseEnd_6756312 : Nat := 3469235507739875131928293

theorem tailTrace_6756312 : CollatzResearch.WordTrace tailWord_6756312 prefixEnd_6756312 3469235507739875131928293 := by
  unfold tailWord_6756312
  simp only [CollatzResearch.WordTrace]
  refine ⟨123211471549521492534567595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164281962066028656712756793 123211471549521492534567595)
  ·
    refine ⟨184817207324282238801851393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123211471549521492534567595 184817207324282238801851393)
    ·
      refine ⟨138612905493211679101388545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184817207324282238801851393 138612905493211679101388545)
      ·
        refine ⟨103959679119908759326041409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138612905493211679101388545 103959679119908759326041409)
        ·
          refine ⟨77969759339931569494531057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103959679119908759326041409 77969759339931569494531057)
          ·
            refine ⟨58477319504948677120898293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77969759339931569494531057 58477319504948677120898293)
            ·
              refine ⟨5482248703588938480084215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58477319504948677120898293 5482248703588938480084215)
              ·
                refine ⟨8223373055383407720126323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5482248703588938480084215 8223373055383407720126323)
                ·
                  refine ⟨12335059583075111580189485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8223373055383407720126323 12335059583075111580189485)
                  ·
                    refine ⟨4625647343653166842571057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12335059583075111580189485 4625647343653166842571057)
                    ·
                      refine ⟨3469235507739875131928293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4625647343653166842571057 3469235507739875131928293)
                      ·
                        rfl

theorem cell23_6756312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_6756312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756312 prefixEnd_6756312 := by exact prefixLift 6756312
  have htrace : WordTrace (prefixWord ++ tailWord_6756312) baseStart_6756312 baseEnd_6756312 := by
    simpa [prefixWord, tailWord_6756312, baseEnd_6756312] using wordTrace_append hprefix tailTrace_6756312
  have hstable : (prefixWord ++ tailWord_6756312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756312).length < 2 ^ (prefixWord ++ tailWord_6756312).sum := by decide
  have hdescent : baseEnd_6756312 < baseStart_6756312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756368 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 4, 5, 2]
def baseStart_6756368 : Nat := 118140960795 + 6756368 * 2 ^ 59
def prefixEnd_6756368 : Nat := 4983230072969 + 3 ^ 40 * 6756368 * 2
def baseEnd_6756368 : Nat := 3469264262656526912828035

theorem tailTrace_6756368 : CollatzResearch.WordTrace tailWord_6756368 prefixEnd_6756368 3469264262656526912828035 := by
  unfold tailWord_6756368
  simp only [CollatzResearch.WordTrace]
  refine ⟨123212492793420053316586879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164283323724560071088782505 123212492793420053316586879)
  ·
    refine ⟨184818739190130079974880319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123212492793420053316586879 184818739190130079974880319)
    ·
      refine ⟨277228108785195119962320479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184818739190130079974880319 277228108785195119962320479)
      ·
        refine ⟨415842163177792679943480719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277228108785195119962320479 415842163177792679943480719)
        ·
          refine ⟨623763244766689019915221079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415842163177792679943480719 623763244766689019915221079)
          ·
            refine ⟨935644867150033529872831619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623763244766689019915221079 935644867150033529872831619)
            ·
              refine ⟨1403467300725050294809247429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935644867150033529872831619 1403467300725050294809247429)
              ·
                refine ⟨263150118885946930276733893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1403467300725050294809247429 263150118885946930276733893)
                ·
                  refine ⟨49340647291115049426887605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263150118885946930276733893 49340647291115049426887605)
                  ·
                    refine ⟨4625685683542035883770713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49340647291115049426887605 4625685683542035883770713)
                    ·
                      refine ⟨3469264262656526912828035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4625685683542035883770713 3469264262656526912828035)
                      ·
                        rfl

theorem cell23_6756368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 5, 2].length) (baseStart_6756368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756368 prefixEnd_6756368 := by exact prefixLift 6756368
  have htrace : WordTrace (prefixWord ++ tailWord_6756368) baseStart_6756368 baseEnd_6756368 := by
    simpa [prefixWord, tailWord_6756368, baseEnd_6756368] using wordTrace_append hprefix tailTrace_6756368
  have hstable : (prefixWord ++ tailWord_6756368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756368).length < 2 ^ (prefixWord ++ tailWord_6756368).sum := by decide
  have hdescent : baseEnd_6756368 < baseStart_6756368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756371 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 5]
def baseStart_6756371 : Nat := 118140960795 + 6756371 * 2 ^ 59
def prefixEnd_6756371 : Nat := 4983230072969 + 3 ^ 40 * 6756371 * 2
def baseEnd_6756371 : Nat := 3469265803098490401090521

theorem tailTrace_6756371 : CollatzResearch.WordTrace tailWord_6756371 prefixEnd_6756371 3469265803098490401090521 := by
  unfold tailWord_6756371
  simp only [CollatzResearch.WordTrace]
  refine ⟨246425095005829238145532967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164283396670552825430355311 246425095005829238145532967)
  ·
    refine ⟨369637642508743857218299451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246425095005829238145532967 369637642508743857218299451)
    ·
      refine ⟨554456463763115785827449177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369637642508743857218299451 554456463763115785827449177)
      ·
        refine ⟨415842347822336839370586883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554456463763115785827449177 415842347822336839370586883)
        ·
          refine ⟨623763521733505259055880325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415842347822336839370586883 623763521733505259055880325)
          ·
            refine ⟨116955660325032236072977561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 623763521733505259055880325 116955660325032236072977561)
            ·
              refine ⟨87716745243774177054733171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116955660325032236072977561 87716745243774177054733171)
              ·
                refine ⟨131575117865661265582099757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87716745243774177054733171 131575117865661265582099757)
                ·
                  refine ⟨49340669199622974593287409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131575117865661265582099757 49340669199622974593287409)
                  ·
                    refine ⟨37005501899717230944965557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49340669199622974593287409 37005501899717230944965557)
                    ·
                      refine ⟨3469265803098490401090521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37005501899717230944965557 3469265803098490401090521)
                      ·
                        rfl

theorem cell23_6756371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_6756371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756371 prefixEnd_6756371 := by exact prefixLift 6756371
  have htrace : WordTrace (prefixWord ++ tailWord_6756371) baseStart_6756371 baseEnd_6756371 := by
    simpa [prefixWord, tailWord_6756371, baseEnd_6756371] using wordTrace_append hprefix tailTrace_6756371
  have hstable : (prefixWord ++ tailWord_6756371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756371).length < 2 ^ (prefixWord ++ tailWord_6756371).sum := by decide
  have hdescent : baseEnd_6756371 < baseStart_6756371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756411 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 6]
def baseStart_6756411 : Nat := 118140960795 + 6756411 * 2 ^ 59
def prefixEnd_6756411 : Nat := 4983230072969 + 3 ^ 40 * 6756411 * 2
def baseEnd_6756411 : Nat := 3469286342324670244590337

theorem tailTrace_6756411 : CollatzResearch.WordTrace tailWord_6756411 prefixEnd_6756411 3469286342324670244590337 := by
  unfold tailWord_6756411
  simp only [CollatzResearch.WordTrace]
  refine ⟨246426553925684324976989087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164284369283789549984659391 246426553925684324976989087)
  ·
    refine ⟨369639830888526487465483631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246426553925684324976989087 369639830888526487465483631)
    ·
      refine ⟨554459746332789731198225447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369639830888526487465483631 554459746332789731198225447)
      ·
        refine ⟨831689619499184596797338171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554459746332789731198225447 831689619499184596797338171)
        ·
          refine ⟨1247534429248776895196007257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 831689619499184596797338171 1247534429248776895196007257)
          ·
            refine ⟨935650821936582671397005443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1247534429248776895196007257 935650821936582671397005443)
            ·
              refine ⟨1403476232904874007095508165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935650821936582671397005443 1403476232904874007095508165)
              ·
                refine ⟨263151793669663876330407781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1403476232904874007095508165 263151793669663876330407781)
                ·
                  refine ⟨49340961313061976811951459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263151793669663876330407781 49340961313061976811951459)
                  ·
                    refine ⟨74011441969592965217927189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49340961313061976811951459 74011441969592965217927189)
                    ·
                      refine ⟨3469286342324670244590337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74011441969592965217927189 3469286342324670244590337)
                      ·
                        rfl

theorem cell23_6756411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 6].length) (baseStart_6756411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756411 prefixEnd_6756411 := by exact prefixLift 6756411
  have htrace : WordTrace (prefixWord ++ tailWord_6756411) baseStart_6756411 baseEnd_6756411 := by
    simpa [prefixWord, tailWord_6756411, baseEnd_6756411] using wordTrace_append hprefix tailTrace_6756411
  have hstable : (prefixWord ++ tailWord_6756411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756411).length < 2 ^ (prefixWord ++ tailWord_6756411).sum := by decide
  have hdescent : baseEnd_6756411 < baseStart_6756411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756465 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 5, 1, 3]
def baseStart_6756465 : Nat := 118140960795 + 6756465 * 2 ^ 59
def prefixEnd_6756465 : Nat := 4983230072969 + 3 ^ 40 * 6756465 * 2
def baseEnd_6756465 : Nat := 3469314070280013033315089

theorem tailTrace_6756465 : CollatzResearch.WordTrace tailWord_6756465 prefixEnd_6756465 3469314070280013033315089 := by
  unfold tailWord_6756465
  simp only [CollatzResearch.WordTrace]
  refine ⟨246428523467488692199454849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164285682311659128132969899 246428523467488692199454849)
  ·
    refine ⟨184821392600616519149591137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246428523467488692199454849 184821392600616519149591137)
    ·
      refine ⟨138616044450462389362193353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184821392600616519149591137 138616044450462389362193353)
      ·
        refine ⟨103962033337846792021645015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138616044450462389362193353 103962033337846792021645015)
        ·
          refine ⟨155943050006770188032467523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103962033337846792021645015 155943050006770188032467523)
          ·
            refine ⟨233914575010155282048701285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155943050006770188032467523 233914575010155282048701285)
            ·
              refine ⟨43858982814404115384131491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233914575010155282048701285 43858982814404115384131491)
              ·
                refine ⟨65788474221606173076197237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43858982814404115384131491 65788474221606173076197237)
                ·
                  refine ⟨6167669458275578725893491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65788474221606173076197237 6167669458275578725893491)
                  ·
                    refine ⟨9251504187413368088840237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6167669458275578725893491 9251504187413368088840237)
                    ·
                      refine ⟨3469314070280013033315089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9251504187413368088840237 3469314070280013033315089)
                      ·
                        rfl

theorem cell23_6756465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_6756465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756465 prefixEnd_6756465 := by exact prefixLift 6756465
  have htrace : WordTrace (prefixWord ++ tailWord_6756465) baseStart_6756465 baseEnd_6756465 := by
    simpa [prefixWord, tailWord_6756465, baseEnd_6756465] using wordTrace_append hprefix tailTrace_6756465
  have hstable : (prefixWord ++ tailWord_6756465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756465).length < 2 ^ (prefixWord ++ tailWord_6756465).sum := by decide
  have hdescent : baseEnd_6756465 < baseStart_6756465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756526 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6756526 : Nat := 118140960795 + 6756526 * 2 ^ 59
def prefixEnd_6756526 : Nat := 4983230072969 + 3 ^ 40 * 6756526 * 2
def baseEnd_6756526 : Nat := 3469345392599937294652309

theorem tailTrace_6756526 : CollatzResearch.WordTrace tailWord_6756526 prefixEnd_6756526 3469345392599937294652309 := by
  unfold tailWord_6756526
  simp only [CollatzResearch.WordTrace]
  refine ⟨30803843540033462452178179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164287165546845133078283621 30803843540033462452178179)
  ·
    refine ⟨46205765310050193678267269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30803843540033462452178179 46205765310050193678267269)
    ·
      refine ⟨8663580995634411314675113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46205765310050193678267269 8663580995634411314675113)
      ·
        refine ⟨6497685746725808486006335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8663580995634411314675113 6497685746725808486006335)
        ·
          refine ⟨9746528620088712729009503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6497685746725808486006335 9746528620088712729009503)
          ·
            refine ⟨14619792930133069093514255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9746528620088712729009503 14619792930133069093514255)
            ·
              refine ⟨21929689395199603640271383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14619792930133069093514255 21929689395199603640271383)
              ·
                refine ⟨32894534092799405460407075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21929689395199603640271383 32894534092799405460407075)
                ·
                  refine ⟨49341801139199108190610613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32894534092799405460407075 49341801139199108190610613)
                  ·
                    refine ⟨4625793856799916392869745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49341801139199108190610613 4625793856799916392869745)
                    ·
                      refine ⟨3469345392599937294652309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4625793856799916392869745 3469345392599937294652309)
                      ·
                        rfl

theorem cell23_6756526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6756526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756526 prefixEnd_6756526 := by exact prefixLift 6756526
  have htrace : WordTrace (prefixWord ++ tailWord_6756526) baseStart_6756526 baseEnd_6756526 := by
    simpa [prefixWord, tailWord_6756526, baseEnd_6756526] using wordTrace_append hprefix tailTrace_6756526
  have hstable : (prefixWord ++ tailWord_6756526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756526).length < 2 ^ (prefixWord ++ tailWord_6756526).sum := by decide
  have hdescent : baseEnd_6756526 < baseStart_6756526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756533 : List Nat := [1, 3, 3, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_6756533 : Nat := 118140960795 + 6756533 * 2 ^ 59
def prefixEnd_6756533 : Nat := 4983230072969 + 3 ^ 40 * 6756533 * 2
def baseEnd_6756533 : Nat := 3469348986964518767264777

theorem tailTrace_6756533 : CollatzResearch.WordTrace tailWord_6756533 prefixEnd_6756533 3469348986964518767264777 := by
  unfold tailWord_6756533
  simp only [CollatzResearch.WordTrace]
  refine ⟨246431003631242339812930253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164287335754161559875286835 246431003631242339812930253)
  ·
    refine ⟨92411626361715877429848845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246431003631242339812930253 92411626361715877429848845)
    ·
      refine ⟨34654359885643454036193317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92411626361715877429848845 34654359885643454036193317)
      ·
        refine ⟨6497692478558147631786247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34654359885643454036193317 6497692478558147631786247)
        ·
          refine ⟨9746538717837221447679371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6497692478558147631786247 9746538717837221447679371)
          ·
            refine ⟨14619808076755832171519057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9746538717837221447679371 14619808076755832171519057)
            ·
              refine ⟨10964856057566874128639293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14619808076755832171519057 10964856057566874128639293)
              ·
                refine ⟨4111821021587577798239735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10964856057566874128639293 4111821021587577798239735)
                ·
                  refine ⟨6167731532381366697359603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4111821021587577798239735 6167731532381366697359603)
                  ·
                    refine ⟨9251597298572050046039405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6167731532381366697359603 9251597298572050046039405)
                    ·
                      refine ⟨3469348986964518767264777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9251597298572050046039405 3469348986964518767264777)
                      ·
                        rfl

theorem cell23_6756533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_6756533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756533 prefixEnd_6756533 := by exact prefixLift 6756533
  have htrace : WordTrace (prefixWord ++ tailWord_6756533) baseStart_6756533 baseEnd_6756533 := by
    simpa [prefixWord, tailWord_6756533, baseEnd_6756533] using wordTrace_append hprefix tailTrace_6756533
  have hstable : (prefixWord ++ tailWord_6756533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756533).length < 2 ^ (prefixWord ++ tailWord_6756533).sum := by decide
  have hdescent : baseEnd_6756533 < baseStart_6756533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756535 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_6756535 : Nat := 118140960795 + 6756535 * 2 ^ 59
def prefixEnd_6756535 : Nat := 4983230072969 + 3 ^ 40 * 6756535 * 2
def baseEnd_6756535 : Nat := 3469350013925827759439767

theorem tailTrace_6756535 : CollatzResearch.WordTrace tailWord_6756535 prefixEnd_6756535 3469350013925827759439767 := by
  unfold tailWord_6756535
  simp only [CollatzResearch.WordTrace]
  refine ⟨246431076577235094154503059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164287384384823396103002039 246431076577235094154503059)
  ·
    refine ⟨369646614865852641231754589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246431076577235094154503059 369646614865852641231754589)
    ·
      refine ⟨138617480574694740461907971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369646614865852641231754589 138617480574694740461907971)
      ·
        refine ⟨207926220862042110692861957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138617480574694740461907971 207926220862042110692861957)
        ·
          refine ⟨38986166411632895754911617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207926220862042110692861957 38986166411632895754911617)
          ·
            refine ⟨29239624808724671816183713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38986166411632895754911617 29239624808724671816183713)
            ·
              refine ⟨21929718606543503862137785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29239624808724671816183713 21929718606543503862137785)
              ·
                refine ⟨16447288954907627896603339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21929718606543503862137785 16447288954907627896603339)
                ·
                  refine ⟨24670933432361441844905009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16447288954907627896603339 24670933432361441844905009)
                  ·
                    refine ⟨18503200074271081383678757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24670933432361441844905009 18503200074271081383678757)
                    ·
                      refine ⟨3469350013925827759439767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18503200074271081383678757 3469350013925827759439767)
                      ·
                        rfl

theorem cell23_6756535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_6756535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756535 prefixEnd_6756535 := by exact prefixLift 6756535
  have htrace : WordTrace (prefixWord ++ tailWord_6756535) baseStart_6756535 baseEnd_6756535 := by
    simpa [prefixWord, tailWord_6756535, baseEnd_6756535] using wordTrace_append hprefix tailTrace_6756535
  have hstable : (prefixWord ++ tailWord_6756535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756535).length < 2 ^ (prefixWord ++ tailWord_6756535).sum := by decide
  have hdescent : baseEnd_6756535 < baseStart_6756535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756579 : List Nat := [1, 1, 1, 8, 1, 2, 2, 7]
def baseStart_6756579 : Nat := 118140960795 + 6756579 * 2 ^ 59
def prefixEnd_6756579 : Nat := 4983230072969 + 3 ^ 40 * 6756579 * 2
def baseEnd_6756579 : Nat := 128495281743504651381095

theorem tailTrace_6756579 : CollatzResearch.WordTrace tailWord_6756579 prefixEnd_6756579 128495281743504651381095 := by
  unfold tailWord_6756579
  simp only [CollatzResearch.WordTrace]
  refine ⟨246432681389075689669104791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164288454259383793112736527 246432681389075689669104791)
  ·
    refine ⟨369649022083613534503657187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246432681389075689669104791 369649022083613534503657187)
    ·
      refine ⟨554473533125420301755485781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369649022083613534503657187 554473533125420301755485781)
      ·
        refine ⟨6497736716313519161197099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 554473533125420301755485781 6497736716313519161197099)
        ·
          refine ⟨9746605074470278741795649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6497736716313519161197099 9746605074470278741795649)
          ·
            refine ⟨7309953805852709056346737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9746605074470278741795649 7309953805852709056346737)
            ·
              refine ⟨5482465354389531792260053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7309953805852709056346737 5482465354389531792260053)
              ·
                refine ⟨128495281743504651381095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5482465354389531792260053 128495281743504651381095)
                ·
                  rfl

theorem cell23_6756579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 7].length) (baseStart_6756579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756579 prefixEnd_6756579 := by exact prefixLift 6756579
  have htrace : WordTrace (prefixWord ++ tailWord_6756579) baseStart_6756579 baseEnd_6756579 := by
    simpa [prefixWord, tailWord_6756579, baseEnd_6756579] using wordTrace_append hprefix tailTrace_6756579
  have hstable : (prefixWord ++ tailWord_6756579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756579).length < 2 ^ (prefixWord ++ tailWord_6756579).sum := by decide
  have hdescent : baseEnd_6756579 < baseStart_6756579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756675 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 5]
def baseStart_6756675 : Nat := 118140960795 + 6756675 * 2 ^ 59
def prefixEnd_6756675 : Nat := 4983230072969 + 3 ^ 40 * 6756675 * 2
def baseEnd_6756675 : Nat := 3469421901217457211689123

theorem tailTrace_6756675 : CollatzResearch.WordTrace tailWord_6756675 prefixEnd_6756675 3469421901217457211689123 := by
  unfold tailWord_6756675
  simp only [CollatzResearch.WordTrace]
  refine ⟨246436182796727898064599479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164290788531151932043066319 246436182796727898064599479)
  ·
    refine ⟨369654274195091847096899219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246436182796727898064599479 369654274195091847096899219)
    ·
      refine ⟨554481411292637770645348829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369654274195091847096899219 554481411292637770645348829)
      ·
        refine ⟨207930529234739163992005811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 554481411292637770645348829 207930529234739163992005811)
        ·
          refine ⟨311895793852108745988008717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207930529234739163992005811 311895793852108745988008717)
          ·
            refine ⟨116960922694540779745503269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311895793852108745988008717 116960922694540779745503269)
            ·
              refine ⟨21930173005226396202281863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116960922694540779745503269 21930173005226396202281863)
              ·
                refine ⟨32895259507839594303422795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21930173005226396202281863 32895259507839594303422795)
                ·
                  refine ⟨49342889261759391455134193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32895259507839594303422795 49342889261759391455134193)
                  ·
                    refine ⟨37007166946319543591350645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49342889261759391455134193 37007166946319543591350645)
                    ·
                      refine ⟨3469421901217457211689123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37007166946319543591350645 3469421901217457211689123)
                      ·
                        rfl

theorem cell23_6756675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_6756675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756675 prefixEnd_6756675 := by exact prefixLift 6756675
  have htrace : WordTrace (prefixWord ++ tailWord_6756675) baseStart_6756675 baseEnd_6756675 := by
    simpa [prefixWord, tailWord_6756675, baseEnd_6756675] using wordTrace_append hprefix tailTrace_6756675
  have hstable : (prefixWord ++ tailWord_6756675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756675).length < 2 ^ (prefixWord ++ tailWord_6756675).sum := by decide
  have hdescent : baseEnd_6756675 < baseStart_6756675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756792 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_6756792 : Nat := 118140960795 + 6756792 * 2 ^ 59
def prefixEnd_6756792 : Nat := 4983230072969 + 3 ^ 40 * 6756792 * 2
def baseEnd_6756792 : Nat := 3469481978454033253926085

theorem tailTrace_6756792 : CollatzResearch.WordTrace tailWord_6756792 prefixEnd_6756792 3469481978454033253926085 := by
  unfold tailWord_6756792
  simp only [CollatzResearch.WordTrace]
  refine ⟨123220225068652013523304315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164293633424869351364405753 123220225068652013523304315)
  ·
    refine ⟨184830337602978020284956473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123220225068652013523304315 184830337602978020284956473)
    ·
      refine ⟨138622753202233515213717355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184830337602978020284956473 138622753202233515213717355)
      ·
        refine ⟨207934129803350272820576033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138622753202233515213717355 207934129803350272820576033)
        ·
          refine ⟨155950597352512704615432025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207934129803350272820576033 155950597352512704615432025)
          ·
            refine ⟨116962948014384528461574019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155950597352512704615432025 116962948014384528461574019)
            ·
              refine ⟨175444422021576792692361029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116962948014384528461574019 175444422021576792692361029)
              ·
                refine ⟨32895829129045648629817693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175444422021576792692361029 32895829129045648629817693)
                ·
                  refine ⟨12335935923392118236181635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32895829129045648629817693 12335935923392118236181635)
                  ·
                    refine ⟨18503903885088177354272453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12335935923392118236181635 18503903885088177354272453)
                    ·
                      refine ⟨3469481978454033253926085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18503903885088177354272453 3469481978454033253926085)
                      ·
                        rfl

theorem cell23_6756792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_6756792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756792 prefixEnd_6756792 := by exact prefixLift 6756792
  have htrace : WordTrace (prefixWord ++ tailWord_6756792) baseStart_6756792 baseEnd_6756792 := by
    simpa [prefixWord, tailWord_6756792, baseEnd_6756792] using wordTrace_append hprefix tailTrace_6756792
  have hstable : (prefixWord ++ tailWord_6756792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756792).length < 2 ^ (prefixWord ++ tailWord_6756792).sum := by decide
  have hdescent : baseEnd_6756792 < baseStart_6756792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756809 : List Nat := [1, 2, 1, 1, 2, 1, 7, 2, 1, 1, 4]
def baseStart_6756809 : Nat := 118140960795 + 6756809 * 2 ^ 59
def prefixEnd_6756809 : Nat := 4983230072969 + 3 ^ 40 * 6756809 * 2
def baseEnd_6756809 : Nat := 3469490707625159687413507

theorem tailTrace_6756809 : CollatzResearch.WordTrace tailWord_6756809 prefixEnd_6756809 3469490707625159687413507 := by
  unfold tailWord_6756809
  simp only [CollatzResearch.WordTrace]
  refine ⟨246441070178242438949977481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164294046785494959299984987 246441070178242438949977481)
  ·
    refine ⟨184830802633681829212483111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246441070178242438949977481 184830802633681829212483111)
    ·
      refine ⟨277246203950522743818724667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184830802633681829212483111 277246203950522743818724667)
      ·
        refine ⟨415869305925784115728087001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277246203950522743818724667 415869305925784115728087001)
        ·
          refine ⟨311901979444338086796065251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415869305925784115728087001 311901979444338086796065251)
          ·
            refine ⟨467852969166507130194097877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311901979444338086796065251 467852969166507130194097877)
            ·
              refine ⟨10965303964840010863924169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 467852969166507130194097877 10965303964840010863924169)
              ·
                refine ⟨8223977973630008147943127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10965303964840010863924169 8223977973630008147943127)
                ·
                  refine ⟨12335966960445012221914691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8223977973630008147943127 12335966960445012221914691)
                  ·
                    refine ⟨18503950440667518332872037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12335966960445012221914691 18503950440667518332872037)
                    ·
                      refine ⟨3469490707625159687413507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18503950440667518332872037 3469490707625159687413507)
                      ·
                        rfl

theorem cell23_6756809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 1, 4].length) (baseStart_6756809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756809 prefixEnd_6756809 := by exact prefixLift 6756809
  have htrace : WordTrace (prefixWord ++ tailWord_6756809) baseStart_6756809 baseEnd_6756809 := by
    simpa [prefixWord, tailWord_6756809, baseEnd_6756809] using wordTrace_append hprefix tailTrace_6756809
  have hstable : (prefixWord ++ tailWord_6756809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756809).length < 2 ^ (prefixWord ++ tailWord_6756809).sum := by decide
  have hdescent : baseEnd_6756809 < baseStart_6756809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756826 : List Nat := [3, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4]
def baseStart_6756826 : Nat := 118140960795 + 6756826 * 2 ^ 59
def prefixEnd_6756826 : Nat := 4983230072969 + 3 ^ 40 * 6756826 * 2
def baseEnd_6756826 : Nat := 3469499436796286120900929

theorem tailTrace_6756826 : CollatzResearch.WordTrace tailWord_6756826 prefixEnd_6756826 3469499436796286120900929 := by
  unfold tailWord_6756826
  simp only [CollatzResearch.WordTrace]
  refine ⟨61610422554795212713336583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164294460146120567235564221 61610422554795212713336583)
  ·
    refine ⟨92415633832192819070004875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61610422554795212713336583 92415633832192819070004875)
    ·
      refine ⟨138623450748289228605007313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92415633832192819070004875 138623450748289228605007313)
      ·
        refine ⟨103967588061216921453755485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138623450748289228605007313 103967588061216921453755485)
        ·
          refine ⟨38987845522956345545158307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103967588061216921453755485 38987845522956345545158307)
          ·
            refine ⟨58481768284434518317737461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38987845522956345545158307 58481768284434518317737461)
            ·
              refine ⟨5482665776665736092287887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58481768284434518317737461 5482665776665736092287887)
              ·
                refine ⟨8223998664998604138431831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5482665776665736092287887 8223998664998604138431831)
                ·
                  refine ⟨12335997997497906207647747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8223998664998604138431831 12335997997497906207647747)
                  ·
                    refine ⟨18503996996246859311471621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12335997997497906207647747 18503996996246859311471621)
                    ·
                      refine ⟨3469499436796286120900929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18503996996246859311471621 3469499436796286120900929)
                      ·
                        rfl

theorem cell23_6756826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_6756826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756826 prefixEnd_6756826 := by exact prefixLift 6756826
  have htrace : WordTrace (prefixWord ++ tailWord_6756826) baseStart_6756826 baseEnd_6756826 := by
    simpa [prefixWord, tailWord_6756826, baseEnd_6756826] using wordTrace_append hprefix tailTrace_6756826
  have hstable : (prefixWord ++ tailWord_6756826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756826).length < 2 ^ (prefixWord ++ tailWord_6756826).sum := by decide
  have hdescent : baseEnd_6756826 < baseStart_6756826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756837 : List Nat := [1, 3, 1, 5, 2, 2, 2, 2, 1, 1, 3]
def baseStart_6756837 : Nat := 118140960795 + 6756837 * 2 ^ 59
def prefixEnd_6756837 : Nat := 4983230072969 + 3 ^ 40 * 6756837 * 2
def baseEnd_6756837 : Nat := 3469505085083485577863379

theorem tailTrace_6756837 : CollatzResearch.WordTrace tailWord_6756837 prefixEnd_6756837 3469505085083485577863379 := by
  unfold tailWord_6756837
  simp only [CollatzResearch.WordTrace]
  refine ⟨246442091422140999731996765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164294727614760666487997843 246442091422140999731996765)
  ·
    refine ⟨92415784283302874899498787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246442091422140999731996765 92415784283302874899498787)
    ·
      refine ⟨138623676424954312349248181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92415784283302874899498787 138623676424954312349248181)
      ·
        refine ⟨12995969664839466782742017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138623676424954312349248181 12995969664839466782742017)
        ·
          refine ⟨9746977248629600087056513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12995969664839466782742017 9746977248629600087056513)
          ·
            refine ⟨7310232936472200065292385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9746977248629600087056513 7310232936472200065292385)
            ·
              refine ⟨5482674702354150048969289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7310232936472200065292385 5482674702354150048969289)
              ·
                refine ⟨4112006026765612536726967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5482674702354150048969289 4112006026765612536726967)
                ·
                  refine ⟨6168009040148418805090451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4112006026765612536726967 6168009040148418805090451)
                  ·
                    refine ⟨9252013560222628207635677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6168009040148418805090451 9252013560222628207635677)
                    ·
                      refine ⟨3469505085083485577863379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9252013560222628207635677 3469505085083485577863379)
                      ·
                        rfl

theorem cell23_6756837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_6756837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756837 prefixEnd_6756837 := by exact prefixLift 6756837
  have htrace : WordTrace (prefixWord ++ tailWord_6756837) baseStart_6756837 baseEnd_6756837 := by
    simpa [prefixWord, tailWord_6756837, baseEnd_6756837] using wordTrace_append hprefix tailTrace_6756837
  have hstable : (prefixWord ++ tailWord_6756837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756837).length < 2 ^ (prefixWord ++ tailWord_6756837).sum := by decide
  have hdescent : baseEnd_6756837 < baseStart_6756837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756843 : List Nat := [1, 1, 1, 1, 2, 3, 5, 4, 1, 2, 2]
def baseStart_6756843 : Nat := 118140960795 + 6756843 * 2 ^ 59
def prefixEnd_6756843 : Nat := 4983230072969 + 3 ^ 40 * 6756843 * 2
def baseEnd_6756843 : Nat := 3469508165967412554388351

theorem tailTrace_6756843 : CollatzResearch.WordTrace tailWord_6756843 prefixEnd_6756843 3469508165967412554388351 := by
  unfold tailWord_6756843
  simp only [CollatzResearch.WordTrace]
  refine ⟨246442310260119262756715183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164294873506746175171143455 246442310260119262756715183)
  ·
    refine ⟨369663465390178894135072775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246442310260119262756715183 369663465390178894135072775)
    ·
      refine ⟨554495198085268341202609163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369663465390178894135072775 554495198085268341202609163)
      ·
        refine ⟨831742797127902511803913745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554495198085268341202609163 831742797127902511803913745)
        ·
          refine ⟨623807097845926883852935309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831742797127902511803913745 623807097845926883852935309)
          ·
            refine ⟨233927661692222581444850741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 623807097845926883852935309 233927661692222581444850741)
            ·
              refine ⟨21930718283645867010454757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 233927661692222581444850741 21930718283645867010454757)
              ·
                refine ⟨4112009678183600064460267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21930718283645867010454757 4112009678183600064460267)
                ·
                  refine ⟨6168014517275400096690401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4112009678183600064460267 6168014517275400096690401)
                  ·
                    refine ⟨4626010887956550072517801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6168014517275400096690401 4626010887956550072517801)
                    ·
                      refine ⟨3469508165967412554388351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626010887956550072517801 3469508165967412554388351)
                      ·
                        rfl

theorem cell23_6756843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 1, 2, 2].length) (baseStart_6756843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756843 prefixEnd_6756843 := by exact prefixLift 6756843
  have htrace : WordTrace (prefixWord ++ tailWord_6756843) baseStart_6756843 baseEnd_6756843 := by
    simpa [prefixWord, tailWord_6756843, baseEnd_6756843] using wordTrace_append hprefix tailTrace_6756843
  have hstable : (prefixWord ++ tailWord_6756843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756843).length < 2 ^ (prefixWord ++ tailWord_6756843).sum := by decide
  have hdescent : baseEnd_6756843 < baseStart_6756843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756872 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_6756872 : Nat := 118140960795 + 6756872 * 2 ^ 59
def prefixEnd_6756872 : Nat := 4983230072969 + 3 ^ 40 * 6756872 * 2
def baseEnd_6756872 : Nat := 3469523056906392940925717

theorem tailTrace_6756872 : CollatzResearch.WordTrace tailWord_6756872 prefixEnd_6756872 3469523056906392940925717 := by
  unfold tailWord_6756872
  simp only [CollatzResearch.WordTrace]
  refine ⟨123221683988507100354760435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164295578651342800473013913 123221683988507100354760435)
  ·
    refine ⟨184832525982760650532140653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123221683988507100354760435 184832525982760650532140653)
    ·
      refine ⟨69312197243535243949552745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184832525982760650532140653 69312197243535243949552745)
      ·
        refine ⟨51984147932651432962164559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69312197243535243949552745 51984147932651432962164559)
        ·
          refine ⟨77976221898977149443246839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51984147932651432962164559 77976221898977149443246839)
          ·
            refine ⟨116964332848465724164870259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77976221898977149443246839 116964332848465724164870259)
            ·
              refine ⟨175446499272698586247305389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116964332848465724164870259 175446499272698586247305389)
              ·
                refine ⟨65792437227261969842739521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175446499272698586247305389 65792437227261969842739521)
                ·
                  refine ⟨49344327920446477382054641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65792437227261969842739521 49344327920446477382054641)
                  ·
                    refine ⟨37008245940334858036540981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49344327920446477382054641 37008245940334858036540981)
                    ·
                      refine ⟨3469523056906392940925717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37008245940334858036540981 3469523056906392940925717)
                      ·
                        rfl

theorem cell23_6756872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_6756872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756872 prefixEnd_6756872 := by exact prefixLift 6756872
  have htrace : WordTrace (prefixWord ++ tailWord_6756872) baseStart_6756872 baseEnd_6756872 := by
    simpa [prefixWord, tailWord_6756872, baseEnd_6756872] using wordTrace_append hprefix tailTrace_6756872
  have hstable : (prefixWord ++ tailWord_6756872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756872).length < 2 ^ (prefixWord ++ tailWord_6756872).sum := by decide
  have hdescent : baseEnd_6756872 < baseStart_6756872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756877 : List Nat := [1, 7, 1, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_6756877 : Nat := 118140960795 + 6756877 * 2 ^ 59
def prefixEnd_6756877 : Nat := 4983230072969 + 3 ^ 40 * 6756877 * 2
def baseEnd_6756877 : Nat := 3469525624309665421363195

theorem tailTrace_6756877 : CollatzResearch.WordTrace tailWord_6756877 prefixEnd_6756877 3469525624309665421363195 := by
  unfold tailWord_6756877
  simp only [CollatzResearch.WordTrace]
  refine ⟨246443550341996086563452885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164295700227997391042301923 246443550341996086563452885)
  ·
    refine ⟨5776020711140533278830927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 246443550341996086563452885 5776020711140533278830927)
    ·
      refine ⟨8664031066710799918246391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5776020711140533278830927 8664031066710799918246391)
      ·
        refine ⟨12996046600066199877369587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8664031066710799918246391 12996046600066199877369587)
        ·
          refine ⟨19494069900099299816054381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12996046600066199877369587 19494069900099299816054381)
          ·
            refine ⟨7310276212537237431020393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19494069900099299816054381 7310276212537237431020393)
            ·
              refine ⟨5482707159402928073265295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7310276212537237431020393 5482707159402928073265295)
              ·
                refine ⟨8224060739104392109897943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5482707159402928073265295 8224060739104392109897943)
                ·
                  refine ⟨12336091108656588164846915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8224060739104392109897943 12336091108656588164846915)
                  ·
                    refine ⟨18504136662984882247270373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12336091108656588164846915 18504136662984882247270373)
                    ·
                      refine ⟨3469525624309665421363195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18504136662984882247270373 3469525624309665421363195)
                      ·
                        rfl

theorem cell23_6756877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_6756877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756877 prefixEnd_6756877 := by exact prefixLift 6756877
  have htrace : WordTrace (prefixWord ++ tailWord_6756877) baseStart_6756877 baseEnd_6756877 := by
    simpa [prefixWord, tailWord_6756877, baseEnd_6756877] using wordTrace_append hprefix tailTrace_6756877
  have hstable : (prefixWord ++ tailWord_6756877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756877).length < 2 ^ (prefixWord ++ tailWord_6756877).sum := by decide
  have hdescent : baseEnd_6756877 < baseStart_6756877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756893 : List Nat := [1, 4, 2, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_6756893 : Nat := 118140960795 + 6756893 * 2 ^ 59
def prefixEnd_6756893 : Nat := 4983230072969 + 3 ^ 40 * 6756893 * 2
def baseEnd_6756893 : Nat := 3469533840000137358763121

theorem tailTrace_6756893 : CollatzResearch.WordTrace tailWord_6756893 prefixEnd_6756893 3469533840000137358763121 := by
  unfold tailWord_6756893
  simp only [CollatzResearch.WordTrace]
  refine ⟨246444133909938121296035333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164296089273292080864023555 246444133909938121296035333)
  ·
    refine ⟨46208275108113397743006625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246444133909938121296035333 46208275108113397743006625)
    ·
      refine ⟨34656206331085048307254969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46208275108113397743006625 34656206331085048307254969)
      ·
        refine ⟨25992154748313786230441227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34656206331085048307254969 25992154748313786230441227)
        ·
          refine ⟨38988232122470679345661841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25992154748313786230441227 38988232122470679345661841)
          ·
            refine ⟨29241174091853009509246381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38988232122470679345661841 29241174091853009509246381)
            ·
              refine ⟨10965440284444878565967393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29241174091853009509246381 10965440284444878565967393)
              ·
                refine ⟨8224080213333658924475545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10965440284444878565967393 8224080213333658924475545)
                ·
                  refine ⟨6168060160000244193356659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8224080213333658924475545 6168060160000244193356659)
                  ·
                    refine ⟨9252090240000366290034989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6168060160000244193356659 9252090240000366290034989)
                    ·
                      refine ⟨3469533840000137358763121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9252090240000366290034989 3469533840000137358763121)
                      ·
                        rfl

theorem cell23_6756893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_6756893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756893 prefixEnd_6756893 := by exact prefixLift 6756893
  have htrace : WordTrace (prefixWord ++ tailWord_6756893) baseStart_6756893 baseEnd_6756893 := by
    simpa [prefixWord, tailWord_6756893, baseEnd_6756893] using wordTrace_append hprefix tailTrace_6756893
  have hstable : (prefixWord ++ tailWord_6756893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756893).length < 2 ^ (prefixWord ++ tailWord_6756893).sum := by decide
  have hdescent : baseEnd_6756893 < baseStart_6756893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756910 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_6756910 : Nat := 118140960795 + 6756910 * 2 ^ 59
def prefixEnd_6756910 : Nat := 4983230072969 + 3 ^ 40 * 6756910 * 2
def baseEnd_6756910 : Nat := 3469542569171263792250543

theorem tailTrace_6756910 : CollatzResearch.WordTrace tailWord_6756910 prefixEnd_6756910 3469542569171263792250543 := by
  unfold tailWord_6756910
  simp only [CollatzResearch.WordTrace]
  refine ⟨30805594243859566649925523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164296502633917688799602789 30805594243859566649925523)
  ·
    refine ⟨46208391365789349974888285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30805594243859566649925523 46208391365789349974888285)
    ·
      refine ⟨17328146762171006240583107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46208391365789349974888285 17328146762171006240583107)
      ·
        refine ⟨25992220143256509360874661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17328146762171006240583107 25992220143256509360874661)
        ·
          refine ⟨4873541276860595505163999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25992220143256509360874661 4873541276860595505163999)
          ·
            refine ⟨7310311915290893257745999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4873541276860595505163999 7310311915290893257745999)
            ·
              refine ⟨10965467872936339886618999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7310311915290893257745999 10965467872936339886618999)
              ·
                refine ⟨16448201809404509829928499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10965467872936339886618999 16448201809404509829928499)
                ·
                  refine ⟨24672302714106764744892749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16448201809404509829928499 24672302714106764744892749)
                  ·
                    refine ⟨9252113517790036779334781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24672302714106764744892749 9252113517790036779334781)
                    ·
                      refine ⟨3469542569171263792250543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9252113517790036779334781 3469542569171263792250543)
                      ·
                        rfl

theorem cell23_6756910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_6756910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756910 prefixEnd_6756910 := by exact prefixLift 6756910
  have htrace : WordTrace (prefixWord ++ tailWord_6756910) baseStart_6756910 baseEnd_6756910 := by
    simpa [prefixWord, tailWord_6756910, baseEnd_6756910] using wordTrace_append hprefix tailTrace_6756910
  have hstable : (prefixWord ++ tailWord_6756910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756910).length < 2 ^ (prefixWord ++ tailWord_6756910).sum := by decide
  have hdescent : baseEnd_6756910 < baseStart_6756910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6756949 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_6756949 : Nat := 118140960795 + 6756949 * 2 ^ 59
def prefixEnd_6756949 : Nat := 4983230072969 + 3 ^ 40 * 6756949 * 2
def baseEnd_6756949 : Nat := 3469562594916789139662863

theorem tailTrace_6756949 : CollatzResearch.WordTrace tailWord_6756949 prefixEnd_6756949 3469562594916789139662863 := by
  unfold tailWord_6756949
  simp only [CollatzResearch.WordTrace]
  refine ⟨246446176397735242860073901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164297450931823495240049267 246446176397735242860073901)
  ·
    refine ⟨92417316149150716072527713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246446176397735242860073901 92417316149150716072527713)
    ·
      refine ⟨69312987111863037054395785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92417316149150716072527713 69312987111863037054395785)
      ·
        refine ⟨51984740333897277790796839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69312987111863037054395785 51984740333897277790796839)
        ·
          refine ⟨77977110500845916686195259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51984740333897277790796839 77977110500845916686195259)
          ·
            refine ⟨116965665751268875029292889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77977110500845916686195259 116965665751268875029292889)
            ·
              refine ⟨87724249313451656271969667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116965665751268875029292889 87724249313451656271969667)
              ·
                refine ⟨131586373970177484407954501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87724249313451656271969667 131586373970177484407954501)
                ·
                  refine ⟨24672445119408278326491469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131586373970177484407954501 24672445119408278326491469)
                  ·
                    refine ⟨9252166919778104372434301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24672445119408278326491469 9252166919778104372434301)
                    ·
                      refine ⟨3469562594916789139662863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9252166919778104372434301 3469562594916789139662863)
                      ·
                        rfl

theorem cell23_6756949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_6756949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6756949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6756949 prefixEnd_6756949 := by exact prefixLift 6756949
  have htrace : WordTrace (prefixWord ++ tailWord_6756949) baseStart_6756949 baseEnd_6756949 := by
    simpa [prefixWord, tailWord_6756949, baseEnd_6756949] using wordTrace_append hprefix tailTrace_6756949
  have hstable : (prefixWord ++ tailWord_6756949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6756949).length < 2 ^ (prefixWord ++ tailWord_6756949).sum := by decide
  have hdescent : baseEnd_6756949 < baseStart_6756949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6756949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757006 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_6757006 : Nat := 118140960795 + 6757006 * 2 ^ 59
def prefixEnd_6757006 : Nat := 4983230072969 + 3 ^ 40 * 6757006 * 2
def baseEnd_6757006 : Nat := 3469591863314095416650101

theorem tailTrace_6757006 : CollatzResearch.WordTrace tailWord_6757006 prefixEnd_6757006 3469591863314095416650101 := by
  unfold tailWord_6757006
  simp only [CollatzResearch.WordTrace]
  refine ⟨30806031919816092699362359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164298836905685827729932581 30806031919816092699362359)
  ·
    refine ⟨46209047879724139049043539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30806031919816092699362359 46209047879724139049043539)
    ·
      refine ⟨69313571819586208573565309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46209047879724139049043539 69313571819586208573565309)
      ·
        refine ⟨25992589432344828215086991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69313571819586208573565309 25992589432344828215086991)
        ·
          refine ⟨38988884148517242322630487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25992589432344828215086991 38988884148517242322630487)
          ·
            refine ⟨58483326222775863483945731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38988884148517242322630487 58483326222775863483945731)
            ·
              refine ⟨87724989334163795225918597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58483326222775863483945731 87724989334163795225918597)
              ·
                refine ⟨16448435500155711604859737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87724989334163795225918597 16448435500155711604859737)
                ·
                  refine ⟨12336326625116783703644803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16448435500155711604859737 12336326625116783703644803)
                  ·
                    refine ⟨18504489937675175555467205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12336326625116783703644803 18504489937675175555467205)
                    ·
                      refine ⟨3469591863314095416650101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18504489937675175555467205 3469591863314095416650101)
                      ·
                        rfl

theorem cell23_6757006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_6757006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757006 prefixEnd_6757006 := by exact prefixLift 6757006
  have htrace : WordTrace (prefixWord ++ tailWord_6757006) baseStart_6757006 baseEnd_6757006 := by
    simpa [prefixWord, tailWord_6757006, baseEnd_6757006] using wordTrace_append hprefix tailTrace_6757006
  have hstable : (prefixWord ++ tailWord_6757006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757006).length < 2 ^ (prefixWord ++ tailWord_6757006).sum := by decide
  have hdescent : baseEnd_6757006 < baseStart_6757006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757016 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 3, 4]
def baseStart_6757016 : Nat := 118140960795 + 6757016 * 2 ^ 59
def prefixEnd_6757016 : Nat := 4983230072969 + 3 ^ 40 * 6757016 * 2
def baseEnd_6757016 : Nat := 1156532332706880125841685

theorem tailTrace_6757016 : CollatzResearch.WordTrace tailWord_6757016 prefixEnd_6757016 1156532332706880125841685 := by
  unfold tailWord_6757016
  simp only [CollatzResearch.WordTrace]
  refine ⟨123224310044246256651381451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164299080058995008868508601 123224310044246256651381451)
  ·
    refine ⟨184836465066369384977072177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123224310044246256651381451 184836465066369384977072177)
    ·
      refine ⟨138627348799777038732804133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184836465066369384977072177 138627348799777038732804133)
      ·
        refine ⟨25992627899958194762400775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138627348799777038732804133 25992627899958194762400775)
        ·
          refine ⟨38988941849937292143601163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25992627899958194762400775 38988941849937292143601163)
          ·
            refine ⟨58483412774905938215401745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38988941849937292143601163 58483412774905938215401745)
            ·
              refine ⟨43862559581179453661551309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58483412774905938215401745 43862559581179453661551309)
              ·
                refine ⟨16448459842942295123081741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43862559581179453661551309 16448459842942295123081741)
                ·
                  refine ⟨6168172441103360671155653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16448459842942295123081741 6168172441103360671155653)
                  ·
                    refine ⟨1156532332706880125841685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6168172441103360671155653 1156532332706880125841685)
                    ·
                      rfl

theorem cell23_6757016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_6757016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757016 prefixEnd_6757016 := by exact prefixLift 6757016
  have htrace : WordTrace (prefixWord ++ tailWord_6757016) baseStart_6757016 baseEnd_6757016 := by
    simpa [prefixWord, tailWord_6757016, baseEnd_6757016] using wordTrace_append hprefix tailTrace_6757016
  have hstable : (prefixWord ++ tailWord_6757016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757016).length < 2 ^ (prefixWord ++ tailWord_6757016).sum := by decide
  have hdescent : baseEnd_6757016 < baseStart_6757016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757043 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 2, 2, 3]
def baseStart_6757043 : Nat := 118140960795 + 6757043 * 2 ^ 59
def prefixEnd_6757043 : Nat := 4983230072969 + 3 ^ 40 * 6757043 * 2
def baseEnd_6757043 : Nat := 3469610862098311771887431

theorem tailTrace_6757043 : CollatzResearch.WordTrace tailWord_6757043 prefixEnd_6757043 3469610862098311771887431 := by
  unfold tailWord_6757043
  simp only [CollatzResearch.WordTrace]
  refine ⟨246449604859394696913995783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164299736572929797942663855 246449604859394696913995783)
  ·
    refine ⟨369674407289092045370993675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246449604859394696913995783 369674407289092045370993675)
    ·
      refine ⟨554511610933638068056490513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369674407289092045370993675 554511610933638068056490513)
      ·
        refine ⟨415883708200228551042367885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554511610933638068056490513 415883708200228551042367885)
        ·
          refine ⟨155956390575085706640887957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415883708200228551042367885 155956390575085706640887957)
          ·
            refine ⟨7310455808207142498791623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155956390575085706640887957 7310455808207142498791623)
            ·
              refine ⟨10965683712310713748187435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7310455808207142498791623 10965683712310713748187435)
              ·
                refine ⟨16448525568466070622281153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10965683712310713748187435 16448525568466070622281153)
                ·
                  refine ⟨12336394176349552966710865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16448525568466070622281153 12336394176349552966710865)
                  ·
                    refine ⟨9252295632262164725033149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12336394176349552966710865 9252295632262164725033149)
                    ·
                      refine ⟨3469610862098311771887431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9252295632262164725033149 3469610862098311771887431)
                      ·
                        rfl

theorem cell23_6757043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 2, 3].length) (baseStart_6757043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757043 prefixEnd_6757043 := by exact prefixLift 6757043
  have htrace : WordTrace (prefixWord ++ tailWord_6757043) baseStart_6757043 baseEnd_6757043 := by
    simpa [prefixWord, tailWord_6757043, baseEnd_6757043] using wordTrace_append hprefix tailTrace_6757043
  have hstable : (prefixWord ++ tailWord_6757043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757043).length < 2 ^ (prefixWord ++ tailWord_6757043).sum := by decide
  have hdescent : baseEnd_6757043 < baseStart_6757043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757073 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 3, 1, 3]
def baseStart_6757073 : Nat := 118140960795 + 6757073 * 2 ^ 59
def prefixEnd_6757073 : Nat := 4983230072969 + 3 ^ 40 * 6757073 * 2
def baseEnd_6757073 : Nat := 3469626266517946654512293

theorem tailTrace_6757073 : CollatzResearch.WordTrace tailWord_6757073 prefixEnd_6757073 3469626266517946654512293 := by
  unfold tailWord_6757073
  simp only [CollatzResearch.WordTrace]
  refine ⟨246450699049286012037587873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164300466032857341358391915 246450699049286012037587873)
  ·
    refine ⟨184838024286964509028190905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246450699049286012037587873 184838024286964509028190905)
    ·
      refine ⟨138628518215223381771143179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184838024286964509028190905 138628518215223381771143179)
      ·
        refine ⟨207942777322835072656714769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138628518215223381771143179 207942777322835072656714769)
        ·
          refine ⟨155957082992126304492536077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207942777322835072656714769 155957082992126304492536077)
          ·
            refine ⟨58483906122047364184701029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155957082992126304492536077 58483906122047364184701029)
            ·
              refine ⟨10965732397883880784631443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58483906122047364184701029 10965732397883880784631443)
              ·
                refine ⟨16448598596825821176947165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10965732397883880784631443 16448598596825821176947165)
                ·
                  refine ⟨6168224473809682941355187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16448598596825821176947165 6168224473809682941355187)
                  ·
                    refine ⟨9252336710714524412032781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6168224473809682941355187 9252336710714524412032781)
                    ·
                      refine ⟨3469626266517946654512293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9252336710714524412032781 3469626266517946654512293)
                      ·
                        rfl

theorem cell23_6757073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_6757073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757073 prefixEnd_6757073 := by exact prefixLift 6757073
  have htrace : WordTrace (prefixWord ++ tailWord_6757073) baseStart_6757073 baseEnd_6757073 := by
    simpa [prefixWord, tailWord_6757073, baseEnd_6757073] using wordTrace_append hprefix tailTrace_6757073
  have hstable : (prefixWord ++ tailWord_6757073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757073).length < 2 ^ (prefixWord ++ tailWord_6757073).sum := by decide
  have hdescent : baseEnd_6757073 < baseStart_6757073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757093 : List Nat := [1, 3, 1, 4, 1, 3, 2, 2, 1, 5]
def baseStart_6757093 : Nat := 118140960795 + 6757093 * 2 ^ 59
def prefixEnd_6757093 : Nat := 4983230072969 + 3 ^ 40 * 6757093 * 2
def baseEnd_6757093 : Nat := 1156545512043678858754067

theorem tailTrace_6757093 : CollatzResearch.WordTrace tailWord_6757093 prefixEnd_6757093 1156545512043678858754067 := by
  unfold tailWord_6757093
  simp only [CollatzResearch.WordTrace]
  refine ⟨246451428509213555453315933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164300952339475703635543955 246451428509213555453315933)
  ·
    refine ⟨92419285690955083294993475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246451428509213555453315933 92419285690955083294993475)
    ·
      refine ⟨138628928536432624942490213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92419285690955083294993475 138628928536432624942490213)
      ·
        refine ⟨25992924100581117176716915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138628928536432624942490213 25992924100581117176716915)
        ·
          refine ⟨38989386150871675765075373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25992924100581117176716915 38989386150871675765075373)
          ·
            refine ⟨14621019806576878411903265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38989386150871675765075373 14621019806576878411903265)
            ·
              refine ⟨10965764854932658808927449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14621019806576878411903265 10965764854932658808927449)
              ·
                refine ⟨8224323641199494106695587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10965764854932658808927449 8224323641199494106695587)
                ·
                  refine ⟨12336485461799241160043381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8224323641199494106695587 12336485461799241160043381)
                  ·
                    refine ⟨1156545512043678858754067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12336485461799241160043381 1156545512043678858754067)
                    ·
                      rfl

theorem cell23_6757093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_6757093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757093 prefixEnd_6757093 := by exact prefixLift 6757093
  have htrace : WordTrace (prefixWord ++ tailWord_6757093) baseStart_6757093 baseEnd_6757093 := by
    simpa [prefixWord, tailWord_6757093, baseEnd_6757093] using wordTrace_append hprefix tailTrace_6757093
  have hstable : (prefixWord ++ tailWord_6757093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757093).length < 2 ^ (prefixWord ++ tailWord_6757093).sum := by decide
  have hdescent : baseEnd_6757093 < baseStart_6757093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757099 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 5]
def baseStart_6757099 : Nat := 118140960795 + 6757099 * 2 ^ 59
def prefixEnd_6757099 : Nat := 4983230072969 + 3 ^ 40 * 6757099 * 2
def baseEnd_6757099 : Nat := 3469639617014963552787173

theorem tailTrace_6757099 : CollatzResearch.WordTrace tailWord_6757099 prefixEnd_6757099 3469639617014963552787173 := by
  unfold tailWord_6757099
  simp only [CollatzResearch.WordTrace]
  refine ⟨246451647347191818478034351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164301098231461212318689567 246451647347191818478034351)
  ·
    refine ⟨369677471020787727717051527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246451647347191818478034351 369677471020787727717051527)
    ·
      refine ⟨554516206531181591575577291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369677471020787727717051527 554516206531181591575577291)
      ·
        refine ⟨831774309796772387363365937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554516206531181591575577291 831774309796772387363365937)
        ·
          refine ⟨623830732347579290522524453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831774309796772387363365937 623830732347579290522524453)
          ·
            refine ⟨116968262315171116972973335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 623830732347579290522524453 116968262315171116972973335)
            ·
              refine ⟨175452393472756675459460003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116968262315171116972973335 175452393472756675459460003)
              ·
                refine ⟨263178590209135013189190005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175452393472756675459460003 263178590209135013189190005)
                ·
                  refine ⟨24672992832106407486486563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 263178590209135013189190005 24672992832106407486486563)
                  ·
                    refine ⟨37009489248159611229729845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24672992832106407486486563 37009489248159611229729845)
                    ·
                      refine ⟨3469639617014963552787173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37009489248159611229729845 3469639617014963552787173)
                      ·
                        rfl

theorem cell23_6757099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 5].length) (baseStart_6757099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757099 prefixEnd_6757099 := by exact prefixLift 6757099
  have htrace : WordTrace (prefixWord ++ tailWord_6757099) baseStart_6757099 baseEnd_6757099 := by
    simpa [prefixWord, tailWord_6757099, baseEnd_6757099] using wordTrace_append hprefix tailTrace_6757099
  have hstable : (prefixWord ++ tailWord_6757099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757099).length < 2 ^ (prefixWord ++ tailWord_6757099).sum := by decide
  have hdescent : baseEnd_6757099 < baseStart_6757099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757113 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 5, 2, 2]
def baseStart_6757113 : Nat := 118140960795 + 6757113 * 2 ^ 59
def prefixEnd_6757113 : Nat := 4983230072969 + 3 ^ 40 * 6757113 * 2
def baseEnd_6757113 : Nat := 3469646805744126498012109

theorem tailTrace_6757113 : CollatzResearch.WordTrace tailWord_6757113 prefixEnd_6757113 3469646805744126498012109 := by
  unfold tailWord_6757113
  simp only [CollatzResearch.WordTrace]
  refine ⟨246452157969141098869043993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164301438646094065912695995 246452157969141098869043993)
  ·
    refine ⟨184839118476855824151782995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246452157969141098869043993 184839118476855824151782995)
    ·
      refine ⟨277258677715283736227674493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184839118476855824151782995 277258677715283736227674493)
      ·
        refine ⟨103972004143231401085377935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277258677715283736227674493 103972004143231401085377935)
        ·
          refine ⟨155958006214847101628066903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103972004143231401085377935 155958006214847101628066903)
          ·
            refine ⟨233937009322270652442100355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155958006214847101628066903 233937009322270652442100355)
            ·
              refine ⟨350905513983405978663150533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233937009322270652442100355 350905513983405978663150533)
              ·
                refine ⟨65794783871888620999340725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350905513983405978663150533 65794783871888620999340725)
                ·
                  refine ⟨6168260987989558218688193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65794783871888620999340725 6168260987989558218688193)
                  ·
                    refine ⟨4626195740992168664016145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6168260987989558218688193 4626195740992168664016145)
                    ·
                      refine ⟨3469646805744126498012109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626195740992168664016145 3469646805744126498012109)
                      ·
                        rfl

theorem cell23_6757113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_6757113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757113 prefixEnd_6757113 := by exact prefixLift 6757113
  have htrace : WordTrace (prefixWord ++ tailWord_6757113) baseStart_6757113 baseEnd_6757113 := by
    simpa [prefixWord, tailWord_6757113, baseEnd_6757113] using wordTrace_append hprefix tailTrace_6757113
  have hstable : (prefixWord ++ tailWord_6757113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757113).length < 2 ^ (prefixWord ++ tailWord_6757113).sum := by decide
  have hdescent : baseEnd_6757113 < baseStart_6757113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757116 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_6757116 : Nat := 118140960795 + 6757116 * 2 ^ 59
def prefixEnd_6757116 : Nat := 4983230072969 + 3 ^ 40 * 6757116 * 2
def baseEnd_6757116 : Nat := 3469648346186089986274595

theorem tailTrace_6757116 : CollatzResearch.WordTrace tailWord_6757116 prefixEnd_6757116 3469648346186089986274595 := by
  unfold tailWord_6757116
  simp only [CollatzResearch.WordTrace]
  refine ⟨123226133694065115190701601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164301511592086820254268801 123226133694065115190701601)
  ·
    refine ⟨92419600270548836393026201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123226133694065115190701601 92419600270548836393026201)
    ·
      refine ⟨69314700202911627294769651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92419600270548836393026201 69314700202911627294769651)
      ·
        refine ⟨103972050304367440942154477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69314700202911627294769651 103972050304367440942154477)
        ·
          refine ⟨38989518864137790353307929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103972050304367440942154477 38989518864137790353307929)
          ·
            refine ⟨29242139148103342764980947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38989518864137790353307929 29242139148103342764980947)
            ·
              refine ⟨43863208722155014147471421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29242139148103342764980947 43863208722155014147471421)
              ·
                refine ⟨16448703270808130305301783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43863208722155014147471421 16448703270808130305301783)
                ·
                  refine ⟨24673054906212195457952675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16448703270808130305301783 24673054906212195457952675)
                  ·
                    refine ⟨37009582359318293186929013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24673054906212195457952675 37009582359318293186929013)
                    ·
                      refine ⟨3469648346186089986274595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37009582359318293186929013 3469648346186089986274595)
                      ·
                        rfl

theorem cell23_6757116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_6757116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757116 prefixEnd_6757116 := by exact prefixLift 6757116
  have htrace : WordTrace (prefixWord ++ tailWord_6757116) baseStart_6757116 baseEnd_6757116 := by
    simpa [prefixWord, tailWord_6757116, baseEnd_6757116] using wordTrace_append hprefix tailTrace_6757116
  have hstable : (prefixWord ++ tailWord_6757116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757116).length < 2 ^ (prefixWord ++ tailWord_6757116).sum := by decide
  have hdescent : baseEnd_6757116 < baseStart_6757116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757139 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 6]
def baseStart_6757139 : Nat := 118140960795 + 6757139 * 2 ^ 59
def prefixEnd_6757139 : Nat := 4983230072969 + 3 ^ 40 * 6757139 * 2
def baseEnd_6757139 : Nat := 3469660156241143396286989

theorem tailTrace_6757139 : CollatzResearch.WordTrace tailWord_6757139 prefixEnd_6757139 3469660156241143396286989 := by
  unfold tailWord_6757139
  simp only [CollatzResearch.WordTrace]
  refine ⟨246453106267046905309490471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164302070844697936872993647 246453106267046905309490471)
  ·
    refine ⟨369679659400570357964235707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246453106267046905309490471 369679659400570357964235707)
    ·
      refine ⟨554519489100855536946353561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369679659400570357964235707 554519489100855536946353561)
      ·
        refine ⟨415889616825641652709765171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554519489100855536946353561 415889616825641652709765171)
        ·
          refine ⟨623834425238462479064647757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415889616825641652709765171 623834425238462479064647757)
          ·
            refine ⟨233937909464423429649242909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 623834425238462479064647757 233937909464423429649242909)
            ·
              refine ⟨87726716049158786118466091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233937909464423429649242909 87726716049158786118466091)
              ·
                refine ⟨131590074073738179177699137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87726716049158786118466091 131590074073738179177699137)
                ·
                  refine ⟨98692555555303634383274353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131590074073738179177699137 98692555555303634383274353)
                  ·
                    refine ⟨74019416666477725787455765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98692555555303634383274353 74019416666477725787455765)
                    ·
                      refine ⟨3469660156241143396286989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74019416666477725787455765 3469660156241143396286989)
                      ·
                        rfl

theorem cell23_6757139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_6757139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757139 prefixEnd_6757139 := by exact prefixLift 6757139
  have htrace : WordTrace (prefixWord ++ tailWord_6757139) baseStart_6757139 baseEnd_6757139 := by
    simpa [prefixWord, tailWord_6757139, baseEnd_6757139] using wordTrace_append hprefix tailTrace_6757139
  have hstable : (prefixWord ++ tailWord_6757139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757139).length < 2 ^ (prefixWord ++ tailWord_6757139).sum := by decide
  have hdescent : baseEnd_6757139 < baseStart_6757139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757196 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 1, 8]
def baseStart_6757196 : Nat := 118140960795 + 6757196 * 2 ^ 59
def prefixEnd_6757196 : Nat := 4983230072969 + 3 ^ 40 * 6757196 * 2
def baseEnd_6757196 : Nat := 1156563141546149891091409

theorem tailTrace_6757196 : CollatzResearch.WordTrace tailWord_6757196 prefixEnd_6757196 1156563141546149891091409 := by
  unfold tailWord_6757196
  simp only [CollatzResearch.WordTrace]
  refine ⟨123227592613920202022157721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164303456818560269362876961 123227592613920202022157721)
  ·
    refine ⟨92420694460440151516618291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123227592613920202022157721 92420694460440151516618291)
    ·
      refine ⟨138631041690660227274927437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92420694460440151516618291 138631041690660227274927437)
      ·
        refine ⟨51986640633997585228097789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138631041690660227274927437 51986640633997585228097789)
        ·
          refine ⟨19494990237749094460536671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51986640633997585228097789 19494990237749094460536671)
          ·
            refine ⟨29242485356623641690805007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19494990237749094460536671 29242485356623641690805007)
            ·
              refine ⟨43863728034935462536207511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29242485356623641690805007 43863728034935462536207511)
              ·
                refine ⟨65795592052403193804311267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43863728034935462536207511 65795592052403193804311267)
                ·
                  refine ⟨98693388078604790706466901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65795592052403193804311267 98693388078604790706466901)
                  ·
                    refine ⟨1156563141546149891091409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98693388078604790706466901 1156563141546149891091409)
                    ·
                      rfl

theorem cell23_6757196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_6757196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757196 prefixEnd_6757196 := by exact prefixLift 6757196
  have htrace : WordTrace (prefixWord ++ tailWord_6757196) baseStart_6757196 baseEnd_6757196 := by
    simpa [prefixWord, tailWord_6757196, baseEnd_6757196] using wordTrace_append hprefix tailTrace_6757196
  have hstable : (prefixWord ++ tailWord_6757196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757196).length < 2 ^ (prefixWord ++ tailWord_6757196).sum := by decide
  have hdescent : baseEnd_6757196 < baseStart_6757196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757197 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_6757197 : Nat := 118140960795 + 6757197 * 2 ^ 59
def prefixEnd_6757197 : Nat := 4983230072969 + 3 ^ 40 * 6757197 * 2
def baseEnd_6757197 : Nat := 3469689938119104169361723

theorem tailTrace_6757197 : CollatzResearch.WordTrace tailWord_6757197 prefixEnd_6757197 3469689938119104169361723 := by
  unfold tailWord_6757197
  simp only [CollatzResearch.WordTrace]
  refine ⟨246455221700836781215101845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164303481133891187476734563 246455221700836781215101845)
  ·
    refine ⟨11552588517226724119457899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 246455221700836781215101845 11552588517226724119457899)
    ·
      refine ⟨17328882775840086179186849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11552588517226724119457899 17328882775840086179186849)
      ·
        refine ⟨12996662081880064634390137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17328882775840086179186849 12996662081880064634390137)
        ·
          refine ⟨9747496561410048475792603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12996662081880064634390137 9747496561410048475792603)
          ·
            refine ⟨14621244842115072713688905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9747496561410048475792603 14621244842115072713688905)
            ·
              refine ⟨10965933631586304535266679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14621244842115072713688905 10965933631586304535266679)
              ·
                refine ⟨16448900447379456802900019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10965933631586304535266679 16448900447379456802900019)
                ·
                  refine ⟨24673350671069185204350029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16448900447379456802900019 24673350671069185204350029)
                  ·
                    refine ⟨9252506501650944451631261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24673350671069185204350029 9252506501650944451631261)
                    ·
                      refine ⟨3469689938119104169361723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9252506501650944451631261 3469689938119104169361723)
                      ·
                        rfl

theorem cell23_6757197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_6757197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757197 prefixEnd_6757197 := by exact prefixLift 6757197
  have htrace : WordTrace (prefixWord ++ tailWord_6757197) baseStart_6757197 baseEnd_6757197 := by
    simpa [prefixWord, tailWord_6757197, baseEnd_6757197] using wordTrace_append hprefix tailTrace_6757197
  have hstable : (prefixWord ++ tailWord_6757197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757197).length < 2 ^ (prefixWord ++ tailWord_6757197).sum := by decide
  have hdescent : baseEnd_6757197 < baseStart_6757197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757216 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 4]
def baseStart_6757216 : Nat := 118140960795 + 6757216 * 2 ^ 59
def prefixEnd_6757216 : Nat := 4983230072969 + 3 ^ 40 * 6757216 * 2
def baseEnd_6757216 : Nat := 3469699694251539595024135

theorem tailTrace_6757216 : CollatzResearch.WordTrace tailWord_6757216 prefixEnd_6757216 3469699694251539595024135 := by
  unfold tailWord_6757216
  simp only [CollatzResearch.WordTrace]
  refine ⟨123227957343883973730021751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164303943125178631640029001 123227957343883973730021751)
  ·
    refine ⟨184841936015825960595032627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123227957343883973730021751 184841936015825960595032627)
    ·
      refine ⟨277262904023738940892548941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184841936015825960595032627 277262904023738940892548941)
      ·
        refine ⟨103973589008902102834705853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277262904023738940892548941 103973589008902102834705853)
        ·
          refine ⟨38990095878338288563014695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103973589008902102834705853 38990095878338288563014695)
          ·
            refine ⟨58485143817507432844522043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38990095878338288563014695 58485143817507432844522043)
            ·
              refine ⟨87727715726261149266783065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58485143817507432844522043 87727715726261149266783065)
              ·
                refine ⟨65795786794695861950087299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87727715726261149266783065 65795786794695861950087299)
                ·
                  refine ⟨98693680192043792925130949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65795786794695861950087299 98693680192043792925130949)
                  ·
                    refine ⟨18505065036008211173462053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98693680192043792925130949 18505065036008211173462053)
                    ·
                      refine ⟨3469699694251539595024135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18505065036008211173462053 3469699694251539595024135)
                      ·
                        rfl

theorem cell23_6757216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_6757216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757216 prefixEnd_6757216 := by exact prefixLift 6757216
  have htrace : WordTrace (prefixWord ++ tailWord_6757216) baseStart_6757216 baseEnd_6757216 := by
    simpa [prefixWord, tailWord_6757216, baseEnd_6757216] using wordTrace_append hprefix tailTrace_6757216
  have hstable : (prefixWord ++ tailWord_6757216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757216).length < 2 ^ (prefixWord ++ tailWord_6757216).sum := by decide
  have hdescent : baseEnd_6757216 < baseStart_6757216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757220 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 1, 4, 2]
def baseStart_6757220 : Nat := 118140960795 + 6757220 * 2 ^ 59
def prefixEnd_6757220 : Nat := 4983230072969 + 3 ^ 40 * 6757220 * 2
def baseEnd_6757220 : Nat := 3469701748174157579374117

theorem tailTrace_6757220 : CollatzResearch.WordTrace tailWord_6757220 prefixEnd_6757220 3469701748174157579374117 := by
  unfold tailWord_6757220
  simp only [CollatzResearch.WordTrace]
  refine ⟨123228030289876728071594557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164304040386502304095459409 123228030289876728071594557)
  ·
    refine ⟨46210511358703773026847959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123228030289876728071594557 46210511358703773026847959)
    ·
      refine ⟨69315767038055659540271939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46210511358703773026847959 69315767038055659540271939)
      ·
        refine ⟨103973650557083489310407909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69315767038055659540271939 103973650557083489310407909)
        ·
          refine ⟨19495059479453154245701483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103973650557083489310407909 19495059479453154245701483)
          ·
            refine ⟨29242589219179731368552225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19495059479453154245701483 29242589219179731368552225)
            ·
              refine ⟨21931941914384798526414169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29242589219179731368552225 21931941914384798526414169)
              ·
                refine ⟨16448956435788598894810627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21931941914384798526414169 16448956435788598894810627)
                ·
                  refine ⟨24673434653682898342215941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16448956435788598894810627 24673434653682898342215941)
                  ·
                    refine ⟨4626268997565543439165489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24673434653682898342215941 4626268997565543439165489)
                    ·
                      refine ⟨3469701748174157579374117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626268997565543439165489 3469701748174157579374117)
                      ·
                        rfl

theorem cell23_6757220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_6757220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757220 prefixEnd_6757220 := by exact prefixLift 6757220
  have htrace : WordTrace (prefixWord ++ tailWord_6757220) baseStart_6757220 baseEnd_6757220 := by
    simpa [prefixWord, tailWord_6757220, baseEnd_6757220] using wordTrace_append hprefix tailTrace_6757220
  have hstable : (prefixWord ++ tailWord_6757220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757220).length < 2 ^ (prefixWord ++ tailWord_6757220).sum := by decide
  have hdescent : baseEnd_6757220 < baseStart_6757220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757224 : List Nat := [2, 1, 4, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_6757224 : Nat := 118140960795 + 6757224 * 2 ^ 59
def prefixEnd_6757224 : Nat := 4983230072969 + 3 ^ 40 * 6757224 * 2
def baseEnd_6757224 : Nat := 3469703802096775563724099

theorem tailTrace_6757224 : CollatzResearch.WordTrace tailWord_6757224 prefixEnd_6757224 3469703802096775563724099 := by
  unfold tailWord_6757224
  simp only [CollatzResearch.WordTrace]
  refine ⟨123228103235869482413167363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164304137647825976550889817 123228103235869482413167363)
  ·
    refine ⟨184842154853804223619751045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123228103235869482413167363 184842154853804223619751045)
    ·
      refine ⟨34657904035088291928703321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184842154853804223619751045 34657904035088291928703321)
      ·
        refine ⟨25993428026316218946527491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34657904035088291928703321 25993428026316218946527491)
        ·
          refine ⟨38990142039474328419791237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25993428026316218946527491 38990142039474328419791237)
          ·
            refine ⟨7310651632401436578710857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38990142039474328419791237 7310651632401436578710857)
            ·
              refine ⟨5482988724301077434033143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7310651632401436578710857 5482988724301077434033143)
              ·
                refine ⟨8224483086451616151049715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5482988724301077434033143 8224483086451616151049715)
                ·
                  refine ⟨12336724629677424226574573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8224483086451616151049715 12336724629677424226574573)
                  ·
                    refine ⟨4626271736129034084965465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12336724629677424226574573 4626271736129034084965465)
                    ·
                      refine ⟨3469703802096775563724099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626271736129034084965465 3469703802096775563724099)
                      ·
                        rfl

theorem cell23_6757224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_6757224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757224 prefixEnd_6757224 := by exact prefixLift 6757224
  have htrace : WordTrace (prefixWord ++ tailWord_6757224) baseStart_6757224 baseEnd_6757224 := by
    simpa [prefixWord, tailWord_6757224, baseEnd_6757224] using wordTrace_append hprefix tailTrace_6757224
  have hstable : (prefixWord ++ tailWord_6757224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757224).length < 2 ^ (prefixWord ++ tailWord_6757224).sum := by decide
  have hdescent : baseEnd_6757224 < baseStart_6757224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757237 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_6757237 : Nat := 118140960795 + 6757237 * 2 ^ 59
def prefixEnd_6757237 : Nat := 4983230072969 + 3 ^ 40 * 6757237 * 2
def baseEnd_6757237 : Nat := 3469710477345284012861539

theorem tailTrace_6757237 : CollatzResearch.WordTrace tailWord_6757237 prefixEnd_6757237 3469710477345284012861539 := by
  unfold tailWord_6757237
  simp only [CollatzResearch.WordTrace]
  refine ⟨246456680620691868046557965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164304453747127912031038643 246456680620691868046557965)
  ·
    refine ⟨92421255232759450517459237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246456680620691868046557965 92421255232759450517459237)
    ·
      refine ⟨17328985356142396972023607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92421255232759450517459237 17328985356142396972023607)
      ·
        refine ⟨25993478034213595458035411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17328985356142396972023607 25993478034213595458035411)
        ·
          refine ⟨38990217051320393187053117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25993478034213595458035411 38990217051320393187053117)
          ·
            refine ⟨14621331394245147445144919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38990217051320393187053117 14621331394245147445144919)
            ·
              refine ⟨21931997091367721167717379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14621331394245147445144919 21931997091367721167717379)
              ·
                refine ⟨32897995637051581751576069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21931997091367721167717379 32897995637051581751576069)
                ·
                  refine ⟨6168374181947171578420513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32897995637051581751576069 6168374181947171578420513)
                  ·
                    refine ⟨4626280636460378683815385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6168374181947171578420513 4626280636460378683815385)
                    ·
                      refine ⟨3469710477345284012861539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626280636460378683815385 3469710477345284012861539)
                      ·
                        rfl

theorem cell23_6757237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_6757237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757237 prefixEnd_6757237 := by exact prefixLift 6757237
  have htrace : WordTrace (prefixWord ++ tailWord_6757237) baseStart_6757237 baseEnd_6757237 := by
    simpa [prefixWord, tailWord_6757237, baseEnd_6757237] using wordTrace_append hprefix tailTrace_6757237
  have hstable : (prefixWord ++ tailWord_6757237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757237).length < 2 ^ (prefixWord ++ tailWord_6757237).sum := by decide
  have hdescent : baseEnd_6757237 < baseStart_6757237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757243 : List Nat := [1, 1, 1, 1, 1, 5, 4, 4, 5]
def baseStart_6757243 : Nat := 118140960795 + 6757243 * 2 ^ 59
def prefixEnd_6757243 : Nat := 4983230072969 + 3 ^ 40 * 6757243 * 2
def baseEnd_6757243 : Nat := 385523728692134554376279

theorem tailTrace_6757243 : CollatzResearch.WordTrace tailWord_6757243 prefixEnd_6757243 385523728692134554376279 := by
  unfold tailWord_6757243
  simp only [CollatzResearch.WordTrace]
  refine ⟨246456899458670131071276383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164304599639113420714184255 246456899458670131071276383)
  ·
    refine ⟨369685349188005196606914575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246456899458670131071276383 369685349188005196606914575)
    ·
      refine ⟨554528023782007794910371863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369685349188005196606914575 554528023782007794910371863)
      ·
        refine ⟨831792035673011692365557795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554528023782007794910371863 831792035673011692365557795)
        ·
          refine ⟨1247688053509517538548336693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 831792035673011692365557795 1247688053509517538548336693)
          ·
            refine ⟨116970755016517269238906565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1247688053509517538548336693 116970755016517269238906565)
            ·
              refine ⟨21932016565596987982294981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116970755016517269238906565 21932016565596987982294981)
              ·
                refine ⟨4112253106049435246680309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21932016565596987982294981 4112253106049435246680309)
                ·
                  refine ⟨385523728692134554376279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4112253106049435246680309 385523728692134554376279)
                  ·
                    rfl

theorem cell23_6757243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 5].length) (baseStart_6757243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757243 prefixEnd_6757243 := by exact prefixLift 6757243
  have htrace : WordTrace (prefixWord ++ tailWord_6757243) baseStart_6757243 baseEnd_6757243 := by
    simpa [prefixWord, tailWord_6757243, baseEnd_6757243] using wordTrace_append hprefix tailTrace_6757243
  have hstable : (prefixWord ++ tailWord_6757243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757243).length < 2 ^ (prefixWord ++ tailWord_6757243).sum := by decide
  have hdescent : baseEnd_6757243 < baseStart_6757243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757253 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 2, 3, 3]
def baseStart_6757253 : Nat := 118140960795 + 6757253 * 2 ^ 59
def prefixEnd_6757253 : Nat := 4983230072969 + 3 ^ 40 * 6757253 * 2
def baseEnd_6757253 : Nat := 3469718693035755950261465

theorem tailTrace_6757253 : CollatzResearch.WordTrace tailWord_6757253 prefixEnd_6757253 3469718693035755950261465 := by
  unfold tailWord_6757253
  simp only [CollatzResearch.WordTrace]
  refine ⟨246457264188633902779140413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164304842792422601852760275 246457264188633902779140413)
  ·
    refine ⟨92421474070737713542177655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246457264188633902779140413 92421474070737713542177655)
    ·
      refine ⟨138632211106106570313266483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92421474070737713542177655 138632211106106570313266483)
      ·
        refine ⟨207948316659159855469899725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138632211106106570313266483 207948316659159855469899725)
        ·
          refine ⟨77980618747184945801212397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207948316659159855469899725 77980618747184945801212397)
          ·
            refine ⟨29242732030194354675454649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77980618747184945801212397 29242732030194354675454649)
            ·
              refine ⟨21932049022645766006590987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29242732030194354675454649 21932049022645766006590987)
              ·
                refine ⟨32898073533968649009886481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21932049022645766006590987 32898073533968649009886481)
                ·
                  refine ⟨24673555150476486757414861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32898073533968649009886481 24673555150476486757414861)
                  ·
                    refine ⟨9252583181428682534030573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24673555150476486757414861 9252583181428682534030573)
                    ·
                      refine ⟨3469718693035755950261465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9252583181428682534030573 3469718693035755950261465)
                      ·
                        rfl

theorem cell23_6757253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_6757253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757253 prefixEnd_6757253 := by exact prefixLift 6757253
  have htrace : WordTrace (prefixWord ++ tailWord_6757253) baseStart_6757253 baseEnd_6757253 := by
    simpa [prefixWord, tailWord_6757253, baseEnd_6757253] using wordTrace_append hprefix tailTrace_6757253
  have hstable : (prefixWord ++ tailWord_6757253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757253).length < 2 ^ (prefixWord ++ tailWord_6757253).sum := by decide
  have hdescent : baseEnd_6757253 < baseStart_6757253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757300 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_6757300 : Nat := 118140960795 + 6757300 * 2 ^ 59
def prefixEnd_6757300 : Nat := 4983230072969 + 3 ^ 40 * 6757300 * 2
def baseEnd_6757300 : Nat := 3469742826626517266373749

theorem tailTrace_6757300 : CollatzResearch.WordTrace tailWord_6757300 prefixEnd_6757300 3469742826626517266373749 := by
  unfold tailWord_6757300
  simp only [CollatzResearch.WordTrace]
  refine ⟨123229489209731814903050677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164305985612975753204067569 123229489209731814903050677)
  ·
    refine ⟨11552764613412357647161001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123229489209731814903050677 11552764613412357647161001)
    ·
      refine ⟨8664573460059268235370751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11552764613412357647161001 8664573460059268235370751)
      ·
        refine ⟨12996860190088902353056127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8664573460059268235370751 12996860190088902353056127)
        ·
          refine ⟨19495290285133353529584191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12996860190088902353056127 19495290285133353529584191)
          ·
            refine ⟨29242935427700030294376287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19495290285133353529584191 29242935427700030294376287)
            ·
              refine ⟨43864403141550045441564431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29242935427700030294376287 43864403141550045441564431)
              ·
                refine ⟨65796604712325068162346647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43864403141550045441564431 65796604712325068162346647)
                ·
                  refine ⟨98694907068487602243519971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65796604712325068162346647 98694907068487602243519971)
                  ·
                    refine ⟨148042360602731403365279957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98694907068487602243519971 148042360602731403365279957)
                    ·
                      refine ⟨3469742826626517266373749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148042360602731403365279957 3469742826626517266373749)
                      ·
                        rfl

theorem cell23_6757300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_6757300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757300 prefixEnd_6757300 := by exact prefixLift 6757300
  have htrace : WordTrace (prefixWord ++ tailWord_6757300) baseStart_6757300 baseEnd_6757300 := by
    simpa [prefixWord, tailWord_6757300, baseEnd_6757300] using wordTrace_append hprefix tailTrace_6757300
  have hstable : (prefixWord ++ tailWord_6757300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757300).length < 2 ^ (prefixWord ++ tailWord_6757300).sum := by decide
  have hdescent : baseEnd_6757300 < baseStart_6757300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757310 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_6757310 : Nat := 118140960795 + 6757310 * 2 ^ 59
def prefixEnd_6757310 : Nat := 4983230072969 + 3 ^ 40 * 6757310 * 2
def baseEnd_6757310 : Nat := 3469747961433062227248703

theorem tailTrace_6757310 : CollatzResearch.WordTrace tailWord_6757310 prefixEnd_6757310 3469747961433062227248703 := by
  unfold tailWord_6757310
  simp only [CollatzResearch.WordTrace]
  refine ⟨30807417893678425189245673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164306228766284934342643589 30807417893678425189245673)
  ·
    refine ⟨23105563420258818891934255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30807417893678425189245673 23105563420258818891934255)
    ·
      refine ⟨34658345130388228337901383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23105563420258818891934255 34658345130388228337901383)
      ·
        refine ⟨51987517695582342506852075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34658345130388228337901383 51987517695582342506852075)
        ·
          refine ⟨77981276543373513760278113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51987517695582342506852075 77981276543373513760278113)
          ·
            refine ⟨58485957407530135320208585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77981276543373513760278113 58485957407530135320208585)
            ·
              refine ⟨43864468055647601490156439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58485957407530135320208585 43864468055647601490156439)
              ·
                refine ⟨65796702083471402235234659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43864468055647601490156439 65796702083471402235234659)
                ·
                  refine ⟨98695053125207103352851989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65796702083471402235234659 98695053125207103352851989)
                  ·
                    refine ⟨4626330615244082969664937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98695053125207103352851989 4626330615244082969664937)
                    ·
                      refine ⟨3469747961433062227248703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626330615244082969664937 3469747961433062227248703)
                      ·
                        rfl

theorem cell23_6757310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_6757310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757310 prefixEnd_6757310 := by exact prefixLift 6757310
  have htrace : WordTrace (prefixWord ++ tailWord_6757310) baseStart_6757310 baseEnd_6757310 := by
    simpa [prefixWord, tailWord_6757310, baseEnd_6757310] using wordTrace_append hprefix tailTrace_6757310
  have hstable : (prefixWord ++ tailWord_6757310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757310).length < 2 ^ (prefixWord ++ tailWord_6757310).sum := by decide
  have hdescent : baseEnd_6757310 < baseStart_6757310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757354 : List Nat := [3, 1, 3, 1, 2, 2, 4, 2, 1, 4]
def baseStart_6757354 : Nat := 118140960795 + 6757354 * 2 ^ 59
def prefixEnd_6757354 : Nat := 4983230072969 + 3 ^ 40 * 6757354 * 2
def baseEnd_6757354 : Nat := 1156590184860620018366167

theorem tailTrace_6757354 : CollatzResearch.WordTrace tailWord_6757354 prefixEnd_6757354 1156590184860620018366167 := by
  unfold tailWord_6757354
  simp only [CollatzResearch.WordTrace]
  refine ⟨61615236990316999257141779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164307298640845331352378077 61615236990316999257141779)
  ·
    refine ⟨92422855485475498885712669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61615236990316999257141779 92422855485475498885712669)
    ·
      refine ⟨34658570807053312082142251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92422855485475498885712669 34658570807053312082142251)
      ·
        refine ⟨51987856210579968123213377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34658570807053312082142251 51987856210579968123213377)
        ·
          refine ⟨38990892157934976092410033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51987856210579968123213377 38990892157934976092410033)
          ·
            refine ⟨29243169118451232069307525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38990892157934976092410033 29243169118451232069307525)
            ·
              refine ⟨5483094209709606012995161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29243169118451232069307525 5483094209709606012995161)
              ·
                refine ⟨4112320657282204509746371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5483094209709606012995161 4112320657282204509746371)
                ·
                  refine ⟨6168480985923306764619557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4112320657282204509746371 6168480985923306764619557)
                  ·
                    refine ⟨1156590184860620018366167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6168480985923306764619557 1156590184860620018366167)
                    ·
                      rfl

theorem cell23_6757354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_6757354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757354 prefixEnd_6757354 := by exact prefixLift 6757354
  have htrace : WordTrace (prefixWord ++ tailWord_6757354) baseStart_6757354 baseEnd_6757354 := by
    simpa [prefixWord, tailWord_6757354, baseEnd_6757354] using wordTrace_append hprefix tailTrace_6757354
  have hstable : (prefixWord ++ tailWord_6757354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757354).length < 2 ^ (prefixWord ++ tailWord_6757354).sum := by decide
  have hdescent : baseEnd_6757354 < baseStart_6757354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757360 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 3, 1, 3]
def baseStart_6757360 : Nat := 118140960795 + 6757360 * 2 ^ 59
def prefixEnd_6757360 : Nat := 4983230072969 + 3 ^ 40 * 6757360 * 2
def baseEnd_6757360 : Nat := 3469773635465787031623473

theorem tailTrace_6757360 : CollatzResearch.WordTrace tailWord_6757360 prefixEnd_6757360 3469773635465787031623473 := by
  unfold tailWord_6757360
  simp only [CollatzResearch.WordTrace]
  refine ⟨123230583399623130026642767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164307444532830840035523689 123230583399623130026642767)
  ·
    refine ⟨184845875099434695039964151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123230583399623130026642767 184845875099434695039964151)
    ·
      refine ⟨277268812649152042559946227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184845875099434695039964151 277268812649152042559946227)
      ·
        refine ⟨415903218973728063839919341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277268812649152042559946227 415903218973728063839919341)
        ·
          refine ⟨155963707115148023939969753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415903218973728063839919341 155963707115148023939969753)
          ·
            refine ⟨116972780336361017954977315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155963707115148023939969753 116972780336361017954977315)
            ·
              refine ⟨175459170504541526932465973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116972780336361017954977315 175459170504541526932465973)
              ·
                refine ⟨16449297234800768149918685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175459170504541526932465973 16449297234800768149918685)
                ·
                  refine ⟨6168486463050288056219507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16449297234800768149918685 6168486463050288056219507)
                  ·
                    refine ⟨9252729694575432084329261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6168486463050288056219507 9252729694575432084329261)
                    ·
                      refine ⟨3469773635465787031623473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9252729694575432084329261 3469773635465787031623473)
                      ·
                        rfl

theorem cell23_6757360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 3, 1, 3].length) (baseStart_6757360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757360 prefixEnd_6757360 := by exact prefixLift 6757360
  have htrace : WordTrace (prefixWord ++ tailWord_6757360) baseStart_6757360 baseEnd_6757360 := by
    simpa [prefixWord, tailWord_6757360, baseEnd_6757360] using wordTrace_append hprefix tailTrace_6757360
  have hstable : (prefixWord ++ tailWord_6757360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757360).length < 2 ^ (prefixWord ++ tailWord_6757360).sum := by decide
  have hdescent : baseEnd_6757360 < baseStart_6757360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757370 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2]
def baseStart_6757370 : Nat := 118140960795 + 6757370 * 2 ^ 59
def prefixEnd_6757370 : Nat := 4983230072969 + 3 ^ 40 * 6757370 * 2
def baseEnd_6757370 : Nat := 3469778770272331992498427

theorem tailTrace_6757370 : CollatzResearch.WordTrace tailWord_6757370 prefixEnd_6757370 3469778770272331992498427 := by
  unfold tailWord_6757370
  simp only [CollatzResearch.WordTrace]
  refine ⟨61615382882302507940287391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164307687686140021174099709 61615382882302507940287391)
  ·
    refine ⟨92423074323453761910431087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61615382882302507940287391 92423074323453761910431087)
    ·
      refine ⟨138634611485180642865646631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92423074323453761910431087 138634611485180642865646631)
      ·
        refine ⟨207951917227770964298469947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138634611485180642865646631 207951917227770964298469947)
        ·
          refine ⟨311927875841656446447704921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207951917227770964298469947 311927875841656446447704921)
          ·
            refine ⟨233945906881242334835778691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311927875841656446447704921 233945906881242334835778691)
            ·
              refine ⟨350918860321863502253668037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233945906881242334835778691 350918860321863502253668037)
              ·
                refine ⟨65797286310349406672562757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350918860321863502253668037 65797286310349406672562757)
                ·
                  refine ⟨12336991183190513751105517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65797286310349406672562757 12336991183190513751105517)
                  ·
                    refine ⟨4626371693696442656664569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12336991183190513751105517 4626371693696442656664569)
                    ·
                      refine ⟨3469778770272331992498427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626371693696442656664569 3469778770272331992498427)
                      ·
                        rfl

theorem cell23_6757370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2].length) (baseStart_6757370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757370 prefixEnd_6757370 := by exact prefixLift 6757370
  have htrace : WordTrace (prefixWord ++ tailWord_6757370) baseStart_6757370 baseEnd_6757370 := by
    simpa [prefixWord, tailWord_6757370, baseEnd_6757370] using wordTrace_append hprefix tailTrace_6757370
  have hstable : (prefixWord ++ tailWord_6757370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757370).length < 2 ^ (prefixWord ++ tailWord_6757370).sum := by decide
  have hdescent : baseEnd_6757370 < baseStart_6757370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757377 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_6757377 : Nat := 118140960795 + 6757377 * 2 ^ 59
def prefixEnd_6757377 : Nat := 4983230072969 + 3 ^ 40 * 6757377 * 2
def baseEnd_6757377 : Nat := 3469782364636913465110895

theorem tailTrace_6757377 : CollatzResearch.WordTrace tailWord_6757377 prefixEnd_6757377 3469782364636913465110895 := by
  unfold tailWord_6757377
  simp only [CollatzResearch.WordTrace]
  refine ⟨246461786840184671956654385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164307857893456447971102923 246461786840184671956654385)
  ·
    refine ⟨184846340130138503967490789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246461786840184671956654385 184846340130138503967490789)
    ·
      refine ⟨34658688774400969493904523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184846340130138503967490789 34658688774400969493904523)
      ·
        refine ⟨51988033161601454240856785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34658688774400969493904523 51988033161601454240856785)
        ·
          refine ⟨38991024871201090680642589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51988033161601454240856785 38991024871201090680642589)
          ·
            refine ⟨14621634326700409005240971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38991024871201090680642589 14621634326700409005240971)
            ·
              refine ⟨21932451490050613507861457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14621634326700409005240971 21932451490050613507861457)
              ·
                refine ⟨16449338617537960130896093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21932451490050613507861457 16449338617537960130896093)
                ·
                  refine ⟨6168501981576735049086035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16449338617537960130896093 6168501981576735049086035)
                  ·
                    refine ⟨9252752972365102573629053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6168501981576735049086035 9252752972365102573629053)
                    ·
                      refine ⟨3469782364636913465110895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9252752972365102573629053 3469782364636913465110895)
                      ·
                        rfl

theorem cell23_6757377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_6757377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757377 prefixEnd_6757377 := by exact prefixLift 6757377
  have htrace : WordTrace (prefixWord ++ tailWord_6757377) baseStart_6757377 baseEnd_6757377 := by
    simpa [prefixWord, tailWord_6757377, baseEnd_6757377] using wordTrace_append hprefix tailTrace_6757377
  have hstable : (prefixWord ++ tailWord_6757377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757377).length < 2 ^ (prefixWord ++ tailWord_6757377).sum := by decide
  have hdescent : baseEnd_6757377 < baseStart_6757377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757387 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 2, 3, 2]
def baseStart_6757387 : Nat := 118140960795 + 6757387 * 2 ^ 59
def prefixEnd_6757387 : Nat := 4983230072969 + 3 ^ 40 * 6757387 * 2
def baseEnd_6757387 : Nat := 3469787499443458425985849

theorem tailTrace_6757387 : CollatzResearch.WordTrace tailWord_6757387 prefixEnd_6757387 3469787499443458425985849 := by
  unfold tailWord_6757387
  simp only [CollatzResearch.WordTrace]
  refine ⟨246462151570148443664518415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164308101046765629109678943 246462151570148443664518415)
  ·
    refine ⟨369693227355222665496777623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246462151570148443664518415 369693227355222665496777623)
    ·
      refine ⟨554539841032833998245166435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369693227355222665496777623 554539841032833998245166435)
      ·
        refine ⟨831809761549250997367749653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554539841032833998245166435 831809761549250997367749653)
        ·
          refine ⟨38991082572621140501613265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 831809761549250997367749653 38991082572621140501613265)
          ·
            refine ⟨29243311929465855376209949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38991082572621140501613265 29243311929465855376209949)
            ·
              refine ⟨10966241973549695766078731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29243311929465855376209949 10966241973549695766078731)
              ·
                refine ⟨16449362960324543649118097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10966241973549695766078731 16449362960324543649118097)
                ·
                  refine ⟨12337022220243407736838573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16449362960324543649118097 12337022220243407736838573)
                  ·
                    refine ⟨4626383332591277901314465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12337022220243407736838573 4626383332591277901314465)
                    ·
                      refine ⟨3469787499443458425985849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626383332591277901314465 3469787499443458425985849)
                      ·
                        rfl

theorem cell23_6757387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 3, 2].length) (baseStart_6757387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757387 prefixEnd_6757387 := by exact prefixLift 6757387
  have htrace : WordTrace (prefixWord ++ tailWord_6757387) baseStart_6757387 baseEnd_6757387 := by
    simpa [prefixWord, tailWord_6757387, baseEnd_6757387] using wordTrace_append hprefix tailTrace_6757387
  have hstable : (prefixWord ++ tailWord_6757387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757387).length < 2 ^ (prefixWord ++ tailWord_6757387).sum := by decide
  have hdescent : baseEnd_6757387 < baseStart_6757387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757397 : List Nat := [1, 3, 2, 1, 4, 1, 4, 1, 1, 5]
def baseStart_6757397 : Nat := 118140960795 + 6757397 * 2 ^ 59
def prefixEnd_6757397 : Nat := 4983230072969 + 3 ^ 40 * 6757397 * 2
def baseEnd_6757397 : Nat := 1156597544750001128953601

theorem tailTrace_6757397 : CollatzResearch.WordTrace tailWord_6757397 prefixEnd_6757397 1156597544750001128953601 := by
  unfold tailWord_6757397
  simp only [CollatzResearch.WordTrace]
  refine ⟨246462516300112215372382445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164308344200074810248254963 246462516300112215372382445)
  ·
    refine ⟨92423443612542080764643417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246462516300112215372382445 92423443612542080764643417)
    ·
      refine ⟨69317582709406560573482563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92423443612542080764643417 69317582709406560573482563)
      ·
        refine ⟨103976374064109840860223845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69317582709406560573482563 103976374064109840860223845)
        ·
          refine ⟨19495570137020595161291971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103976374064109840860223845 19495570137020595161291971)
          ·
            refine ⟨29243355205530892741937957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19495570137020595161291971 29243355205530892741937957)
            ·
              refine ⟨5483129101037042389113367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29243355205530892741937957 5483129101037042389113367)
              ·
                refine ⟨8224693651555563583670051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5483129101037042389113367 8224693651555563583670051)
                ·
                  refine ⟨12337040477333345375505077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8224693651555563583670051 12337040477333345375505077)
                  ·
                    refine ⟨1156597544750001128953601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12337040477333345375505077 1156597544750001128953601)
                    ·
                      rfl

theorem cell23_6757397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_6757397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757397 prefixEnd_6757397 := by exact prefixLift 6757397
  have htrace : WordTrace (prefixWord ++ tailWord_6757397) baseStart_6757397 baseEnd_6757397 := by
    simpa [prefixWord, tailWord_6757397, baseEnd_6757397] using wordTrace_append hprefix tailTrace_6757397
  have hstable : (prefixWord ++ tailWord_6757397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757397).length < 2 ^ (prefixWord ++ tailWord_6757397).sum := by decide
  have hdescent : baseEnd_6757397 < baseStart_6757397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757413 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_6757413 : Nat := 118140960795 + 6757413 * 2 ^ 59
def prefixEnd_6757413 : Nat := 4983230072969 + 3 ^ 40 * 6757413 * 2
def baseEnd_6757413 : Nat := 3469800849940475324260729

theorem tailTrace_6757413 : CollatzResearch.WordTrace tailWord_6757413 prefixEnd_6757413 3469800849940475324260729 := by
  unfold tailWord_6757413
  simp only [CollatzResearch.WordTrace]
  refine ⟨246463099868054250104964893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164308733245369500069976595 246463099868054250104964893)
  ·
    refine ⟨92423662450520343789361835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246463099868054250104964893 92423662450520343789361835)
    ·
      refine ⟨138635493675780515684042753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92423662450520343789361835 138635493675780515684042753)
      ·
        refine ⟨103976620256835386763032065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138635493675780515684042753 103976620256835386763032065)
        ·
          refine ⟨77982465192626540072274049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103976620256835386763032065 77982465192626540072274049)
          ·
            refine ⟨58486848894469905054205537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77982465192626540072274049 58486848894469905054205537)
            ·
              refine ⟨43865136670852428790654153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58486848894469905054205537 43865136670852428790654153)
              ·
                refine ⟨32898852503139321592990615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43865136670852428790654153 32898852503139321592990615)
                ·
                  refine ⟨49348278754708982389485923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32898852503139321592990615 49348278754708982389485923)
                  ·
                    refine ⟨74022418132063473584228885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49348278754708982389485923 74022418132063473584228885)
                    ·
                      refine ⟨3469800849940475324260729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74022418132063473584228885 3469800849940475324260729)
                      ·
                        rfl

theorem cell23_6757413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_6757413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757413 prefixEnd_6757413 := by exact prefixLift 6757413
  have htrace : WordTrace (prefixWord ++ tailWord_6757413) baseStart_6757413 baseEnd_6757413 := by
    simpa [prefixWord, tailWord_6757413, baseEnd_6757413] using wordTrace_append hprefix tailTrace_6757413
  have hstable : (prefixWord ++ tailWord_6757413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757413).length < 2 ^ (prefixWord ++ tailWord_6757413).sum := by decide
  have hdescent : baseEnd_6757413 < baseStart_6757413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757437 : List Nat := [1, 4, 1, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_6757437 : Nat := 118140960795 + 6757437 * 2 ^ 59
def prefixEnd_6757437 : Nat := 4983230072969 + 3 ^ 40 * 6757437 * 2
def baseEnd_6757437 : Nat := 3469813173476183230360619

theorem tailTrace_6757437 : CollatzResearch.WordTrace tailWord_6757437 prefixEnd_6757437 3469813173476183230360619 := by
  unfold tailWord_6757437
  simp only [CollatzResearch.WordTrace]
  refine ⟨246463975219967302203838565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164309316813311534802559043 246463975219967302203838565)
  ·
    refine ⟨46211995353743869163219731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246463975219967302203838565 46211995353743869163219731)
    ·
      refine ⟨69317993030615803744829597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46211995353743869163219731 69317993030615803744829597)
      ·
        refine ⟨25994247386480926404311099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69317993030615803744829597 25994247386480926404311099)
        ·
          refine ⟨38991371079721389606466649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25994247386480926404311099 38991371079721389606466649)
          ·
            refine ⟨29243528309791042204849987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38991371079721389606466649 29243528309791042204849987)
            ·
              refine ⟨43865292464686563307274981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29243528309791042204849987 43865292464686563307274981)
              ·
                refine ⟨8224742337128730620114059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43865292464686563307274981 8224742337128730620114059)
                ·
                  refine ⟨12337113505693095930171089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8224742337128730620114059 12337113505693095930171089)
                  ·
                    refine ⟨9252835129269821947628317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12337113505693095930171089 9252835129269821947628317)
                    ·
                      refine ⟨3469813173476183230360619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9252835129269821947628317 3469813173476183230360619)
                      ·
                        rfl

theorem cell23_6757437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_6757437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757437 prefixEnd_6757437 := by exact prefixLift 6757437
  have htrace : WordTrace (prefixWord ++ tailWord_6757437) baseStart_6757437 baseEnd_6757437 := by
    simpa [prefixWord, tailWord_6757437, baseEnd_6757437] using wordTrace_append hprefix tailTrace_6757437
  have hstable : (prefixWord ++ tailWord_6757437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757437).length < 2 ^ (prefixWord ++ tailWord_6757437).sum := by decide
  have hdescent : baseEnd_6757437 < baseStart_6757437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757450 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_6757450 : Nat := 118140960795 + 6757450 * 2 ^ 59
def prefixEnd_6757450 : Nat := 4983230072969 + 3 ^ 40 * 6757450 * 2
def baseEnd_6757450 : Nat := 3469819848724691679498059

theorem tailTrace_6757450 : CollatzResearch.WordTrace tailWord_6757450 prefixEnd_6757450 3469819848724691679498059 := by
  unfold tailWord_6757450
  simp only [CollatzResearch.WordTrace]
  refine ⟨61616112342230051356015451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164309632912613470282707869 61616112342230051356015451)
  ·
    refine ⟨92424168513345077034023177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61616112342230051356015451 92424168513345077034023177)
    ·
      refine ⟨69318126385008807775517383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92424168513345077034023177 69318126385008807775517383)
      ·
        refine ⟨103977189577513211663276075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69318126385008807775517383 103977189577513211663276075)
        ·
          refine ⟨155965784366269817494914113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103977189577513211663276075 155965784366269817494914113)
          ·
            refine ⟨116974338274702363121185585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155965784366269817494914113 116974338274702363121185585)
            ·
              refine ⟨87730753706026772340889189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116974338274702363121185585 87730753706026772340889189)
              ·
                refine ⟨16449516319880019813916723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87730753706026772340889189 16449516319880019813916723)
                ·
                  refine ⟨24674274479820029720875085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16449516319880019813916723 24674274479820029720875085)
                  ·
                    refine ⟨9252852929932511145328157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24674274479820029720875085 9252852929932511145328157)
                    ·
                      refine ⟨3469819848724691679498059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9252852929932511145328157 3469819848724691679498059)
                      ·
                        rfl

theorem cell23_6757450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_6757450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757450 prefixEnd_6757450 := by exact prefixLift 6757450
  have htrace : WordTrace (prefixWord ++ tailWord_6757450) baseStart_6757450 baseEnd_6757450 := by
    simpa [prefixWord, tailWord_6757450, baseEnd_6757450] using wordTrace_append hprefix tailTrace_6757450
  have hstable : (prefixWord ++ tailWord_6757450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757450).length < 2 ^ (prefixWord ++ tailWord_6757450).sum := by decide
  have hdescent : baseEnd_6757450 < baseStart_6757450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757463 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_6757463 : Nat := 118140960795 + 6757463 * 2 ^ 59
def prefixEnd_6757463 : Nat := 4983230072969 + 3 ^ 40 * 6757463 * 2
def baseEnd_6757463 : Nat := 3469826523973200128635499

theorem tailTrace_6757463 : CollatzResearch.WordTrace tailWord_6757463 prefixEnd_6757463 3469826523973200128635499 := by
  unfold tailWord_6757463
  simp only [CollatzResearch.WordTrace]
  refine ⟨246464923517873108644285043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164309949011915405762856695 246464923517873108644285043)
  ·
    refine ⟨369697385276809662966427565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246464923517873108644285043 369697385276809662966427565)
    ·
      refine ⟨138636519478803623612410337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369697385276809662966427565 138636519478803623612410337)
      ·
        refine ⟨103977389609102717709307753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138636519478803623612410337 103977389609102717709307753)
        ·
          refine ⟨77983042206827038281980815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103977389609102717709307753 77983042206827038281980815)
          ·
            refine ⟨116974563310240557422971223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77983042206827038281980815 116974563310240557422971223)
            ·
              refine ⟨175461844965360836134456835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116974563310240557422971223 175461844965360836134456835)
              ·
                refine ⟨263192767448041254201685253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175461844965360836134456835 263192767448041254201685253)
                ·
                  refine ⟨49348643896507735162815985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263192767448041254201685253 49348643896507735162815985)
                  ·
                    refine ⟨37011482922380801372111989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49348643896507735162815985 37011482922380801372111989)
                    ·
                      refine ⟨3469826523973200128635499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37011482922380801372111989 3469826523973200128635499)
                      ·
                        rfl

theorem cell23_6757463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_6757463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757463 prefixEnd_6757463 := by exact prefixLift 6757463
  have htrace : WordTrace (prefixWord ++ tailWord_6757463) baseStart_6757463 baseEnd_6757463 := by
    simpa [prefixWord, tailWord_6757463, baseEnd_6757463] using wordTrace_append hprefix tailTrace_6757463
  have hstable : (prefixWord ++ tailWord_6757463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757463).length < 2 ^ (prefixWord ++ tailWord_6757463).sum := by decide
  have hdescent : baseEnd_6757463 < baseStart_6757463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757468 : List Nat := [2, 2, 4, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_6757468 : Nat := 118140960795 + 6757468 * 2 ^ 59
def prefixEnd_6757468 : Nat := 4983230072969 + 3 ^ 40 * 6757468 * 2
def baseEnd_6757468 : Nat := 3469829091376472609072977

theorem tailTrace_6757468 : CollatzResearch.WordTrace tailWord_6757468 prefixEnd_6757468 3469829091376472609072977 := by
  unfold tailWord_6757468
  simp only [CollatzResearch.WordTrace]
  refine ⟨123232552941427497249108529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164310070588569996332144705 123232552941427497249108529)
  ·
    refine ⟨92424414706070622936831397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123232552941427497249108529 92424414706070622936831397)
    ·
      refine ⟨17329577757388241800655887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92424414706070622936831397 17329577757388241800655887)
      ·
        refine ⟨25994366636082362700983831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17329577757388241800655887 25994366636082362700983831)
        ·
          refine ⟨38991549954123544051475747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25994366636082362700983831 38991549954123544051475747)
          ·
            refine ⟨58487324931185316077213621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38991549954123544051475747 58487324931185316077213621)
            ·
              refine ⟨5483186712298623382238777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58487324931185316077213621 5483186712298623382238777)
              ·
                refine ⟨4112390034223967536679083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5483186712298623382238777 4112390034223967536679083)
                ·
                  refine ⟨6168585051335951305018625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4112390034223967536679083 6168585051335951305018625)
                  ·
                    refine ⟨4626438788501963478763969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6168585051335951305018625 4626438788501963478763969)
                    ·
                      refine ⟨3469829091376472609072977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626438788501963478763969 3469829091376472609072977)
                      ·
                        rfl

theorem cell23_6757468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_6757468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757468 prefixEnd_6757468 := by exact prefixLift 6757468
  have htrace : WordTrace (prefixWord ++ tailWord_6757468) baseStart_6757468 baseEnd_6757468 := by
    simpa [prefixWord, tailWord_6757468, baseEnd_6757468] using wordTrace_append hprefix tailTrace_6757468
  have hstable : (prefixWord ++ tailWord_6757468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757468).length < 2 ^ (prefixWord ++ tailWord_6757468).sum := by decide
  have hdescent : baseEnd_6757468 < baseStart_6757468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757477 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 3, 3, 2]
def baseStart_6757477 : Nat := 118140960795 + 6757477 * 2 ^ 59
def prefixEnd_6757477 : Nat := 4983230072969 + 3 ^ 40 * 6757477 * 2
def baseEnd_6757477 : Nat := 3469833712702363073860435

theorem tailTrace_6757477 : CollatzResearch.WordTrace tailWord_6757477 prefixEnd_6757477 3469833712702363073860435 := by
  unfold tailWord_6757477
  simp only [CollatzResearch.WordTrace]
  refine ⟨246465434139822389035294685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164310289426548259356863123 246465434139822389035294685)
  ·
    refine ⟨92424537802433395888235507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246465434139822389035294685 92424537802433395888235507)
    ·
      refine ⟨138636806703650093832353261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92424537802433395888235507 138636806703650093832353261)
      ·
        refine ⟨51988802513868785187132473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138636806703650093832353261 51988802513868785187132473)
        ·
          refine ⟨38991601885401588890349355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51988802513868785187132473 38991601885401588890349355)
          ·
            refine ⟨58487402828102383335524033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38991601885401588890349355 58487402828102383335524033)
            ·
              refine ⟨43865552121076787501643025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58487402828102383335524033 43865552121076787501643025)
              ·
                refine ⟨32899164090807590626232269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43865552121076787501643025 32899164090807590626232269)
                ·
                  refine ⟨12337186534052846484837101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32899164090807590626232269 12337186534052846484837101)
                  ·
                    refine ⟨4626444950269817431813913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12337186534052846484837101 4626444950269817431813913)
                    ·
                      refine ⟨3469833712702363073860435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626444950269817431813913 3469833712702363073860435)
                      ·
                        rfl

theorem cell23_6757477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_6757477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757477 prefixEnd_6757477 := by exact prefixLift 6757477
  have htrace : WordTrace (prefixWord ++ tailWord_6757477) baseStart_6757477 baseEnd_6757477 := by
    simpa [prefixWord, tailWord_6757477, baseEnd_6757477] using wordTrace_append hprefix tailTrace_6757477
  have hstable : (prefixWord ++ tailWord_6757477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757477).length < 2 ^ (prefixWord ++ tailWord_6757477).sum := by decide
  have hdescent : baseEnd_6757477 < baseStart_6757477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757494 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_6757494 : Nat := 118140960795 + 6757494 * 2 ^ 59
def prefixEnd_6757494 : Nat := 4983230072969 + 3 ^ 40 * 6757494 * 2
def baseEnd_6757494 : Nat := 3469842441873489507347857

theorem tailTrace_6757494 : CollatzResearch.WordTrace tailWord_6757494 prefixEnd_6757494 3469842441873489507347857 := by
  unfold tailWord_6757494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15404128386297550058666471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164310702787173867292442357 15404128386297550058666471)
  ·
    refine ⟨23106192579446325087999707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15404128386297550058666471 23106192579446325087999707)
    ·
      refine ⟨34659288869169487631999561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23106192579446325087999707 34659288869169487631999561)
      ·
        refine ⟨25994466651877115723999671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34659288869169487631999561 25994466651877115723999671)
        ·
          refine ⟨38991699977815673585999507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25994466651877115723999671 38991699977815673585999507)
          ·
            refine ⟨58487549966723510378999261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38991699977815673585999507 58487549966723510378999261)
            ·
              refine ⟨21932831237521316392124723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58487549966723510378999261 21932831237521316392124723)
              ·
                refine ⟨32899246856281974588187085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21932831237521316392124723 32899246856281974588187085)
                ·
                  refine ⟨12337217571105740470570157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32899246856281974588187085 12337217571105740470570157)
                  ·
                    refine ⟨4626456589164652676463809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12337217571105740470570157 4626456589164652676463809)
                    ·
                      refine ⟨3469842441873489507347857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626456589164652676463809 3469842441873489507347857)
                      ·
                        rfl

theorem cell23_6757494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_6757494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757494 prefixEnd_6757494 := by exact prefixLift 6757494
  have htrace : WordTrace (prefixWord ++ tailWord_6757494) baseStart_6757494 baseEnd_6757494 := by
    simpa [prefixWord, tailWord_6757494, baseEnd_6757494] using wordTrace_append hprefix tailTrace_6757494
  have hstable : (prefixWord ++ tailWord_6757494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757494).length < 2 ^ (prefixWord ++ tailWord_6757494).sum := by decide
  have hdescent : baseEnd_6757494 < baseStart_6757494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757507 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 1, 4, 2]
def baseStart_6757507 : Nat := 118140960795 + 6757507 * 2 ^ 59
def prefixEnd_6757507 : Nat := 4983230072969 + 3 ^ 40 * 6757507 * 2
def baseEnd_6757507 : Nat := 3469849117121997956485297

theorem tailTrace_6757507 : CollatzResearch.WordTrace tailWord_6757507 prefixEnd_6757507 3469849117121997956485297 := by
  unfold tailWord_6757507
  simp only [CollatzResearch.WordTrace]
  refine ⟨246466528329713704158886775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164311018886475802772591183 246466528329713704158886775)
  ·
    refine ⟨369699792494570556238330163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246466528329713704158886775 369699792494570556238330163)
    ·
      refine ⟨554549688741855834357495245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369699792494570556238330163 554549688741855834357495245)
      ·
        refine ⟨207956133278195937884060717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 554549688741855834357495245 207956133278195937884060717)
        ·
          refine ⟨77983549979323476706522769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207956133278195937884060717 77983549979323476706522769)
          ·
            refine ⟨58487662484492607529892077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77983549979323476706522769 58487662484492607529892077)
            ·
              refine ⟨21932873431684727823709529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58487662484492607529892077 21932873431684727823709529)
              ·
                refine ⟨16449655073763545867782147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21932873431684727823709529 16449655073763545867782147)
                ·
                  refine ⟨24674482610645318801673221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16449655073763545867782147 24674482610645318801673221)
                  ·
                    refine ⟨4626465489495997275313729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24674482610645318801673221 4626465489495997275313729)
                    ·
                      refine ⟨3469849117121997956485297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626465489495997275313729 3469849117121997956485297)
                      ·
                        rfl

theorem cell23_6757507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 4, 2].length) (baseStart_6757507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757507 prefixEnd_6757507 := by exact prefixLift 6757507
  have htrace : WordTrace (prefixWord ++ tailWord_6757507) baseStart_6757507 baseEnd_6757507 := by
    simpa [prefixWord, tailWord_6757507, baseEnd_6757507] using wordTrace_append hprefix tailTrace_6757507
  have hstable : (prefixWord ++ tailWord_6757507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757507).length < 2 ^ (prefixWord ++ tailWord_6757507).sum := by decide
  have hdescent : baseEnd_6757507 < baseStart_6757507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757523 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 7]
def baseStart_6757523 : Nat := 118140960795 + 6757523 * 2 ^ 59
def prefixEnd_6757523 : Nat := 4983230072969 + 3 ^ 40 * 6757523 * 2
def baseEnd_6757523 : Nat := 3469857332812469893885223

theorem tailTrace_6757523 : CollatzResearch.WordTrace tailWord_6757523 prefixEnd_6757523 3469857332812469893885223 := by
  unfold tailWord_6757523
  simp only [CollatzResearch.WordTrace]
  refine ⟨246467111897655738891469223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164311407931770492594312815 246467111897655738891469223)
  ·
    refine ⟨369700667846483608337203835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246467111897655738891469223 369700667846483608337203835)
    ·
      refine ⟨554551001769725412505805753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369700667846483608337203835 554551001769725412505805753)
      ·
        refine ⟨415913251327294059379354315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554551001769725412505805753 415913251327294059379354315)
        ·
          refine ⟨623869876990941089069031473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415913251327294059379354315 623869876990941089069031473)
          ·
            refine ⟨467902407743205816801773605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623869876990941089069031473 467902407743205816801773605)
            ·
              refine ⟨87731701451851090650332551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 467902407743205816801773605 87731701451851090650332551)
              ·
                refine ⟨131597552177776635975498827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87731701451851090650332551 131597552177776635975498827)
                ·
                  refine ⟨197396328266664953963248241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131597552177776635975498827 197396328266664953963248241)
                  ·
                    refine ⟨148047246199998715472436181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197396328266664953963248241 148047246199998715472436181)
                    ·
                      refine ⟨3469857332812469893885223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148047246199998715472436181 3469857332812469893885223)
                      ·
                        rfl

theorem cell23_6757523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_6757523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757523 prefixEnd_6757523 := by exact prefixLift 6757523
  have htrace : WordTrace (prefixWord ++ tailWord_6757523) baseStart_6757523 baseEnd_6757523 := by
    simpa [prefixWord, tailWord_6757523, baseEnd_6757523] using wordTrace_append hprefix tailTrace_6757523
  have hstable : (prefixWord ++ tailWord_6757523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757523).length < 2 ^ (prefixWord ++ tailWord_6757523).sum := by decide
  have hdescent : baseEnd_6757523 < baseStart_6757523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757560 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 2, 5]
def baseStart_6757560 : Nat := 118140960795 + 6757560 * 2 ^ 59
def prefixEnd_6757560 : Nat := 4983230072969 + 3 ^ 40 * 6757560 * 2
def baseEnd_6757560 : Nat := 1156625443865562083040851

theorem tailTrace_6757560 : CollatzResearch.WordTrace tailWord_6757560 prefixEnd_6757560 1156625443865562083040851 := by
  unfold tailWord_6757560
  simp only [CollatzResearch.WordTrace]
  refine ⟨123234230699260847105283067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164312307599014462807044089 123234230699260847105283067)
  ·
    refine ⟨184851346048891270657924601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123234230699260847105283067 184851346048891270657924601)
    ·
      refine ⟨138638509536668452993443451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184851346048891270657924601 138638509536668452993443451)
      ·
        refine ⟨207957764305002679490165177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138638509536668452993443451 207957764305002679490165177)
        ·
          refine ⟨155968323228752009617623883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207957764305002679490165177 155968323228752009617623883)
          ·
            refine ⟨233952484843128014426435825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155968323228752009617623883 233952484843128014426435825)
            ·
              refine ⟨175464363632346010819826869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233952484843128014426435825 175464363632346010819826869)
              ·
                refine ⟨16449784090532438514358769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175464363632346010819826869 16449784090532438514358769)
                ·
                  refine ⟨12337338067899328885769077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16449784090532438514358769 12337338067899328885769077)
                  ·
                    refine ⟨1156625443865562083040851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12337338067899328885769077 1156625443865562083040851)
                    ·
                      rfl

theorem cell23_6757560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_6757560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757560 prefixEnd_6757560 := by exact prefixLift 6757560
  have htrace : WordTrace (prefixWord ++ tailWord_6757560) baseStart_6757560 baseEnd_6757560 := by
    simpa [prefixWord, tailWord_6757560, baseEnd_6757560] using wordTrace_append hprefix tailTrace_6757560
  have hstable : (prefixWord ++ tailWord_6757560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757560).length < 2 ^ (prefixWord ++ tailWord_6757560).sum := by decide
  have hdescent : baseEnd_6757560 < baseStart_6757560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757564 : List Nat := [2, 2, 2, 3, 2, 2, 2, 3, 5]
def baseStart_6757564 : Nat := 118140960795 + 6757564 * 2 ^ 59
def prefixEnd_6757564 : Nat := 4983230072969 + 3 ^ 40 * 6757564 * 2
def baseEnd_6757564 : Nat := 385542042835478248163615

theorem tailTrace_6757564 : CollatzResearch.WordTrace tailWord_6757564 prefixEnd_6757564 385542042835478248163615 := by
  unfold tailWord_6757564
  simp only [CollatzResearch.WordTrace]
  refine ⟨123234303645253601446855873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164312404860338135262474497 123234303645253601446855873)
  ·
    refine ⟨92425727733940201085141905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123234303645253601446855873 92425727733940201085141905)
    ·
      refine ⟨69319295800455150813856429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92425727733940201085141905 69319295800455150813856429)
      ·
        refine ⟨25994735925170681555196161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69319295800455150813856429 25994735925170681555196161)
        ·
          refine ⟨19496051943878011166397121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25994735925170681555196161 19496051943878011166397121)
          ·
            refine ⟨14622038957908508374797841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19496051943878011166397121 14622038957908508374797841)
            ·
              refine ⟨10966529218431381281098381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14622038957908508374797841 10966529218431381281098381)
              ·
                refine ⟨4112448456911767980411893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10966529218431381281098381 4112448456911767980411893)
                ·
                  refine ⟨385542042835478248163615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4112448456911767980411893 385542042835478248163615)
                  ·
                    rfl

theorem cell23_6757564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 5].length) (baseStart_6757564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757564 prefixEnd_6757564 := by exact prefixLift 6757564
  have htrace : WordTrace (prefixWord ++ tailWord_6757564) baseStart_6757564 baseEnd_6757564 := by
    simpa [prefixWord, tailWord_6757564, baseEnd_6757564] using wordTrace_append hprefix tailTrace_6757564
  have hstable : (prefixWord ++ tailWord_6757564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757564).length < 2 ^ (prefixWord ++ tailWord_6757564).sum := by decide
  have hdescent : baseEnd_6757564 < baseStart_6757564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757581 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 7]
def baseStart_6757581 : Nat := 118140960795 + 6757581 * 2 ^ 59
def prefixEnd_6757581 : Nat := 4983230072969 + 3 ^ 40 * 6757581 * 2
def baseEnd_6757581 : Nat := 385543012743381185217773

theorem tailTrace_6757581 : CollatzResearch.WordTrace tailWord_6757581 prefixEnd_6757581 385543012743381185217773 := by
  unfold tailWord_6757581
  simp only [CollatzResearch.WordTrace]
  refine ⟨246469227331445614797080597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164312818220963743198053731 246469227331445614797080597)
  ·
    refine ⟨11553245031161513193613153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 246469227331445614797080597 11553245031161513193613153)
    ·
      refine ⟨8664933773371134895209865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11553245031161513193613153 8664933773371134895209865)
      ·
        refine ⟨6498700330028351171407399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8664933773371134895209865 6498700330028351171407399)
        ·
          refine ⟨9748050495042526757111099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6498700330028351171407399 9748050495042526757111099)
          ·
            refine ⟨14622075742563790135666649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9748050495042526757111099 14622075742563790135666649)
            ·
              refine ⟨10966556806922842601749987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14622075742563790135666649 10966556806922842601749987)
              ·
                refine ⟨16449835210384263902624981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10966556806922842601749987 16449835210384263902624981)
                ·
                  refine ⟨385543012743381185217773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16449835210384263902624981 385543012743381185217773)
                  ·
                    rfl

theorem cell23_6757581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_6757581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757581 prefixEnd_6757581 := by exact prefixLift 6757581
  have htrace : WordTrace (prefixWord ++ tailWord_6757581) baseStart_6757581 baseEnd_6757581 := by
    simpa [prefixWord, tailWord_6757581, baseEnd_6757581] using wordTrace_append hprefix tailTrace_6757581
  have hstable : (prefixWord ++ tailWord_6757581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757581).length < 2 ^ (prefixWord ++ tailWord_6757581).sum := by decide
  have hdescent : baseEnd_6757581 < baseStart_6757581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757617 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 2, 2, 3]
def baseStart_6757617 : Nat := 118140960795 + 6757617 * 2 ^ 59
def prefixEnd_6757617 : Nat := 4983230072969 + 3 ^ 40 * 6757617 * 2
def baseEnd_6757617 : Nat := 3469905599993992526109791

theorem tailTrace_6757617 : CollatzResearch.WordTrace tailWord_6757617 prefixEnd_6757617 3469905599993992526109791 := by
  unfold tailWord_6757617
  simp only [CollatzResearch.WordTrace]
  refine ⟨246470540359315192945391105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164313693572876795296927403 246470540359315192945391105)
  ·
    refine ⟨184852905269486394709043329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246470540359315192945391105 184852905269486394709043329)
    ·
      refine ⟨138639678952114796031782497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184852905269486394709043329 138639678952114796031782497)
      ·
        refine ⟨103979759214086097023836873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138639678952114796031782497 103979759214086097023836873)
        ·
          refine ⟨77984819410564572767877655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103979759214086097023836873 77984819410564572767877655)
          ·
            refine ⟨116977229115846859151816483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77984819410564572767877655 116977229115846859151816483)
            ·
              refine ⟨175465843673770288727724725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116977229115846859151816483 175465843673770288727724725)
              ·
                refine ⟨16449922844415964568224193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175465843673770288727724725 16449922844415964568224193)
                ·
                  refine ⟨12337442133311973426168145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16449922844415964568224193 12337442133311973426168145)
                  ·
                    refine ⟨9253081599983980069626109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12337442133311973426168145 9253081599983980069626109)
                    ·
                      refine ⟨3469905599993992526109791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9253081599983980069626109 3469905599993992526109791)
                      ·
                        rfl

theorem cell23_6757617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_6757617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757617 prefixEnd_6757617 := by exact prefixLift 6757617
  have htrace : WordTrace (prefixWord ++ tailWord_6757617) baseStart_6757617 baseEnd_6757617 := by
    simpa [prefixWord, tailWord_6757617, baseEnd_6757617] using wordTrace_append hprefix tailTrace_6757617
  have hstable : (prefixWord ++ tailWord_6757617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757617).length < 2 ^ (prefixWord ++ tailWord_6757617).sum := by decide
  have hdescent : baseEnd_6757617 < baseStart_6757617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757641 : List Nat := [1, 2, 1, 1, 3, 3, 5, 2, 1, 4]
def baseStart_6757641 : Nat := 118140960795 + 6757641 * 2 ^ 59
def prefixEnd_6757641 : Nat := 4983230072969 + 3 ^ 40 * 6757641 * 2
def baseEnd_6757641 : Nat := 1156639307843233477403227

theorem tailTrace_6757641 : CollatzResearch.WordTrace tailWord_6757641 prefixEnd_6757641 1156639307843233477403227 := by
  unfold tailWord_6757641
  simp only [CollatzResearch.WordTrace]
  refine ⟨246471415711228245044264777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164314277140818830029509851 246471415711228245044264777)
  ·
    refine ⟨184853561783421183783198583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246471415711228245044264777 184853561783421183783198583)
    ·
      refine ⟨277280342675131775674797875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184853561783421183783198583 277280342675131775674797875)
      ·
        refine ⟨415920514012697663512196813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277280342675131775674797875 415920514012697663512196813)
        ·
          refine ⟨155970192754761623817073805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415920514012697663512196813 155970192754761623817073805)
          ·
            refine ⟨58488822283035608931402677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155970192754761623817073805 58488822283035608931402677)
            ·
              refine ⟨5483327089034588337319001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58488822283035608931402677 5483327089034588337319001)
              ·
                refine ⟨4112495316775941252989251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5483327089034588337319001 4112495316775941252989251)
                ·
                  refine ⟨6168742975163911879483877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4112495316775941252989251 6168742975163911879483877)
                  ·
                    refine ⟨1156639307843233477403227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6168742975163911879483877 1156639307843233477403227)
                    ·
                      rfl

theorem cell23_6757641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 1, 4].length) (baseStart_6757641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757641 prefixEnd_6757641 := by exact prefixLift 6757641
  have htrace : WordTrace (prefixWord ++ tailWord_6757641) baseStart_6757641 baseEnd_6757641 := by
    simpa [prefixWord, tailWord_6757641, baseEnd_6757641] using wordTrace_append hprefix tailTrace_6757641
  have hstable : (prefixWord ++ tailWord_6757641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757641).length < 2 ^ (prefixWord ++ tailWord_6757641).sum := by decide
  have hdescent : baseEnd_6757641 < baseStart_6757641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757667 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 3, 5]
def baseStart_6757667 : Nat := 118140960795 + 6757667 * 2 ^ 59
def prefixEnd_6757667 : Nat := 4983230072969 + 3 ^ 40 * 6757667 * 2
def baseEnd_6757667 : Nat := 1156643758008905776828187

theorem tailTrace_6757667 : CollatzResearch.WordTrace tailWord_6757667 prefixEnd_6757667 1156643758008905776828187 := by
  unfold tailWord_6757667
  simp only [CollatzResearch.WordTrace]
  refine ⟨246472364009134051484711255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164314909339422700989807503 246472364009134051484711255)
  ·
    refine ⟨369708546013701077227066883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246472364009134051484711255 369708546013701077227066883)
    ·
      refine ⟨554562819020551615840600325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369708546013701077227066883 554562819020551615840600325)
      ·
        refine ⟨103980528566353427970112561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 554562819020551615840600325 103980528566353427970112561)
        ·
          refine ⟨77985396424765070977584421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103980528566353427970112561 77985396424765070977584421)
          ·
            refine ⟨14622261829643450808297079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77985396424765070977584421 14622261829643450808297079)
            ·
              refine ⟨21933392744465176212445619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14622261829643450808297079 21933392744465176212445619)
              ·
                refine ⟨32900089116697764318668429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21933392744465176212445619 32900089116697764318668429)
                ·
                  refine ⟨12337533418761661619500661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32900089116697764318668429 12337533418761661619500661)
                  ·
                    refine ⟨1156643758008905776828187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12337533418761661619500661 1156643758008905776828187)
                    ·
                      rfl

theorem cell23_6757667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 5].length) (baseStart_6757667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757667 prefixEnd_6757667 := by exact prefixLift 6757667
  have htrace : WordTrace (prefixWord ++ tailWord_6757667) baseStart_6757667 baseEnd_6757667 := by
    simpa [prefixWord, tailWord_6757667, baseEnd_6757667] using wordTrace_append hprefix tailTrace_6757667
  have hstable : (prefixWord ++ tailWord_6757667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757667).length < 2 ^ (prefixWord ++ tailWord_6757667).sum := by decide
  have hdescent : baseEnd_6757667 < baseStart_6757667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757725 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6757725 : Nat := 118140960795 + 6757725 * 2 ^ 59
def prefixEnd_6757725 : Nat := 4983230072969 + 3 ^ 40 * 6757725 * 2
def baseEnd_6757725 : Nat := 3469961055904678103559295

theorem tailTrace_6757725 : CollatzResearch.WordTrace tailWord_6757725 prefixEnd_6757725 3469961055904678103559295 := by
  unfold tailWord_6757725
  simp only [CollatzResearch.WordTrace]
  refine ⟨246474479442923927390322629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164316319628615951593548419 246474479442923927390322629)
  ·
    refine ⟨46213964895548236385685493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246474479442923927390322629 46213964895548236385685493)
    ·
      refine ⟨4332559208957647161158015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46213964895548236385685493 4332559208957647161158015)
      ·
        refine ⟨6498838813436470741737023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4332559208957647161158015 6498838813436470741737023)
        ·
          refine ⟨9748258220154706112605535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6498838813436470741737023 9748258220154706112605535)
          ·
            refine ⟨14622387330232059168908303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9748258220154706112605535 14622387330232059168908303)
            ·
              refine ⟨21933580995348088753362455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14622387330232059168908303 21933580995348088753362455)
              ·
                refine ⟨32900371493022133130043683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21933580995348088753362455 32900371493022133130043683)
                ·
                  refine ⟨49350557239533199695065525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32900371493022133130043683 49350557239533199695065525)
                  ·
                    refine ⟨4626614741206237471412393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49350557239533199695065525 4626614741206237471412393)
                    ·
                      refine ⟨3469961055904678103559295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626614741206237471412393 3469961055904678103559295)
                      ·
                        rfl

theorem cell23_6757725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6757725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757725 prefixEnd_6757725 := by exact prefixLift 6757725
  have htrace : WordTrace (prefixWord ++ tailWord_6757725) baseStart_6757725 baseEnd_6757725 := by
    simpa [prefixWord, tailWord_6757725, baseEnd_6757725] using wordTrace_append hprefix tailTrace_6757725
  have hstable : (prefixWord ++ tailWord_6757725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757725).length < 2 ^ (prefixWord ++ tailWord_6757725).sum := by decide
  have hdescent : baseEnd_6757725 < baseStart_6757725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757737 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 3, 3, 3]
def baseStart_6757737 : Nat := 118140960795 + 6757737 * 2 ^ 59
def prefixEnd_6757737 : Nat := 4983230072969 + 3 ^ 40 * 6757737 * 2
def baseEnd_6757737 : Nat := 3469967217672532056609239

theorem tailTrace_6757737 : CollatzResearch.WordTrace tailWord_6757737 prefixEnd_6757737 3469967217672532056609239 := by
  unfold tailWord_6757737
  simp only [CollatzResearch.WordTrace]
  refine ⟨246474917118880453439759465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164316611412586968959839643 246474917118880453439759465)
  ·
    refine ⟨184856187839160340079819599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246474917118880453439759465 184856187839160340079819599)
    ·
      refine ⟨277284281758740510119729399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184856187839160340079819599 277284281758740510119729399)
      ·
        refine ⟨415926422638110765179594099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277284281758740510119729399 415926422638110765179594099)
        ·
          refine ⟨623889633957166147769391149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415926422638110765179594099 623889633957166147769391149)
          ·
            refine ⟨233958612733937305413521681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 623889633957166147769391149 233958612733937305413521681)
            ·
              refine ⟨175468959550452979060141261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233958612733937305413521681 175468959550452979060141261)
              ·
                refine ⟨65800859831419867147552973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175468959550452979060141261 65800859831419867147552973)
                ·
                  refine ⟨24675322436782450180332365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65800859831419867147552973 24675322436782450180332365)
                  ·
                    refine ⟨9253245913793418817624637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24675322436782450180332365 9253245913793418817624637)
                    ·
                      refine ⟨3469967217672532056609239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9253245913793418817624637 3469967217672532056609239)
                      ·
                        rfl

theorem cell23_6757737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 3, 3].length) (baseStart_6757737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757737 prefixEnd_6757737 := by exact prefixLift 6757737
  have htrace : WordTrace (prefixWord ++ tailWord_6757737) baseStart_6757737 baseEnd_6757737 := by
    simpa [prefixWord, tailWord_6757737, baseEnd_6757737] using wordTrace_append hprefix tailTrace_6757737
  have hstable : (prefixWord ++ tailWord_6757737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757737).length < 2 ^ (prefixWord ++ tailWord_6757737).sum := by decide
  have hdescent : baseEnd_6757737 < baseStart_6757737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757741 : List Nat := [1, 5, 1, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_6757741 : Nat := 118140960795 + 6757741 * 2 ^ 59
def prefixEnd_6757741 : Nat := 4983230072969 + 3 ^ 40 * 6757741 * 2
def baseEnd_6757741 : Nat := 3469969271595150040959221

theorem tailTrace_6757741 : CollatzResearch.WordTrace tailWord_6757741 prefixEnd_6757741 3469969271595150040959221 := by
  unfold tailWord_6757741
  simp only [CollatzResearch.WordTrace]
  refine ⟨246475063010865962122905077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164316708673910641415270051 246475063010865962122905077)
  ·
    refine ⟨23107037157268683949022351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246475063010865962122905077 23107037157268683949022351)
    ·
      refine ⟨34660555735903025923533527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23107037157268683949022351 34660555735903025923533527)
      ·
        refine ⟨51990833603854538885300291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34660555735903025923533527 51990833603854538885300291)
        ·
          refine ⟨77986250405781808327950437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51990833603854538885300291 77986250405781808327950437)
          ·
            refine ⟨14622421951084089061490707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77986250405781808327950437 14622421951084089061490707)
            ·
              refine ⟨21933632926626133592236061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14622421951084089061490707 21933632926626133592236061)
              ·
                refine ⟨8225112347484800097088523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21933632926626133592236061 8225112347484800097088523)
                ·
                  refine ⟨12337668521227200145632785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8225112347484800097088523 12337668521227200145632785)
                  ·
                    refine ⟨9253251390920400109224589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12337668521227200145632785 9253251390920400109224589)
                    ·
                      refine ⟨3469969271595150040959221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9253251390920400109224589 3469969271595150040959221)
                      ·
                        rfl

theorem cell23_6757741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_6757741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757741 prefixEnd_6757741 := by exact prefixLift 6757741
  have htrace : WordTrace (prefixWord ++ tailWord_6757741) baseStart_6757741 baseEnd_6757741 := by
    simpa [prefixWord, tailWord_6757741, baseEnd_6757741] using wordTrace_append hprefix tailTrace_6757741
  have hstable : (prefixWord ++ tailWord_6757741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757741).length < 2 ^ (prefixWord ++ tailWord_6757741).sum := by decide
  have hdescent : baseEnd_6757741 < baseStart_6757741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757754 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3]
def baseStart_6757754 : Nat := 118140960795 + 6757754 * 2 ^ 59
def prefixEnd_6757754 : Nat := 4983230072969 + 3 ^ 40 * 6757754 * 2
def baseEnd_6757754 : Nat := 3469975946843658490096661

theorem tailTrace_6757754 : CollatzResearch.WordTrace tailWord_6757754 prefixEnd_6757754 3469975946843658490096661 := by
  unfold tailWord_6757754
  simp only [CollatzResearch.WordTrace]
  refine ⟨61618884289954716335782079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164317024773212576895418877 61618884289954716335782079)
  ·
    refine ⟨92428326434932074503673119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61618884289954716335782079 92428326434932074503673119)
    ·
      refine ⟨138642489652398111755509679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92428326434932074503673119 138642489652398111755509679)
      ·
        refine ⟨207963734478597167633264519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138642489652398111755509679 207963734478597167633264519)
        ·
          refine ⟨311945601717895751449896779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207963734478597167633264519 311945601717895751449896779)
          ·
            refine ⟨467918402576843627174845169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311945601717895751449896779 467918402576843627174845169)
            ·
              refine ⟨350938801932632720381133877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467918402576843627174845169 350938801932632720381133877)
              ·
                refine ⟨32900512681184317535731301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 350938801932632720381133877 32900512681184317535731301)
                ·
                  refine ⟨6168846127722059537949619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32900512681184317535731301 6168846127722059537949619)
                  ·
                    refine ⟨9253269191583089306924429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6168846127722059537949619 9253269191583089306924429)
                    ·
                      refine ⟨3469975946843658490096661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9253269191583089306924429 3469975946843658490096661)
                      ·
                        rfl

theorem cell23_6757754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_6757754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757754 prefixEnd_6757754 := by exact prefixLift 6757754
  have htrace : WordTrace (prefixWord ++ tailWord_6757754) baseStart_6757754 baseEnd_6757754 := by
    simpa [prefixWord, tailWord_6757754, baseEnd_6757754] using wordTrace_append hprefix tailTrace_6757754
  have hstable : (prefixWord ++ tailWord_6757754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757754).length < 2 ^ (prefixWord ++ tailWord_6757754).sum := by decide
  have hdescent : baseEnd_6757754 < baseStart_6757754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757758 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6757758 : Nat := 118140960795 + 6757758 * 2 ^ 59
def prefixEnd_6757758 : Nat := 4983230072969 + 3 ^ 40 * 6757758 * 2
def baseEnd_6757758 : Nat := 3469978000766276474446643

theorem tailTrace_6757758 : CollatzResearch.WordTrace tailWord_6757758 prefixEnd_6757758 3469978000766276474446643 := by
  unfold tailWord_6757758
  simp only [CollatzResearch.WordTrace]
  refine ⟨30809460381475546753284241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164317122034536249350849285 30809460381475546753284241)
  ·
    refine ⟨23107095286106660064963181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30809460381475546753284241 23107095286106660064963181)
    ·
      refine ⟨8665160732289997524361193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23107095286106660064963181 8665160732289997524361193)
      ·
        refine ⟨6498870549217498143270895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8665160732289997524361193 6498870549217498143270895)
        ·
          refine ⟨9748305823826247214906343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6498870549217498143270895 9748305823826247214906343)
          ·
            refine ⟨14622458735739370822359515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9748305823826247214906343 14622458735739370822359515)
            ·
              refine ⟨21933688103609056233539273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14622458735739370822359515 21933688103609056233539273)
              ·
                refine ⟨16450266077706792175154455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21933688103609056233539273 16450266077706792175154455)
                ·
                  refine ⟨24675399116560188262731683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16450266077706792175154455 24675399116560188262731683)
                  ·
                    refine ⟨37013098674840282394097525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24675399116560188262731683 37013098674840282394097525)
                    ·
                      refine ⟨3469978000766276474446643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37013098674840282394097525 3469978000766276474446643)
                      ·
                        rfl

theorem cell23_6757758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6757758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757758 prefixEnd_6757758 := by exact prefixLift 6757758
  have htrace : WordTrace (prefixWord ++ tailWord_6757758) baseStart_6757758 baseEnd_6757758 := by
    simpa [prefixWord, tailWord_6757758, baseEnd_6757758] using wordTrace_append hprefix tailTrace_6757758
  have hstable : (prefixWord ++ tailWord_6757758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757758).length < 2 ^ (prefixWord ++ tailWord_6757758).sum := by decide
  have hdescent : baseEnd_6757758 < baseStart_6757758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757778 : List Nat := [3, 2, 3, 3, 1, 2, 2, 7]
def baseStart_6757778 : Nat := 118140960795 + 6757778 * 2 ^ 59
def prefixEnd_6757778 : Nat := 4983230072969 + 3 ^ 40 * 6757778 * 2
def baseEnd_6757778 : Nat := 128518084088124681340613

theorem tailTrace_6757778 : CollatzResearch.WordTrace tailWord_6757778 prefixEnd_6757778 128518084088124681340613 := by
  unfold tailWord_6757778
  simp only [CollatzResearch.WordTrace]
  refine ⟨61619103127932979360500497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164317608341154611628001325 61619103127932979360500497)
  ·
    refine ⟨46214327345949734520375373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61619103127932979360500497 46214327345949734520375373)
    ·
      refine ⟨17330372754731150445140765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46214327345949734520375373 17330372754731150445140765)
      ·
        refine ⟨6498889783024181416927787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17330372754731150445140765 6498889783024181416927787)
        ·
          refine ⟨9748334674536272125391681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6498889783024181416927787 9748334674536272125391681)
          ·
            refine ⟨7311251005902204094043761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9748334674536272125391681 7311251005902204094043761)
            ·
              refine ⟨5483438254426653070532821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7311251005902204094043761 5483438254426653070532821)
              ·
                refine ⟨128518084088124681340613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5483438254426653070532821 128518084088124681340613)
                ·
                  rfl

theorem cell23_6757778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 7].length) (baseStart_6757778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757778 prefixEnd_6757778 := by exact prefixLift 6757778
  have htrace : WordTrace (prefixWord ++ tailWord_6757778) baseStart_6757778 baseEnd_6757778 := by
    simpa [prefixWord, tailWord_6757778, baseEnd_6757778] using wordTrace_append hprefix tailTrace_6757778
  have hstable : (prefixWord ++ tailWord_6757778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757778).length < 2 ^ (prefixWord ++ tailWord_6757778).sum := by decide
  have hdescent : baseEnd_6757778 < baseStart_6757778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757781 : List Nat := [1, 3, 2, 1, 1, 2, 3, 4, 1, 3, 2]
def baseStart_6757781 : Nat := 118140960795 + 6757781 * 2 ^ 59
def prefixEnd_6757781 : Nat := 4983230072969 + 3 ^ 40 * 6757781 * 2
def baseEnd_6757781 : Nat := 3469989810821329884459037

theorem tailTrace_6757781 : CollatzResearch.WordTrace tailWord_6757781 prefixEnd_6757781 3469989810821329884459037 := by
  unfold tailWord_6757781
  simp only [CollatzResearch.WordTrace]
  refine ⟨246476521930721048954361197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164317681287147365969574131 246476521930721048954361197)
  ·
    refine ⟨92428695724020393357885449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246476521930721048954361197 92428695724020393357885449)
    ·
      refine ⟨69321521793015295018414087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92428695724020393357885449 69321521793015295018414087)
      ·
        refine ⟨103982282689522942527621131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69321521793015295018414087 103982282689522942527621131)
        ·
          refine ⟨155973424034284413791431697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103982282689522942527621131 155973424034284413791431697)
          ·
            refine ⟨116980068025713310343573773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155973424034284413791431697 116980068025713310343573773)
            ·
              refine ⟨43867525509642491378840165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116980068025713310343573773 43867525509642491378840165)
              ·
                refine ⟨8225161033057967133532531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43867525509642491378840165 8225161033057967133532531)
                ·
                  refine ⟨12337741549586950700298797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8225161033057967133532531 12337741549586950700298797)
                  ·
                    refine ⟨4626653081095106512612049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12337741549586950700298797 4626653081095106512612049)
                    ·
                      refine ⟨3469989810821329884459037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626653081095106512612049 3469989810821329884459037)
                      ·
                        rfl

theorem cell23_6757781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_6757781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757781 prefixEnd_6757781 := by exact prefixLift 6757781
  have htrace : WordTrace (prefixWord ++ tailWord_6757781) baseStart_6757781 baseEnd_6757781 := by
    simpa [prefixWord, tailWord_6757781, baseEnd_6757781] using wordTrace_append hprefix tailTrace_6757781
  have hstable : (prefixWord ++ tailWord_6757781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757781).length < 2 ^ (prefixWord ++ tailWord_6757781).sum := by decide
  have hdescent : baseEnd_6757781 < baseStart_6757781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757807 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 4]
def baseStart_6757807 : Nat := 118140960795 + 6757807 * 2 ^ 59
def prefixEnd_6757807 : Nat := 4983230072969 + 3 ^ 40 * 6757807 * 2
def baseEnd_6757807 : Nat := 3470003161318346782733917

theorem tailTrace_6757807 : CollatzResearch.WordTrace tailWord_6757807 prefixEnd_6757807 3470003161318346782733917 := by
  unfold tailWord_6757807
  simp only [CollatzResearch.WordTrace]
  refine ⟨246477470228626855394807675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164318313485751236929871783 246477470228626855394807675)
  ·
    refine ⟨369716205342940283092211513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246477470228626855394807675 369716205342940283092211513)
    ·
      refine ⟨277287154007205212319158635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369716205342940283092211513 277287154007205212319158635)
      ·
        refine ⟨415930731010807818478737953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277287154007205212319158635 415930731010807818478737953)
        ·
          refine ⟨311948048258105863859053465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415930731010807818478737953 311948048258105863859053465)
          ·
            refine ⟨233961036193579397894290099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311948048258105863859053465 233961036193579397894290099)
            ·
              refine ⟨350941554290369096841435149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233961036193579397894290099 350941554290369096841435149)
              ·
                refine ⟨131603082858888411315538181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350941554290369096841435149 131603082858888411315538181)
                ·
                  refine ⟨24675578036041577121663409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131603082858888411315538181 24675578036041577121663409)
                  ·
                    refine ⟨18506683527031182841247557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24675578036041577121663409 18506683527031182841247557)
                    ·
                      refine ⟨3470003161318346782733917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18506683527031182841247557 3470003161318346782733917)
                      ·
                        rfl

theorem cell23_6757807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_6757807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757807 prefixEnd_6757807 := by exact prefixLift 6757807
  have htrace : WordTrace (prefixWord ++ tailWord_6757807) baseStart_6757807 baseEnd_6757807 := by
    simpa [prefixWord, tailWord_6757807, baseEnd_6757807] using wordTrace_append hprefix tailTrace_6757807
  have hstable : (prefixWord ++ tailWord_6757807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757807).length < 2 ^ (prefixWord ++ tailWord_6757807).sum := by decide
  have hdescent : baseEnd_6757807 < baseStart_6757807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757826 : List Nat := [3, 5, 2, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_6757826 : Nat := 118140960795 + 6757826 * 2 ^ 59
def prefixEnd_6757826 : Nat := 4983230072969 + 3 ^ 40 * 6757826 * 2
def baseEnd_6757826 : Nat := 3470012917450782208396331

theorem tailTrace_6757826 : CollatzResearch.WordTrace tailWord_6757826 prefixEnd_6757826 3470012917450782208396331 := by
  unfold tailWord_6757826
  simp only [CollatzResearch.WordTrace]
  refine ⟨61619540803889505409937333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164318775477038681093166221 61619540803889505409937333)
  ·
    refine ⟨5776831950364641132181625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61619540803889505409937333 5776831950364641132181625)
    ·
      refine ⟨4332623962773480849136219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5776831950364641132181625 4332623962773480849136219)
      ·
        refine ⟨6498935944160221273704329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4332623962773480849136219 6498935944160221273704329)
        ·
          refine ⟨4874201958120165955278247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6498935944160221273704329 4874201958120165955278247)
          ·
            refine ⟨7311302937180248932917371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4874201958120165955278247 7311302937180248932917371)
            ·
              refine ⟨10966954405770373399376057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7311302937180248932917371 10966954405770373399376057)
              ·
                refine ⟨8225215804327780049532043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10966954405770373399376057 8225215804327780049532043)
                ·
                  refine ⟨12337823706491670074298065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8225215804327780049532043 12337823706491670074298065)
                  ·
                    refine ⟨9253367779868752555723549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12337823706491670074298065 9253367779868752555723549)
                    ·
                      refine ⟨3470012917450782208396331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9253367779868752555723549 3470012917450782208396331)
                      ·
                        rfl

theorem cell23_6757826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_6757826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757826 prefixEnd_6757826 := by exact prefixLift 6757826
  have htrace : WordTrace (prefixWord ++ tailWord_6757826) baseStart_6757826 baseEnd_6757826 := by
    simpa [prefixWord, tailWord_6757826, baseEnd_6757826] using wordTrace_append hprefix tailTrace_6757826
  have hstable : (prefixWord ++ tailWord_6757826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757826).length < 2 ^ (prefixWord ++ tailWord_6757826).sum := by decide
  have hdescent : baseEnd_6757826 < baseStart_6757826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757847 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 1, 7]
def baseStart_6757847 : Nat := 118140960795 + 6757847 * 2 ^ 59
def prefixEnd_6757847 : Nat := 4983230072969 + 3 ^ 40 * 6757847 * 2
def baseEnd_6757847 : Nat := 1156674566848175542077911

theorem tailTrace_6757847 : CollatzResearch.WordTrace tailWord_6757847 prefixEnd_6757847 1156674566848175542077911 := by
  unfold tailWord_6757847
  simp only [CollatzResearch.WordTrace]
  refine ⟨246478929148481942226263795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164319286098987961484175863 246478929148481942226263795)
  ·
    refine ⟨369718393722722913339395693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246478929148481942226263795 369718393722722913339395693)
    ·
      refine ⟨138644397646021092502273385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369718393722722913339395693 138644397646021092502273385)
      ·
        refine ⟨103983298234515819376705039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138644397646021092502273385 103983298234515819376705039)
        ·
          refine ⟨155974947351773729065057559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103983298234515819376705039 155974947351773729065057559)
          ·
            refine ⟨233962421027660593597586339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155974947351773729065057559 233962421027660593597586339)
            ·
              refine ⟨350943631541490890396379509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233962421027660593597586339 350943631541490890396379509)
              ·
                refine ⟨32900965457014770974660579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 350943631541490890396379509 32900965457014770974660579)
                ·
                  refine ⟨49351448185522156461990869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32900965457014770974660579 49351448185522156461990869)
                  ·
                    refine ⟨1156674566848175542077911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49351448185522156461990869 1156674566848175542077911)
                    ·
                      rfl

theorem cell23_6757847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_6757847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757847 prefixEnd_6757847 := by exact prefixLift 6757847
  have htrace : WordTrace (prefixWord ++ tailWord_6757847) baseStart_6757847 baseEnd_6757847 := by
    simpa [prefixWord, tailWord_6757847, baseEnd_6757847] using wordTrace_append hprefix tailTrace_6757847
  have hstable : (prefixWord ++ tailWord_6757847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757847).length < 2 ^ (prefixWord ++ tailWord_6757847).sum := by decide
  have hdescent : baseEnd_6757847 < baseStart_6757847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757864 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 2, 5]
def baseStart_6757864 : Nat := 118140960795 + 6757864 * 2 ^ 59
def prefixEnd_6757864 : Nat := 4983230072969 + 3 ^ 40 * 6757864 * 2
def baseEnd_6757864 : Nat := 1156677476571884353240385

theorem tailTrace_6757864 : CollatzResearch.WordTrace tailWord_6757864 prefixEnd_6757864 1156677476571884353240385 := by
  unfold tailWord_6757864
  simp only [CollatzResearch.WordTrace]
  refine ⟨123239774594710177064816323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164319699459613569419755097 123239774594710177064816323)
  ·
    refine ⟨184859661892065265597224485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123239774594710177064816323 184859661892065265597224485)
    ·
      refine ⟨34661186604762237299479591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184859661892065265597224485 34661186604762237299479591)
      ·
        refine ⟨51991779907143355949219387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34661186604762237299479591 51991779907143355949219387)
        ·
          refine ⟨77987669860715033923829081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51991779907143355949219387 77987669860715033923829081)
          ·
            refine ⟨58490752395536275442871811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77987669860715033923829081 58490752395536275442871811)
            ·
              refine ⟨87736128593304413164307717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58490752395536275442871811 87736128593304413164307717)
              ·
                refine ⟨16450524111244577468307697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87736128593304413164307717 16450524111244577468307697)
                ·
                  refine ⟨12337893083433433101230773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16450524111244577468307697 12337893083433433101230773)
                  ·
                    refine ⟨1156677476571884353240385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12337893083433433101230773 1156677476571884353240385)
                    ·
                      rfl

theorem cell23_6757864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_6757864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757864 prefixEnd_6757864 := by exact prefixLift 6757864
  have htrace : WordTrace (prefixWord ++ tailWord_6757864) baseStart_6757864 baseEnd_6757864 := by
    simpa [prefixWord, tailWord_6757864, baseEnd_6757864] using wordTrace_append hprefix tailTrace_6757864
  have hstable : (prefixWord ++ tailWord_6757864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757864).length < 2 ^ (prefixWord ++ tailWord_6757864).sum := by decide
  have hdescent : baseEnd_6757864 < baseStart_6757864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757884 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_6757884 : Nat := 118140960795 + 6757884 * 2 ^ 59
def prefixEnd_6757884 : Nat := 4983230072969 + 3 ^ 40 * 6757884 * 2
def baseEnd_6757884 : Nat := 3470042699328742981471063

theorem tailTrace_6757884 : CollatzResearch.WordTrace tailWord_6757884 prefixEnd_6757884 3470042699328742981471063 := by
  unfold tailWord_6757884
  simp only [CollatzResearch.WordTrace]
  refine ⟨123240139324673948772680353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164320185766231931696907137 123240139324673948772680353)
  ·
    refine ⟨92430104493505461579510265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123240139324673948772680353 92430104493505461579510265)
    ·
      refine ⟨69322578370129096184632699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92430104493505461579510265 69322578370129096184632699)
      ·
        refine ⟨103983867555193644276949049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69322578370129096184632699 103983867555193644276949049)
        ·
          refine ⟨77987900666395233207711787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103983867555193644276949049 77987900666395233207711787)
          ·
            refine ⟨116981850999592849811567681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77987900666395233207711787 116981850999592849811567681)
            ·
              refine ⟨87736388249694637358675761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116981850999592849811567681 87736388249694637358675761)
              ·
                refine ⟨65802291187270978019006821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87736388249694637358675761 65802291187270978019006821)
                ·
                  refine ⟨12337929597613308378563779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65802291187270978019006821 12337929597613308378563779)
                  ·
                    refine ⟨18506894396419962567845669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12337929597613308378563779 18506894396419962567845669)
                    ·
                      refine ⟨3470042699328742981471063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18506894396419962567845669 3470042699328742981471063)
                      ·
                        rfl

theorem cell23_6757884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_6757884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757884 prefixEnd_6757884 := by exact prefixLift 6757884
  have htrace : WordTrace (prefixWord ++ tailWord_6757884) baseStart_6757884 baseEnd_6757884 := by
    simpa [prefixWord, tailWord_6757884, baseEnd_6757884] using wordTrace_append hprefix tailTrace_6757884
  have hstable : (prefixWord ++ tailWord_6757884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757884).length < 2 ^ (prefixWord ++ tailWord_6757884).sum := by decide
  have hdescent : baseEnd_6757884 < baseStart_6757884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757961 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 6, 3, 2]
def baseStart_6757961 : Nat := 118140960795 + 6757961 * 2 ^ 59
def prefixEnd_6757961 : Nat := 4983230072969 + 3 ^ 40 * 6757961 * 2
def baseEnd_6757961 : Nat := 3470082237339139180208209

theorem tailTrace_6757961 : CollatzResearch.WordTrace tailWord_6757961 prefixEnd_6757961 3470082237339139180208209 := by
  unfold tailWord_6757961
  simp only [CollatzResearch.WordTrace]
  refine ⟨246483087070068939695913737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164322058046712626463942491 246483087070068939695913737)
  ·
    refine ⟨184862315302551704771935303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246483087070068939695913737 184862315302551704771935303)
    ·
      refine ⟨277293472953827557157902955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184862315302551704771935303 277293472953827557157902955)
      ·
        refine ⟨415940209430741335736854433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277293472953827557157902955 415940209430741335736854433)
        ·
          refine ⟨311955157073056001802640825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415940209430741335736854433 311955157073056001802640825)
          ·
            refine ⟨233966367804792001351980619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311955157073056001802640825 233966367804792001351980619)
            ·
              refine ⟨350949551707188002027970929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233966367804792001351980619 350949551707188002027970929)
              ·
                refine ⟨263212163780391001520978197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350949551707188002027970929 263212163780391001520978197)
                ·
                  refine ⟨12338070177205828196295853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 263212163780391001520978197 12338070177205828196295853)
                  ·
                    refine ⟨4626776316452185573610945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12338070177205828196295853 4626776316452185573610945)
                    ·
                      refine ⟨3470082237339139180208209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626776316452185573610945 3470082237339139180208209)
                      ·
                        rfl

theorem cell23_6757961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 3, 2].length) (baseStart_6757961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6757961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6757961 prefixEnd_6757961 := by exact prefixLift 6757961
  have htrace : WordTrace (prefixWord ++ tailWord_6757961) baseStart_6757961 baseEnd_6757961 := by
    simpa [prefixWord, tailWord_6757961, baseEnd_6757961] using wordTrace_append hprefix tailTrace_6757961
  have hstable : (prefixWord ++ tailWord_6757961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757961).length < 2 ^ (prefixWord ++ tailWord_6757961).sum := by decide
  have hdescent : baseEnd_6757961 < baseStart_6757961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758005 : List Nat := [1, 3, 4, 2, 1, 3, 1, 2, 1, 5]
def baseStart_6758005 : Nat := 118140960795 + 6758005 * 2 ^ 59
def prefixEnd_6758005 : Nat := 4983230072969 + 3 ^ 40 * 6758005 * 2
def baseEnd_6758005 : Nat := 1156701610162645669352669

theorem tailTrace_6758005 : CollatzResearch.WordTrace tailWord_6758005 prefixEnd_6758005 1156701610162645669352669 := by
  unfold tailWord_6758005
  simp only [CollatzResearch.WordTrace]
  refine ⟨246484691881909535210515469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164323127921273023473676979 246484691881909535210515469)
  ·
    refine ⟨92431759455716075703943301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246484691881909535210515469 92431759455716075703943301)
    ·
      refine ⟨17330954897946764194489369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92431759455716075703943301 17330954897946764194489369)
      ·
        refine ⟨12998216173460073145867027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17330954897946764194489369 12998216173460073145867027)
        ·
          refine ⟨19497324260190109718800541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12998216173460073145867027 19497324260190109718800541)
          ·
            refine ⟨7311496597571291144550203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19497324260190109718800541 7311496597571291144550203)
            ·
              refine ⟨10967244896356936716825305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7311496597571291144550203 10967244896356936716825305)
              ·
                refine ⟨8225433672267702537618979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10967244896356936716825305 8225433672267702537618979)
                ·
                  refine ⟨12338150508401553806428469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8225433672267702537618979 12338150508401553806428469)
                  ·
                    refine ⟨1156701610162645669352669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12338150508401553806428469 1156701610162645669352669)
                    ·
                      rfl

theorem cell23_6758005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_6758005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758005 prefixEnd_6758005 := by exact prefixLift 6758005
  have htrace : WordTrace (prefixWord ++ tailWord_6758005) baseStart_6758005 baseEnd_6758005 := by
    simpa [prefixWord, tailWord_6758005, baseEnd_6758005] using wordTrace_append hprefix tailTrace_6758005
  have hstable : (prefixWord ++ tailWord_6758005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758005).length < 2 ^ (prefixWord ++ tailWord_6758005).sum := by decide
  have hdescent : baseEnd_6758005 < baseStart_6758005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758011 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 3]
def baseStart_6758011 : Nat := 118140960795 + 6758011 * 2 ^ 59
def prefixEnd_6758011 : Nat := 4983230072969 + 3 ^ 40 * 6758011 * 2
def baseEnd_6758011 : Nat := 3470107911371863984582979

theorem tailTrace_6758011 : CollatzResearch.WordTrace tailWord_6758011 prefixEnd_6758011 3470107911371863984582979 := by
  unfold tailWord_6758011
  simp only [CollatzResearch.WordTrace]
  refine ⟨246484910719887798235233887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164323273813258532156822591 246484910719887798235233887)
  ·
    refine ⟨369727366079831697352850831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246484910719887798235233887 369727366079831697352850831)
    ·
      refine ⟨554591049119747546029276247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369727366079831697352850831 554591049119747546029276247)
      ·
        refine ⟨831886573679621319043914371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554591049119747546029276247 831886573679621319043914371)
        ·
          refine ⟨1247829860519431978565871557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 831886573679621319043914371 1247829860519431978565871557)
          ·
            refine ⟨233968098847393495981100917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1247829860519431978565871557 233968098847393495981100917)
            ·
              refine ⟨21934509266943140248228211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 233968098847393495981100917 21934509266943140248228211)
              ·
                refine ⟨32901763900414710372342317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21934509266943140248228211 32901763900414710372342317)
                ·
                  refine ⟨12338161462655516389628369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32901763900414710372342317 12338161462655516389628369)
                  ·
                    refine ⟨9253621096991637292221277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12338161462655516389628369 9253621096991637292221277)
                    ·
                      refine ⟨3470107911371863984582979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9253621096991637292221277 3470107911371863984582979)
                      ·
                        rfl

theorem cell23_6758011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 3].length) (baseStart_6758011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758011 prefixEnd_6758011 := by exact prefixLift 6758011
  have htrace : WordTrace (prefixWord ++ tailWord_6758011) baseStart_6758011 baseEnd_6758011 := by
    simpa [prefixWord, tailWord_6758011, baseEnd_6758011] using wordTrace_append hprefix tailTrace_6758011
  have hstable : (prefixWord ++ tailWord_6758011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758011).length < 2 ^ (prefixWord ++ tailWord_6758011).sum := by decide
  have hdescent : baseEnd_6758011 < baseStart_6758011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758021 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_6758021 : Nat := 118140960795 + 6758021 * 2 ^ 59
def prefixEnd_6758021 : Nat := 4983230072969 + 3 ^ 40 * 6758021 * 2
def baseEnd_6758021 : Nat := 3470113046178408945457933

theorem tailTrace_6758021 : CollatzResearch.WordTrace tailWord_6758021 prefixEnd_6758021 3470113046178408945457933 := by
  unfold tailWord_6758021
  simp only [CollatzResearch.WordTrace]
  refine ⟨246485275449851569943097917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164323516966567713295398611 246485275449851569943097917)
  ·
    refine ⟨92431978293694338728661719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246485275449851569943097917 92431978293694338728661719)
    ·
      refine ⟨138647967440541508092992579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92431978293694338728661719 138647967440541508092992579)
      ·
        refine ⟨207971951160812262139488869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138647967440541508092992579 207971951160812262139488869)
        ·
          refine ⟨38994740842652299151154163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207971951160812262139488869 38994740842652299151154163)
          ·
            refine ⟨58492111263978448726731245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38994740842652299151154163 58492111263978448726731245)
            ·
              refine ⟨21934541723991918272524217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58492111263978448726731245 21934541723991918272524217)
              ·
                refine ⟨16450906292993938704393163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21934541723991918272524217 16450906292993938704393163)
                ·
                  refine ⟨24676359439490908056589745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16450906292993938704393163 24676359439490908056589745)
                  ·
                    refine ⟨18507269579618181042442309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24676359439490908056589745 18507269579618181042442309)
                    ·
                      refine ⟨3470113046178408945457933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18507269579618181042442309 3470113046178408945457933)
                      ·
                        rfl

theorem cell23_6758021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_6758021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758021 prefixEnd_6758021 := by exact prefixLift 6758021
  have htrace : WordTrace (prefixWord ++ tailWord_6758021) baseStart_6758021 baseEnd_6758021 := by
    simpa [prefixWord, tailWord_6758021, baseEnd_6758021] using wordTrace_append hprefix tailTrace_6758021
  have hstable : (prefixWord ++ tailWord_6758021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758021).length < 2 ^ (prefixWord ++ tailWord_6758021).sum := by decide
  have hdescent : baseEnd_6758021 < baseStart_6758021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758036 : List Nat := [2, 4, 2, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_6758036 : Nat := 118140960795 + 6758036 * 2 ^ 59
def prefixEnd_6758036 : Nat := 4983230072969 + 3 ^ 40 * 6758036 * 2
def baseEnd_6758036 : Nat := 3470120748388226386770365

theorem tailTrace_6758036 : CollatzResearch.WordTrace tailWord_6758036 prefixEnd_6758036 3470120748388226386770365 := by
  unfold tailWord_6758036
  simp only [CollatzResearch.WordTrace]
  refine ⟨123242911272398613752446981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164323881696531485003262641 123242911272398613752446981)
  ·
    refine ⟨23108045863574740078583809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123242911272398613752446981 23108045863574740078583809)
    ·
      refine ⟨17331034397681055058937857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23108045863574740078583809 17331034397681055058937857)
      ·
        refine ⟨12998275798260791294203393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17331034397681055058937857 12998275798260791294203393)
        ·
          refine ⟨9748706848695593470652545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12998275798260791294203393 9748706848695593470652545)
          ·
            refine ⟨7311530136521695102989409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9748706848695593470652545 7311530136521695102989409)
            ·
              refine ⟨5483647602391271327242057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7311530136521695102989409 5483647602391271327242057)
              ·
                refine ⟨4112735701793453495431543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5483647602391271327242057 4112735701793453495431543)
                ·
                  refine ⟨6169103552690180243147315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4112735701793453495431543 6169103552690180243147315)
                  ·
                    refine ⟨9253655329035270364720973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6169103552690180243147315 9253655329035270364720973)
                    ·
                      refine ⟨3470120748388226386770365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9253655329035270364720973 3470120748388226386770365)
                      ·
                        rfl

theorem cell23_6758036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_6758036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758036 prefixEnd_6758036 := by exact prefixLift 6758036
  have htrace : WordTrace (prefixWord ++ tailWord_6758036) baseStart_6758036 baseEnd_6758036 := by
    simpa [prefixWord, tailWord_6758036, baseEnd_6758036] using wordTrace_append hprefix tailTrace_6758036
  have hstable : (prefixWord ++ tailWord_6758036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758036).length < 2 ^ (prefixWord ++ tailWord_6758036).sum := by decide
  have hdescent : baseEnd_6758036 < baseStart_6758036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758061 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_6758061 : Nat := 118140960795 + 6758061 * 2 ^ 59
def prefixEnd_6758061 : Nat := 4983230072969 + 3 ^ 40 * 6758061 * 2
def baseEnd_6758061 : Nat := 1156711195134862929652583

theorem tailTrace_6758061 : CollatzResearch.WordTrace tailWord_6758061 prefixEnd_6758061 1156711195134862929652583 := by
  unfold tailWord_6758061
  simp only [CollatzResearch.WordTrace]
  refine ⟨246486734369706656774554037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164324489579804437849702691 246486734369706656774554037)
  ·
    refine ⟨23108131347159999072614441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246486734369706656774554037 23108131347159999072614441)
    ·
      refine ⟨17331098510369999304460831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23108131347159999072614441 17331098510369999304460831)
      ·
        refine ⟨25996647765554998956691247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17331098510369999304460831 25996647765554998956691247)
        ·
          refine ⟨38994971648332498435036871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25996647765554998956691247 38994971648332498435036871)
          ·
            refine ⟨58492457472498747652555307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38994971648332498435036871 58492457472498747652555307)
            ·
              refine ⟨87738686208748121478832961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58492457472498747652555307 87738686208748121478832961)
              ·
                refine ⟨65804014656561091109124721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87738686208748121478832961 65804014656561091109124721)
                ·
                  refine ⟨49353010992420818331843541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65804014656561091109124721 49353010992420818331843541)
                  ·
                    refine ⟨1156711195134862929652583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49353010992420818331843541 1156711195134862929652583)
                    ·
                      rfl

theorem cell23_6758061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_6758061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758061 prefixEnd_6758061 := by exact prefixLift 6758061
  have htrace : WordTrace (prefixWord ++ tailWord_6758061) baseStart_6758061 baseEnd_6758061 := by
    simpa [prefixWord, tailWord_6758061, baseEnd_6758061] using wordTrace_append hprefix tailTrace_6758061
  have hstable : (prefixWord ++ tailWord_6758061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758061).length < 2 ^ (prefixWord ++ tailWord_6758061).sum := by decide
  have hdescent : baseEnd_6758061 < baseStart_6758061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758109 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6758109 : Nat := 118140960795 + 6758109 * 2 ^ 59
def prefixEnd_6758109 : Nat := 4983230072969 + 3 ^ 40 * 6758109 * 2
def baseEnd_6758109 : Nat := 3470158232476004601157529

theorem tailTrace_6758109 : CollatzResearch.WordTrace tailWord_6758109 prefixEnd_6758109 3470158232476004601157529 := by
  unfold tailWord_6758109
  simp only [CollatzResearch.WordTrace]
  refine ⟨246488485073532760972301381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164325656715688507314867587 246488485073532760972301381)
  ·
    refine ⟨46216590951287392682306509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246488485073532760972301381 46216590951287392682306509)
    ·
      refine ⟨17331221606732772255864941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46216590951287392682306509 17331221606732772255864941)
      ·
        refine ⟨6499208102524789595949353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17331221606732772255864941 6499208102524789595949353)
        ·
          refine ⟨4874406076893592196962015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6499208102524789595949353 4874406076893592196962015)
          ·
            refine ⟨7311609115340388295443023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4874406076893592196962015 7311609115340388295443023)
            ·
              refine ⟨10967413673010582443164535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7311609115340388295443023 10967413673010582443164535)
              ·
                refine ⟨16451120509515873664746803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10967413673010582443164535 16451120509515873664746803)
                ·
                  refine ⟨24676680764273810497120205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16451120509515873664746803 24676680764273810497120205)
                  ·
                    refine ⟨9253755286602678936420077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24676680764273810497120205 9253755286602678936420077)
                    ·
                      refine ⟨3470158232476004601157529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9253755286602678936420077 3470158232476004601157529)
                      ·
                        rfl

theorem cell23_6758109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6758109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758109 prefixEnd_6758109 := by exact prefixLift 6758109
  have htrace : WordTrace (prefixWord ++ tailWord_6758109) baseStart_6758109 baseEnd_6758109 := by
    simpa [prefixWord, tailWord_6758109, baseEnd_6758109] using wordTrace_append hprefix tailTrace_6758109
  have hstable : (prefixWord ++ tailWord_6758109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758109).length < 2 ^ (prefixWord ++ tailWord_6758109).sum := by decide
  have hdescent : baseEnd_6758109 < baseStart_6758109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758111 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 4]
def baseStart_6758111 : Nat := 118140960795 + 6758111 * 2 ^ 59
def prefixEnd_6758111 : Nat := 4983230072969 + 3 ^ 40 * 6758111 * 2
def baseEnd_6758111 : Nat := 3470159259437313593332519

theorem tailTrace_6758111 : CollatzResearch.WordTrace tailWord_6758111 prefixEnd_6758111 3470159259437313593332519 := by
  unfold tailWord_6758111
  simp only [CollatzResearch.WordTrace]
  refine ⟨246488558019525515313874187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164325705346350343542582791 246488558019525515313874187)
  ·
    refine ⟨369732837029288272970811281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246488558019525515313874187 369732837029288272970811281)
    ·
      refine ⟨277299627771966204728108461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369732837029288272970811281 277299627771966204728108461)
      ·
        refine ⟨103987360414487326773040673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277299627771966204728108461 103987360414487326773040673)
        ·
          refine ⟨77990520310865495079780505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103987360414487326773040673 77990520310865495079780505)
          ·
            refine ⟨58492890233149121309835379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77990520310865495079780505 58492890233149121309835379)
            ·
              refine ⟨87739335349723681964753069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58492890233149121309835379 87739335349723681964753069)
              ·
                refine ⟨32902250756146380736782401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87739335349723681964753069 32902250756146380736782401)
                ·
                  refine ⟨24676688067109785552586801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32902250756146380736782401 24676688067109785552586801)
                  ·
                    refine ⟨18507516050332339164440101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24676688067109785552586801 18507516050332339164440101)
                    ·
                      refine ⟨3470159259437313593332519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18507516050332339164440101 3470159259437313593332519)
                      ·
                        rfl

theorem cell23_6758111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_6758111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758111 prefixEnd_6758111 := by exact prefixLift 6758111
  have htrace : WordTrace (prefixWord ++ tailWord_6758111) baseStart_6758111 baseEnd_6758111 := by
    simpa [prefixWord, tailWord_6758111, baseEnd_6758111] using wordTrace_append hprefix tailTrace_6758111
  have hstable : (prefixWord ++ tailWord_6758111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758111).length < 2 ^ (prefixWord ++ tailWord_6758111).sum := by decide
  have hdescent : baseEnd_6758111 < baseStart_6758111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758119 : List Nat := [1, 1, 5, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6758119 : Nat := 118140960795 + 6758119 * 2 ^ 59
def prefixEnd_6758119 : Nat := 4983230072969 + 3 ^ 40 * 6758119 * 2
def baseEnd_6758119 : Nat := 3470163367282549562032483

theorem tailTrace_6758119 : CollatzResearch.WordTrace tailWord_6758119 prefixEnd_6758119 3470163367282549562032483 := by
  unfold tailWord_6758119
  simp only [CollatzResearch.WordTrace]
  refine ⟨246488849803496532680165411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164325899868997688453443607 246488849803496532680165411)
  ·
    refine ⟨369733274705244799020248117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246488849803496532680165411 369733274705244799020248117)
    ·
      refine ⟨34662494503616699908148261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 369733274705244799020248117 34662494503616699908148261)
      ·
        refine ⟨6499217719428131232777799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34662494503616699908148261 6499217719428131232777799)
        ·
          refine ⟨9748826579142196849166699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6499217719428131232777799 9748826579142196849166699)
          ·
            refine ⟨14623239868713295273750049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9748826579142196849166699 14623239868713295273750049)
            ·
              refine ⟨10967429901534971455312537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14623239868713295273750049 10967429901534971455312537)
              ·
                refine ⟨8225572426151228591484403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10967429901534971455312537 8225572426151228591484403)
                ·
                  refine ⟨12338358639226842887226605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8225572426151228591484403 12338358639226842887226605)
                  ·
                    refine ⟨4626884489710066082709977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12338358639226842887226605 4626884489710066082709977)
                    ·
                      refine ⟨3470163367282549562032483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626884489710066082709977 3470163367282549562032483)
                      ·
                        rfl

theorem cell23_6758119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6758119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758119 prefixEnd_6758119 := by exact prefixLift 6758119
  have htrace : WordTrace (prefixWord ++ tailWord_6758119) baseStart_6758119 baseEnd_6758119 := by
    simpa [prefixWord, tailWord_6758119, baseEnd_6758119] using wordTrace_append hprefix tailTrace_6758119
  have hstable : (prefixWord ++ tailWord_6758119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758119).length < 2 ^ (prefixWord ++ tailWord_6758119).sum := by decide
  have hdescent : baseEnd_6758119 < baseStart_6758119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758131 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 3]
def baseStart_6758131 : Nat := 118140960795 + 6758131 * 2 ^ 59
def prefixEnd_6758131 : Nat := 4983230072969 + 3 ^ 40 * 6758131 * 2
def baseEnd_6758131 : Nat := 3470169529050403515082427

theorem tailTrace_6758131 : CollatzResearch.WordTrace tailWord_6758131 prefixEnd_6758131 3470169529050403515082427 := by
  unfold tailWord_6758131
  simp only [CollatzResearch.WordTrace]
  refine ⟨246489287479453058729602247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164326191652968705819734831 246489287479453058729602247)
  ·
    refine ⟨369733931219179588094403371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246489287479453058729602247 369733931219179588094403371)
    ·
      refine ⟨554600896828769382141605057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369733931219179588094403371 554600896828769382141605057)
      ·
        refine ⟨415950672621577036606203793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554600896828769382141605057 415950672621577036606203793)
        ·
          refine ⟨311963004466182777454652845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415950672621577036606203793 311963004466182777454652845)
          ·
            refine ⟨116986126674818541545494817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311963004466182777454652845 116986126674818541545494817)
            ·
              refine ⟨87739595006113906159121113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116986126674818541545494817 87739595006113906159121113)
              ·
                refine ⟨65804696254585429619340835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87739595006113906159121113 65804696254585429619340835)
                ·
                  refine ⟨98707044381878144429011253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65804696254585429619340835 98707044381878144429011253)
                  ·
                    refine ⟨9253785410801076040219805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98707044381878144429011253 9253785410801076040219805)
                    ·
                      refine ⟨3470169529050403515082427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9253785410801076040219805 3470169529050403515082427)
                      ·
                        rfl

theorem cell23_6758131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 3].length) (baseStart_6758131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758131 prefixEnd_6758131 := by exact prefixLift 6758131
  have htrace : WordTrace (prefixWord ++ tailWord_6758131) baseStart_6758131 baseEnd_6758131 := by
    simpa [prefixWord, tailWord_6758131, baseEnd_6758131] using wordTrace_append hprefix tailTrace_6758131
  have hstable : (prefixWord ++ tailWord_6758131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758131).length < 2 ^ (prefixWord ++ tailWord_6758131).sum := by decide
  have hdescent : baseEnd_6758131 < baseStart_6758131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758188 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_6758188 : Nat := 118140960795 + 6758188 * 2 ^ 59
def prefixEnd_6758188 : Nat := 4983230072969 + 3 ^ 40 * 6758188 * 2
def baseEnd_6758188 : Nat := 3470198797447709792069665

theorem tailTrace_6758188 : CollatzResearch.WordTrace tailWord_6758188 prefixEnd_6758188 3470198797447709792069665 := by
  unfold tailWord_6758188
  simp only [CollatzResearch.WordTrace]
  refine ⟨123245683220123278732213609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164327577626831038309618145 123245683220123278732213609)
  ·
    refine ⟨92434262415092459049160207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123245683220123278732213609 92434262415092459049160207)
    ·
      refine ⟨138651393622638688573740311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92434262415092459049160207 138651393622638688573740311)
      ·
        refine ⟨207977090433958032860610467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138651393622638688573740311 207977090433958032860610467)
        ·
          refine ⟨311965635650937049290915701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207977090433958032860610467 311965635650937049290915701)
          ·
            refine ⟨29246778342275348371023347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 311965635650937049290915701 29246778342275348371023347)
            ·
              refine ⟨43870167513413022556535021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29246778342275348371023347 43870167513413022556535021)
              ·
                refine ⟨16451312817529883458700633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43870167513413022556535021 16451312817529883458700633)
                ·
                  refine ⟨12338484613147412594025475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16451312817529883458700633 12338484613147412594025475)
                  ·
                    refine ⟨18507726919721118891038213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12338484613147412594025475 18507726919721118891038213)
                    ·
                      refine ⟨3470198797447709792069665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18507726919721118891038213 3470198797447709792069665)
                      ·
                        rfl

theorem cell23_6758188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_6758188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758188 prefixEnd_6758188 := by exact prefixLift 6758188
  have htrace : WordTrace (prefixWord ++ tailWord_6758188) baseStart_6758188 baseEnd_6758188 := by
    simpa [prefixWord, tailWord_6758188, baseEnd_6758188] using wordTrace_append hprefix tailTrace_6758188
  have hstable : (prefixWord ++ tailWord_6758188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758188).length < 2 ^ (prefixWord ++ tailWord_6758188).sum := by decide
  have hdescent : baseEnd_6758188 < baseStart_6758188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758205 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_6758205 : Nat := 118140960795 + 6758205 * 2 ^ 59
def prefixEnd_6758205 : Nat := 4983230072969 + 3 ^ 40 * 6758205 * 2
def baseEnd_6758205 : Nat := 3470207526618836225557087

theorem tailTrace_6758205 : CollatzResearch.WordTrace tailWord_6758205 prefixEnd_6758205 3470207526618836225557087 := by
  unfold tailWord_6758205
  simp only [CollatzResearch.WordTrace]
  refine ⟨246491986481184969367796069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164327990987456646245197379 246491986481184969367796069)
  ·
    refine ⟨46217247465222181756461763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246491986481184969367796069 46217247465222181756461763)
    ·
      refine ⟨69325871197833272634692645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46217247465222181756461763 69325871197833272634692645)
      ·
        refine ⟨12998600849593738619004871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69325871197833272634692645 12998600849593738619004871)
        ·
          refine ⟨19497901274390607928507307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12998600849593738619004871 19497901274390607928507307)
          ·
            refine ⟨29246851911585911892760961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19497901274390607928507307 29246851911585911892760961)
            ·
              refine ⟨21935138933689433919570721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29246851911585911892760961 21935138933689433919570721)
              ·
                refine ⟨16451354200267075439678041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21935138933689433919570721 16451354200267075439678041)
                ·
                  refine ⟨12338515650200306579758531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16451354200267075439678041 12338515650200306579758531)
                  ·
                    refine ⟨18507773475300459869637797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12338515650200306579758531 18507773475300459869637797)
                    ·
                      refine ⟨3470207526618836225557087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18507773475300459869637797 3470207526618836225557087)
                      ·
                        rfl

theorem cell23_6758205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_6758205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758205 prefixEnd_6758205 := by exact prefixLift 6758205
  have htrace : WordTrace (prefixWord ++ tailWord_6758205) baseStart_6758205 baseEnd_6758205 := by
    simpa [prefixWord, tailWord_6758205, baseEnd_6758205] using wordTrace_append hprefix tailTrace_6758205
  have hstable : (prefixWord ++ tailWord_6758205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758205).length < 2 ^ (prefixWord ++ tailWord_6758205).sum := by decide
  have hdescent : baseEnd_6758205 < baseStart_6758205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758242 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_6758242 : Nat := 118140960795 + 6758242 * 2 ^ 59
def prefixEnd_6758242 : Nat := 4983230072969 + 3 ^ 40 * 6758242 * 2
def baseEnd_6758242 : Nat := 3470226525403052580794417

theorem tailTrace_6758242 : CollatzResearch.WordTrace tailWord_6758242 prefixEnd_6758242 3470226525403052580794417 := by
  unfold tailWord_6758242
  simp only [CollatzResearch.WordTrace]
  refine ⟨61623333995512731171723245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164328890654700616457928653 61623333995512731171723245)
  ·
    refine ⟨23108750248317274189396217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61623333995512731171723245 23108750248317274189396217)
    ·
      refine ⟨17331562686237955642047163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23108750248317274189396217 17331562686237955642047163)
      ·
        refine ⟨25997344029356933463070745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17331562686237955642047163 25997344029356933463070745)
        ·
          refine ⟨19498008022017700097303059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25997344029356933463070745 19498008022017700097303059)
          ·
            refine ⟨29247012033026550145954589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19498008022017700097303059 29247012033026550145954589)
            ·
              refine ⟨10967629512384956304732971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29247012033026550145954589 10967629512384956304732971)
              ·
                refine ⟨16451444268577434457099457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10967629512384956304732971 16451444268577434457099457)
                ·
                  refine ⟨12338583201433075842824593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16451444268577434457099457 12338583201433075842824593)
                  ·
                    refine ⟨9253937401074806882118445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12338583201433075842824593 9253937401074806882118445)
                    ·
                      refine ⟨3470226525403052580794417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9253937401074806882118445 3470226525403052580794417)
                      ·
                        rfl

theorem cell23_6758242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_6758242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758242 prefixEnd_6758242 := by exact prefixLift 6758242
  have htrace : WordTrace (prefixWord ++ tailWord_6758242) baseStart_6758242 baseEnd_6758242 := by
    simpa [prefixWord, tailWord_6758242, baseEnd_6758242] using wordTrace_append hprefix tailTrace_6758242
  have hstable : (prefixWord ++ tailWord_6758242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758242).length < 2 ^ (prefixWord ++ tailWord_6758242).sum := by decide
  have hdescent : baseEnd_6758242 < baseStart_6758242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758251 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 5]
def baseStart_6758251 : Nat := 118140960795 + 6758251 * 2 ^ 59
def prefixEnd_6758251 : Nat := 4983230072969 + 3 ^ 40 * 6758251 * 2
def baseEnd_6758251 : Nat := 3470231146728943045581875

theorem tailTrace_6758251 : CollatzResearch.WordTrace tailWord_6758251 prefixEnd_6758251 3470231146728943045581875 := by
  unfold tailWord_6758251
  simp only [CollatzResearch.WordTrace]
  refine ⟨246493664239018319223970607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164329109492678879482647071 246493664239018319223970607)
  ·
    refine ⟨369740496358527478835955911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246493664239018319223970607 369740496358527478835955911)
    ·
      refine ⟨554610744537791218253933867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369740496358527478835955911 554610744537791218253933867)
      ·
        refine ⟨831916116806686827380900801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554610744537791218253933867 831916116806686827380900801)
        ·
          refine ⟨623937087605015120535675601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831916116806686827380900801 623937087605015120535675601)
          ·
            refine ⟨467952815703761340401756701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623937087605015120535675601 467952815703761340401756701)
            ·
              refine ⟨175482305888910502650658763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 467952815703761340401756701 175482305888910502650658763)
              ·
                refine ⟨263223458833365753975988145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175482305888910502650658763 263223458833365753975988145)
                ·
                  refine ⟨197417594125024315481991109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263223458833365753975988145 197417594125024315481991109)
                  ·
                    refine ⟨37015798898442059152873333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 197417594125024315481991109 37015798898442059152873333)
                    ·
                      refine ⟨3470231146728943045581875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37015798898442059152873333 3470231146728943045581875)
                      ·
                        rfl

theorem cell23_6758251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 5].length) (baseStart_6758251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758251 prefixEnd_6758251 := by exact prefixLift 6758251
  have htrace : WordTrace (prefixWord ++ tailWord_6758251) baseStart_6758251 baseEnd_6758251 := by
    simpa [prefixWord, tailWord_6758251, baseEnd_6758251] using wordTrace_append hprefix tailTrace_6758251
  have hstable : (prefixWord ++ tailWord_6758251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758251).length < 2 ^ (prefixWord ++ tailWord_6758251).sum := by decide
  have hdescent : baseEnd_6758251 < baseStart_6758251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758265 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 4, 3, 2]
def baseStart_6758265 : Nat := 118140960795 + 6758265 * 2 ^ 59
def prefixEnd_6758265 : Nat := 4983230072969 + 3 ^ 40 * 6758265 * 2
def baseEnd_6758265 : Nat := 3470238335458105990806811

theorem tailTrace_6758265 : CollatzResearch.WordTrace tailWord_6758265 prefixEnd_6758265 3470238335458105990806811 := by
  unfold tailWord_6758265
  simp only [CollatzResearch.WordTrace]
  refine ⟨246494174860967599614980249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164329449907311733076653499 246494174860967599614980249)
  ·
    refine ⟨184870631145725699711235187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246494174860967599614980249 184870631145725699711235187)
    ·
      refine ⟨277305946718588549566852781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184870631145725699711235187 277305946718588549566852781)
      ·
        refine ⟨103989730019470706087569793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277305946718588549566852781 103989730019470706087569793)
        ·
          refine ⟨77992297514603029565677345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103989730019470706087569793 77992297514603029565677345)
          ·
            refine ⟨58494223135952272174258009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77992297514603029565677345 58494223135952272174258009)
            ·
              refine ⟨43870667351964204130693507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58494223135952272174258009 43870667351964204130693507)
              ·
                refine ⟨65806001027946306196040261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43870667351964204130693507 65806001027946306196040261)
                ·
                  refine ⟨12338625192739932411757549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65806001027946306196040261 12338625192739932411757549)
                  ·
                    refine ⟨4626984447277474654409081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12338625192739932411757549 4626984447277474654409081)
                    ·
                      refine ⟨3470238335458105990806811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4626984447277474654409081 3470238335458105990806811)
                      ·
                        rfl

theorem cell23_6758265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_6758265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758265 prefixEnd_6758265 := by exact prefixLift 6758265
  have htrace : WordTrace (prefixWord ++ tailWord_6758265) baseStart_6758265 baseEnd_6758265 := by
    simpa [prefixWord, tailWord_6758265, baseEnd_6758265] using wordTrace_append hprefix tailTrace_6758265
  have hstable : (prefixWord ++ tailWord_6758265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758265).length < 2 ^ (prefixWord ++ tailWord_6758265).sum := by decide
  have hdescent : baseEnd_6758265 < baseStart_6758265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758272 : List Nat := [2, 1, 1, 2, 1, 2, 3, 6, 1, 1, 3]
def baseStart_6758272 : Nat := 118140960795 + 6758272 * 2 ^ 59
def prefixEnd_6758272 : Nat := 4983230072969 + 3 ^ 40 * 6758272 * 2
def baseEnd_6758272 : Nat := 3470241929822687463419279

theorem tailTrace_6758272 : CollatzResearch.WordTrace tailWord_6758272 prefixEnd_6758272 3470241929822687463419279 := by
  unfold tailWord_6758272
  simp only [CollatzResearch.WordTrace]
  refine ⟨123247215085971119905242535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164329620114628159873656713 123247215085971119905242535)
  ·
    refine ⟨184870822628956679857863803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123247215085971119905242535 184870822628956679857863803)
    ·
      refine ⟨277306233943435019786795705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184870822628956679857863803 277306233943435019786795705)
      ·
        refine ⟨207979675457576264840096779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277306233943435019786795705 207979675457576264840096779)
        ·
          refine ⟨311969513186364397260145169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207979675457576264840096779 311969513186364397260145169)
          ·
            refine ⟨233977134889773297945108877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311969513186364397260145169 233977134889773297945108877)
            ·
              refine ⟨87741425583664986729415829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233977134889773297945108877 87741425583664986729415829)
              ·
                refine ⟨4112879324234296252941367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87741425583664986729415829 4112879324234296252941367)
                ·
                  refine ⟨6169318986351444379412051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4112879324234296252941367 6169318986351444379412051)
                  ·
                    refine ⟨9253978479527166569118077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6169318986351444379412051 9253978479527166569118077)
                    ·
                      refine ⟨3470241929822687463419279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9253978479527166569118077 3470241929822687463419279)
                      ·
                        rfl

theorem cell23_6758272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 1, 1, 3].length) (baseStart_6758272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758272 prefixEnd_6758272 := by exact prefixLift 6758272
  have htrace : WordTrace (prefixWord ++ tailWord_6758272) baseStart_6758272 baseEnd_6758272 := by
    simpa [prefixWord, tailWord_6758272, baseEnd_6758272] using wordTrace_append hprefix tailTrace_6758272
  have hstable : (prefixWord ++ tailWord_6758272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758272).length < 2 ^ (prefixWord ++ tailWord_6758272).sum := by decide
  have hdescent : baseEnd_6758272 < baseStart_6758272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758288 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 6, 4]
def baseStart_6758288 : Nat := 118140960795 + 6758288 * 2 ^ 59
def prefixEnd_6758288 : Nat := 4983230072969 + 3 ^ 40 * 6758288 * 2
def baseEnd_6758288 : Nat := 1156750048504386466939735

theorem tailTrace_6758288 : CollatzResearch.WordTrace tailWord_6758288 prefixEnd_6758288 1156750048504386466939735 := by
  unfold tailWord_6758288
  simp only [CollatzResearch.WordTrace]
  refine ⟨123247506869942137271533759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164330009159922849695378345 123247506869942137271533759)
  ·
    refine ⟨184871260304913205907300639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123247506869942137271533759 184871260304913205907300639)
    ·
      refine ⟨277306890457369808860950959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184871260304913205907300639 277306890457369808860950959)
      ·
        refine ⟨415960335686054713291426439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277306890457369808860950959 415960335686054713291426439)
        ·
          refine ⟨623940503529082069937139659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415960335686054713291426439 623940503529082069937139659)
          ·
            refine ⟨935910755293623104905709489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623940503529082069937139659 935910755293623104905709489)
            ·
              refine ⟨701933066470217328679282117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935910755293623104905709489 701933066470217328679282117)
              ·
                refine ⟨131612449963165749127365397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 701933066470217328679282117 131612449963165749127365397)
                ·
                  refine ⟨6169333592023394490345253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131612449963165749127365397 6169333592023394490345253)
                  ·
                    refine ⟨1156750048504386466939735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6169333592023394490345253 1156750048504386466939735)
                    ·
                      rfl

theorem cell23_6758288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 6, 4].length) (baseStart_6758288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758288 prefixEnd_6758288 := by exact prefixLift 6758288
  have htrace : WordTrace (prefixWord ++ tailWord_6758288) baseStart_6758288 baseEnd_6758288 := by
    simpa [prefixWord, tailWord_6758288, baseEnd_6758288] using wordTrace_append hprefix tailTrace_6758288
  have hstable : (prefixWord ++ tailWord_6758288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758288).length < 2 ^ (prefixWord ++ tailWord_6758288).sum := by decide
  have hdescent : baseEnd_6758288 < baseStart_6758288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758292 : List Nat := [2, 4, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_6758292 : Nat := 118140960795 + 6758292 * 2 ^ 59
def prefixEnd_6758292 : Nat := 4983230072969 + 3 ^ 40 * 6758292 * 2
def baseEnd_6758292 : Nat := 1156750733145259128389729

theorem tailTrace_6758292 : CollatzResearch.WordTrace tailWord_6758292 prefixEnd_6758292 1156750733145259128389729 := by
  unfold tailWord_6758292
  simp only [CollatzResearch.WordTrace]
  refine ⟨123247579815934891613106565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164330106421246522150808753 123247579815934891613106565)
  ·
    refine ⟨23108921215487792177457481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123247579815934891613106565 23108921215487792177457481)
    ·
      refine ⟨17331690911615844133093111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23108921215487792177457481 17331690911615844133093111)
      ·
        refine ⟨25997536367423766199639667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17331690911615844133093111 25997536367423766199639667)
        ·
          refine ⟨38996304551135649299459501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25997536367423766199639667 38996304551135649299459501)
          ·
            refine ⟨14623614206675868487297313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38996304551135649299459501 14623614206675868487297313)
            ·
              refine ⟨10967710655006901365472985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14623614206675868487297313 10967710655006901365472985)
              ·
                refine ⟨8225782991255176024104739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10967710655006901365472985 8225782991255176024104739)
                ·
                  refine ⟨12338674486882764036157109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8225782991255176024104739 12338674486882764036157109)
                  ·
                    refine ⟨1156750733145259128389729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12338674486882764036157109 1156750733145259128389729)
                    ·
                      rfl

theorem cell23_6758292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_6758292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758292 prefixEnd_6758292 := by exact prefixLift 6758292
  have htrace : WordTrace (prefixWord ++ tailWord_6758292) baseStart_6758292 baseEnd_6758292 := by
    simpa [prefixWord, tailWord_6758292, baseEnd_6758292] using wordTrace_append hprefix tailTrace_6758292
  have hstable : (prefixWord ++ tailWord_6758292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758292).length < 2 ^ (prefixWord ++ tailWord_6758292).sum := by decide
  have hdescent : baseEnd_6758292 < baseStart_6758292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758295 : List Nat := [1, 1, 3, 3, 1, 3, 1, 4, 1, 1, 4]
def baseStart_6758295 : Nat := 118140960795 + 6758295 * 2 ^ 59
def prefixEnd_6758295 : Nat := 4983230072969 + 3 ^ 40 * 6758295 * 2
def baseEnd_6758295 : Nat := 3470253739877740873431673

theorem tailTrace_6758295 : CollatzResearch.WordTrace tailWord_6758295 prefixEnd_6758295 3470253739877740873431673 := by
  unfold tailWord_6758295
  simp only [CollatzResearch.WordTrace]
  refine ⟨246495269050858914738572339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164330179367239276492381559 246495269050858914738572339)
  ·
    refine ⟨369742903576288372107858509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246495269050858914738572339 369742903576288372107858509)
    ·
      refine ⟨138653588841108139540446941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369742903576288372107858509 138653588841108139540446941)
      ·
        refine ⟨51995095815415552327667603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138653588841108139540446941 51995095815415552327667603)
        ·
          refine ⟨77992643723123328491501405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51995095815415552327667603 77992643723123328491501405)
          ·
            refine ⟨29247241396171248184313027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77992643723123328491501405 29247241396171248184313027)
            ·
              refine ⟨43870862094256872276469541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29247241396171248184313027 43870862094256872276469541)
              ·
                refine ⟨8225786642673163551838039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43870862094256872276469541 8225786642673163551838039)
                ·
                  refine ⟨12338679964009745327757059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8225786642673163551838039 12338679964009745327757059)
                  ·
                    refine ⟨18508019946014617991635589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12338679964009745327757059 18508019946014617991635589)
                    ·
                      refine ⟨3470253739877740873431673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18508019946014617991635589 3470253739877740873431673)
                      ·
                        rfl

theorem cell23_6758295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_6758295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758295 prefixEnd_6758295 := by exact prefixLift 6758295
  have htrace : WordTrace (prefixWord ++ tailWord_6758295) baseStart_6758295 baseEnd_6758295 := by
    simpa [prefixWord, tailWord_6758295, baseEnd_6758295] using wordTrace_append hprefix tailTrace_6758295
  have hstable : (prefixWord ++ tailWord_6758295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758295).length < 2 ^ (prefixWord ++ tailWord_6758295).sum := by decide
  have hdescent : baseEnd_6758295 < baseStart_6758295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758362 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3]
def baseStart_6758362 : Nat := 118140960795 + 6758362 * 2 ^ 59
def prefixEnd_6758362 : Nat := 4983230072969 + 3 ^ 40 * 6758362 * 2
def baseEnd_6758362 : Nat := 3470288143081592111293865

theorem tailTrace_6758362 : CollatzResearch.WordTrace tailWord_6758362 prefixEnd_6758362 3470288143081592111293865 := by
  unfold tailWord_6758362
  simp only [CollatzResearch.WordTrace]
  refine ⟨61624428185404046295315335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164331808494410790120840893 61624428185404046295315335)
  ·
    refine ⟨92436642278106069442973003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61624428185404046295315335 92436642278106069442973003)
    ·
      refine ⟨138654963417159104164459505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92436642278106069442973003 138654963417159104164459505)
      ·
        refine ⟨103991222562869328123344629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138654963417159104164459505 103991222562869328123344629)
        ·
          refine ⟨9749177115268999511563559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103991222562869328123344629 9749177115268999511563559)
          ·
            refine ⟨14623765672903499267345339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9749177115268999511563559 14623765672903499267345339)
            ·
              refine ⟨21935648509355248901018009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14623765672903499267345339 21935648509355248901018009)
              ·
                refine ⟨16451736382016436675763507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21935648509355248901018009 16451736382016436675763507)
                ·
                  refine ⟨24677604573024655013645261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16451736382016436675763507 24677604573024655013645261)
                  ·
                    refine ⟨9254101714884245630116973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24677604573024655013645261 9254101714884245630116973)
                    ·
                      refine ⟨3470288143081592111293865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9254101714884245630116973 3470288143081592111293865)
                      ·
                        rfl

theorem cell23_6758362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_6758362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758362 prefixEnd_6758362 := by exact prefixLift 6758362
  have htrace : WordTrace (prefixWord ++ tailWord_6758362) baseStart_6758362 baseEnd_6758362 := by
    simpa [prefixWord, tailWord_6758362, baseEnd_6758362] using wordTrace_append hprefix tailTrace_6758362
  have hstable : (prefixWord ++ tailWord_6758362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758362).length < 2 ^ (prefixWord ++ tailWord_6758362).sum := by decide
  have hdescent : baseEnd_6758362 < baseStart_6758362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758368 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 4]
def baseStart_6758368 : Nat := 118140960795 + 6758368 * 2 ^ 59
def prefixEnd_6758368 : Nat := 4983230072969 + 3 ^ 40 * 6758368 * 2
def baseEnd_6758368 : Nat := 3470291223965519087818837

theorem tailTrace_6758368 : CollatzResearch.WordTrace tailWord_6758368 prefixEnd_6758368 3470291223965519087818837 := by
  unfold tailWord_6758368
  simp only [CollatzResearch.WordTrace]
  refine ⟨123248965789797224102989879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164331954386396298803986505 123248965789797224102989879)
  ·
    refine ⟨184873448684695836154484819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123248965789797224102989879 184873448684695836154484819)
    ·
      refine ⟨277310173027043754231727229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184873448684695836154484819 277310173027043754231727229)
      ·
        refine ⟨103991314885141407836897711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277310173027043754231727229 103991314885141407836897711)
        ·
          refine ⟨155986972327712111755346567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103991314885141407836897711 155986972327712111755346567)
          ·
            refine ⟨233980458491568167633019851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155986972327712111755346567 233980458491568167633019851)
            ·
              refine ⟨350970687737352251449529777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233980458491568167633019851 350970687737352251449529777)
              ·
                refine ⟨263228015803014188587147333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350970687737352251449529777 263228015803014188587147333)
                ·
                  refine ⟨49355252963065160360090125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263228015803014188587147333 49355252963065160360090125)
                  ·
                    refine ⟨18508219861149435135033797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49355252963065160360090125 18508219861149435135033797)
                    ·
                      refine ⟨3470291223965519087818837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18508219861149435135033797 3470291223965519087818837)
                      ·
                        rfl

theorem cell23_6758368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_6758368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758368 prefixEnd_6758368 := by exact prefixLift 6758368
  have htrace : WordTrace (prefixWord ++ tailWord_6758368) baseStart_6758368 baseEnd_6758368 := by
    simpa [prefixWord, tailWord_6758368, baseEnd_6758368] using wordTrace_append hprefix tailTrace_6758368
  have hstable : (prefixWord ++ tailWord_6758368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758368).length < 2 ^ (prefixWord ++ tailWord_6758368).sum := by decide
  have hdescent : baseEnd_6758368 < baseStart_6758368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758423 : List Nat := [1, 1, 3, 5, 2, 2, 2, 1, 1, 3, 2]
def baseStart_6758423 : Nat := 118140960795 + 6758423 * 2 ^ 59
def prefixEnd_6758423 : Nat := 4983230072969 + 3 ^ 40 * 6758423 * 2
def baseEnd_6758423 : Nat := 3470319465401516372631085

theorem tailTrace_6758423 : CollatzResearch.WordTrace tailWord_6758423 prefixEnd_6758423 3470319465401516372631085 := by
  unfold tailWord_6758423
  simp only [CollatzResearch.WordTrace]
  refine ⟨246499937594395192599231923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164333291729596795066154615 246499937594395192599231923)
  ·
    refine ⟨369749906391592788898847885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246499937594395192599231923 369749906391592788898847885)
    ·
      refine ⟨138656214896847295837067957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369749906391592788898847885 138656214896847295837067957)
      ·
        refine ⟨12999020146579433984725121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138656214896847295837067957 12999020146579433984725121)
        ·
          refine ⟨9749265109934575488543841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12999020146579433984725121 9749265109934575488543841)
          ·
            refine ⟨7311948832450931616407881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9749265109934575488543841 7311948832450931616407881)
            ·
              refine ⟨5483961624338198712305911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7311948832450931616407881 5483961624338198712305911)
              ·
                refine ⟨8225942436507298068458867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5483961624338198712305911 8225942436507298068458867)
                ·
                  refine ⟨12338913654760947102688301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8225942436507298068458867 12338913654760947102688301)
                  ·
                    refine ⟨4627092620535355163508113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12338913654760947102688301 4627092620535355163508113)
                    ·
                      refine ⟨3470319465401516372631085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627092620535355163508113 3470319465401516372631085)
                      ·
                        rfl

theorem cell23_6758423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_6758423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758423 prefixEnd_6758423 := by exact prefixLift 6758423
  have htrace : WordTrace (prefixWord ++ tailWord_6758423) baseStart_6758423 baseEnd_6758423 := by
    simpa [prefixWord, tailWord_6758423, baseEnd_6758423] using wordTrace_append hprefix tailTrace_6758423
  have hstable : (prefixWord ++ tailWord_6758423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758423).length < 2 ^ (prefixWord ++ tailWord_6758423).sum := by decide
  have hdescent : baseEnd_6758423 < baseStart_6758423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758435 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 3]
def baseStart_6758435 : Nat := 118140960795 + 6758435 * 2 ^ 59
def prefixEnd_6758435 : Nat := 4983230072969 + 3 ^ 40 * 6758435 * 2
def baseEnd_6758435 : Nat := 3470325627169370325681029

theorem tailTrace_6758435 : CollatzResearch.WordTrace tailWord_6758435 prefixEnd_6758435 3470325627169370325681029 := by
  unfold tailWord_6758435
  simp only [CollatzResearch.WordTrace]
  refine ⟨246500375270351718648668759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164333583513567812432445839 246500375270351718648668759)
  ·
    refine ⟨369750562905527577973003139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246500375270351718648668759 369750562905527577973003139)
    ·
      refine ⟨554625844358291366959504709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369750562905527577973003139 554625844358291366959504709)
      ·
        refine ⟨103992345817179631304907133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 554625844358291366959504709 103992345817179631304907133)
        ·
          refine ⟨38997129681442361739340175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103992345817179631304907133 38997129681442361739340175)
          ·
            refine ⟨58495694522163542609010263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38997129681442361739340175 58495694522163542609010263)
            ·
              refine ⟨87743541783245313913515395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58495694522163542609010263 87743541783245313913515395)
              ·
                refine ⟨131615312674867970870273093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87743541783245313913515395 131615312674867970870273093)
                ·
                  refine ⟨24677871126537744538176205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131615312674867970870273093 24677871126537744538176205)
                  ·
                    refine ⟨9254201672451654201816077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24677871126537744538176205 9254201672451654201816077)
                    ·
                      refine ⟨3470325627169370325681029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9254201672451654201816077 3470325627169370325681029)
                      ·
                        rfl

theorem cell23_6758435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_6758435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758435 prefixEnd_6758435 := by exact prefixLift 6758435
  have htrace : WordTrace (prefixWord ++ tailWord_6758435) baseStart_6758435 baseEnd_6758435 := by
    simpa [prefixWord, tailWord_6758435, baseEnd_6758435] using wordTrace_append hprefix tailTrace_6758435
  have hstable : (prefixWord ++ tailWord_6758435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758435).length < 2 ^ (prefixWord ++ tailWord_6758435).sum := by decide
  have hdescent : baseEnd_6758435 < baseStart_6758435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758436 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 4, 2, 2]
def baseStart_6758436 : Nat := 118140960795 + 6758436 * 2 ^ 59
def prefixEnd_6758436 : Nat := 4983230072969 + 3 ^ 40 * 6758436 * 2
def baseEnd_6758436 : Nat := 3470326140650024821768525

theorem tailTrace_6758436 : CollatzResearch.WordTrace tailWord_6758436 prefixEnd_6758436 3470326140650024821768525 := by
  unfold tailWord_6758436
  simp only [CollatzResearch.WordTrace]
  refine ⟨123250205871674047909727581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164333607828898730546303441 123250205871674047909727581)
  ·
    refine ⟨46218827201877767966147843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123250205871674047909727581 46218827201877767966147843)
    ·
      refine ⟨69328240802816651949221765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46218827201877767966147843 69328240802816651949221765)
      ·
        refine ⟨12999045150528122240479081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69328240802816651949221765 12999045150528122240479081)
        ·
          refine ⟨9749283862896091680359311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12999045150528122240479081 9749283862896091680359311)
          ·
            refine ⟨14623925794344137520538967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9749283862896091680359311 14623925794344137520538967)
            ·
              refine ⟨21935888691516206280808451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14623925794344137520538967 21935888691516206280808451)
              ·
                refine ⟨32903833037274309421212677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21935888691516206280808451 32903833037274309421212677)
                ·
                  refine ⟨6169468694488933016477377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32903833037274309421212677 6169468694488933016477377)
                  ·
                    refine ⟨4627101520866699762358033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6169468694488933016477377 4627101520866699762358033)
                    ·
                      refine ⟨3470326140650024821768525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627101520866699762358033 3470326140650024821768525)
                      ·
                        rfl

theorem cell23_6758436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_6758436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758436 prefixEnd_6758436 := by exact prefixLift 6758436
  have htrace : WordTrace (prefixWord ++ tailWord_6758436) baseStart_6758436 baseEnd_6758436 := by
    simpa [prefixWord, tailWord_6758436, baseEnd_6758436] using wordTrace_append hprefix tailTrace_6758436
  have hstable : (prefixWord ++ tailWord_6758436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758436).length < 2 ^ (prefixWord ++ tailWord_6758436).sum := by decide
  have hdescent : baseEnd_6758436 < baseStart_6758436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758442 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 7]
def baseStart_6758442 : Nat := 118140960795 + 6758442 * 2 ^ 59
def prefixEnd_6758442 : Nat := 4983230072969 + 3 ^ 40 * 6758442 * 2
def baseEnd_6758442 : Nat := 385592135725994644254833

theorem tailTrace_6758442 : CollatzResearch.WordTrace tailWord_6758442 prefixEnd_6758442 385592135725994644254833 := by
  unfold tailWord_6758442
  simp only [CollatzResearch.WordTrace]
  refine ⟨61625157645331589711043395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164333753720884239229449053 61625157645331589711043395)
  ·
    refine ⟨92437736467997384566565093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61625157645331589711043395 92437736467997384566565093)
    ·
      refine ⟨17332075587749509606230955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92437736467997384566565093 17332075587749509606230955)
      ·
        refine ⟨25998113381624264409346433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17332075587749509606230955 25998113381624264409346433)
        ·
          refine ⟨19498585036218198307009825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25998113381624264409346433 19498585036218198307009825)
          ·
            refine ⟨14623938777163648730257369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19498585036218198307009825 14623938777163648730257369)
            ·
              refine ⟨10967954082872736547693027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14623938777163648730257369 10967954082872736547693027)
              ·
                refine ⟨16451931124309104821539541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10967954082872736547693027 16451931124309104821539541)
                ·
                  refine ⟨385592135725994644254833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16451931124309104821539541 385592135725994644254833)
                  ·
                    rfl

theorem cell23_6758442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_6758442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758442 prefixEnd_6758442 := by exact prefixLift 6758442
  have htrace : WordTrace (prefixWord ++ tailWord_6758442) baseStart_6758442 baseEnd_6758442 := by
    simpa [prefixWord, tailWord_6758442, baseEnd_6758442] using wordTrace_append hprefix tailTrace_6758442
  have hstable : (prefixWord ++ tailWord_6758442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758442).length < 2 ^ (prefixWord ++ tailWord_6758442).sum := by decide
  have hdescent : baseEnd_6758442 < baseStart_6758442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758492 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_6758492 : Nat := 118140960795 + 6758492 * 2 ^ 59
def prefixEnd_6758492 : Nat := 4983230072969 + 3 ^ 40 * 6758492 * 2
def baseEnd_6758492 : Nat := 3470354895566676602668267

theorem tailTrace_6758492 : CollatzResearch.WordTrace tailWord_6758492 prefixEnd_6758492 3470354895566676602668267 := by
  unfold tailWord_6758492
  simp only [CollatzResearch.WordTrace]
  refine ⟨123251227115572608691746865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164334969487430144922329153 123251227115572608691746865)
  ·
    refine ⟨92438420336679456518810149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123251227115572608691746865 92438420336679456518810149)
    ·
      refine ⟨17332203813127398097276903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92438420336679456518810149 17332203813127398097276903)
      ·
        refine ⟨25998305719691097145915355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17332203813127398097276903 25998305719691097145915355)
        ·
          refine ⟨38997458579536645718873033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25998305719691097145915355 38997458579536645718873033)
          ·
            refine ⟨29248093934652484289154775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38997458579536645718873033 29248093934652484289154775)
            ·
              refine ⟨43872140901978726433732163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29248093934652484289154775 43872140901978726433732163)
              ·
                refine ⟨65808211352968089650598245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43872140901978726433732163 65808211352968089650598245)
                ·
                  refine ⟨12339039628681516809487171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65808211352968089650598245 12339039628681516809487171)
                  ·
                    refine ⟨18508559443022275214230757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12339039628681516809487171 18508559443022275214230757)
                    ·
                      refine ⟨3470354895566676602668267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18508559443022275214230757 3470354895566676602668267)
                      ·
                        rfl

theorem cell23_6758492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_6758492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758492 prefixEnd_6758492 := by exact prefixLift 6758492
  have htrace : WordTrace (prefixWord ++ tailWord_6758492) baseStart_6758492 baseEnd_6758492 := by
    simpa [prefixWord, tailWord_6758492, baseEnd_6758492] using wordTrace_append hprefix tailTrace_6758492
  have hstable : (prefixWord ++ tailWord_6758492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758492).length < 2 ^ (prefixWord ++ tailWord_6758492).sum := by decide
  have hdescent : baseEnd_6758492 < baseStart_6758492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
