import V185TrunkScan23Chunk1093

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6476790 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_6476790 : Nat := 118140960795 + 6476790 * 2 ^ 59
def prefixEnd_6476790 : Nat := 4983230072969 + 3 ^ 40 * 6476790 * 2
def baseEnd_6476790 : Nat := 3325706368233819763038791

theorem tailTrace_6476790 : CollatzResearch.WordTrace tailWord_6476790 prefixEnd_6476790 3325706368233819763038791 := by
  unfold tailWord_6476790
  simp only [CollatzResearch.WordTrace]
  refine ⟨14764246137856465782012239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157485292137135635008130549 14764246137856465782012239)
  ·
    refine ⟨22146369206784698673018359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14764246137856465782012239 22146369206784698673018359)
    ·
      refine ⟨33219553810177048009527539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22146369206784698673018359 33219553810177048009527539)
      ·
        refine ⟨49829330715265572014291309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33219553810177048009527539 49829330715265572014291309)
        ·
          refine ⟨18685999018224589505359241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49829330715265572014291309 18685999018224589505359241)
          ·
            refine ⟨14014499263668442129019431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18685999018224589505359241 14014499263668442129019431)
            ·
              refine ⟨21021748895502663193529147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14014499263668442129019431 21021748895502663193529147)
              ·
                refine ⟨31532623343253994790293721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21021748895502663193529147 31532623343253994790293721)
                ·
                  refine ⟨23649467507440496092720291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31532623343253994790293721 23649467507440496092720291)
                  ·
                    refine ⟨35474201261160744139080437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23649467507440496092720291 35474201261160744139080437)
                    ·
                      refine ⟨3325706368233819763038791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35474201261160744139080437 3325706368233819763038791)
                      ·
                        rfl

theorem cell23_6476790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_6476790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476790 prefixEnd_6476790 := by exact prefixLift 6476790
  have htrace : WordTrace (prefixWord ++ tailWord_6476790) baseStart_6476790 baseEnd_6476790 := by
    simpa [prefixWord, tailWord_6476790, baseEnd_6476790] using wordTrace_append hprefix tailTrace_6476790
  have hstable : (prefixWord ++ tailWord_6476790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476790).length < 2 ^ (prefixWord ++ tailWord_6476790).sum := by decide
  have hdescent : baseEnd_6476790 < baseStart_6476790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476810 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 7]
def baseStart_6476810 : Nat := 118140960795 + 6476810 * 2 ^ 59
def prefixEnd_6476810 : Nat := 4983230072969 + 3 ^ 40 * 6476810 * 2
def baseEnd_6476810 : Nat := 369524070871878853865411

theorem tailTrace_6476810 : CollatzResearch.WordTrace tailWord_6476810 prefixEnd_6476810 369524070871878853865411 := by
  unfold tailWord_6476810
  simp only [CollatzResearch.WordTrace]
  refine ⟨59057166916407748981980971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157485778443753997285282589 59057166916407748981980971)
  ·
    refine ⟨88585750374611623472971457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59057166916407748981980971 88585750374611623472971457)
    ·
      refine ⟨66439312780958717604728593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88585750374611623472971457 66439312780958717604728593)
      ·
        refine ⟨49829484585719038203546445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66439312780958717604728593 49829484585719038203546445)
        ·
          refine ⟨18686056719644639326329917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49829484585719038203546445 18686056719644639326329917)
          ·
            refine ⟨7007271269866739747373719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18686056719644639326329917 7007271269866739747373719)
            ·
              refine ⟨10510906904800109621060579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7007271269866739747373719 10510906904800109621060579)
              ·
                refine ⟨15766360357200164431590869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10510906904800109621060579 15766360357200164431590869)
                ·
                  refine ⟨369524070871878853865411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15766360357200164431590869 369524070871878853865411)
                  ·
                    rfl

theorem cell23_6476810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_6476810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476810 prefixEnd_6476810 := by exact prefixLift 6476810
  have htrace : WordTrace (prefixWord ++ tailWord_6476810) baseStart_6476810 baseEnd_6476810 := by
    simpa [prefixWord, tailWord_6476810, baseEnd_6476810] using wordTrace_append hprefix tailTrace_6476810
  have hstable : (prefixWord ++ tailWord_6476810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476810).length < 2 ^ (prefixWord ++ tailWord_6476810).sum := by decide
  have hdescent : baseEnd_6476810 < baseStart_6476810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476821 : List Nat := [1, 3, 2, 1, 4, 3, 2, 1, 2, 2, 2]
def baseStart_6476821 : Nat := 118140960795 + 6476821 * 2 ^ 59
def prefixEnd_6476821 : Nat := 4983230072969 + 3 ^ 40 * 6476821 * 2
def baseEnd_6476821 : Nat := 3325722286134109141751149

theorem tailTrace_6476821 : CollatzResearch.WordTrace tailWord_6476821 prefixEnd_6476821 3325722286134109141751149 := by
  unfold tailWord_6476821
  simp only [CollatzResearch.WordTrace]
  refine ⟨236229068868591144806574317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157486045912394096537716211 236229068868591144806574317)
  ·
    refine ⟨88585900825721679302465369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236229068868591144806574317 88585900825721679302465369)
    ·
      refine ⟨66439425619291259476849027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88585900825721679302465369 66439425619291259476849027)
      ·
        refine ⟨99659138428936889215273541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66439425619291259476849027 99659138428936889215273541)
        ·
          refine ⟨18686088455425666727863789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99659138428936889215273541 18686088455425666727863789)
          ·
            refine ⟨7007283170784625022948921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18686088455425666727863789 7007283170784625022948921)
            ·
              refine ⟨5255462378088468767211691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7007283170784625022948921 5255462378088468767211691)
              ·
                refine ⟨7883193567132703150817537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255462378088468767211691 7883193567132703150817537)
                ·
                  refine ⟨5912395175349527363113153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7883193567132703150817537 5912395175349527363113153)
                  ·
                    refine ⟨4434296381512145522334865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5912395175349527363113153 4434296381512145522334865)
                    ·
                      refine ⟨3325722286134109141751149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434296381512145522334865 3325722286134109141751149)
                      ·
                        rfl

theorem cell23_6476821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_6476821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476821 prefixEnd_6476821 := by exact prefixLift 6476821
  have htrace : WordTrace (prefixWord ++ tailWord_6476821) baseStart_6476821 baseEnd_6476821 := by
    simpa [prefixWord, tailWord_6476821, baseEnd_6476821] using wordTrace_append hprefix tailTrace_6476821
  have hstable : (prefixWord ++ tailWord_6476821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476821).length < 2 ^ (prefixWord ++ tailWord_6476821).sum := by decide
  have hdescent : baseEnd_6476821 < baseStart_6476821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476860 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_6476860 : Nat := 118140960795 + 6476860 * 2 ^ 59
def prefixEnd_6476860 : Nat := 4983230072969 + 3 ^ 40 * 6476860 * 2
def baseEnd_6476860 : Nat := 3325742311879634489163469

theorem tailTrace_6476860 : CollatzResearch.WordTrace tailWord_6476860 prefixEnd_6476860 3325742311879634489163469 := by
  unfold tailWord_6476860
  simp only [CollatzResearch.WordTrace]
  refine ⟨118115245657724927233622017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157486994210299902978162689 118115245657724927233622017)
  ·
    refine ⟨88586434243293695425216513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118115245657724927233622017 88586434243293695425216513)
    ·
      refine ⟨66439825682470271568912385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88586434243293695425216513 66439825682470271568912385)
      ·
        refine ⟨49829869261852703676684289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66439825682470271568912385 49829869261852703676684289)
        ·
          refine ⟨37372401946389527757513217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49829869261852703676684289 37372401946389527757513217)
          ·
            refine ⟨28029301459792145818134913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37372401946389527757513217 28029301459792145818134913)
            ·
              refine ⟨21021976094844109363601185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28029301459792145818134913 21021976094844109363601185)
              ·
                refine ⟨15766482071133082022700889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21021976094844109363601185 15766482071133082022700889)
                ·
                  refine ⟨11824861553349811517025667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15766482071133082022700889 11824861553349811517025667)
                  ·
                    refine ⟨17737292330024717275538501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11824861553349811517025667 17737292330024717275538501)
                    ·
                      refine ⟨3325742311879634489163469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17737292330024717275538501 3325742311879634489163469)
                      ·
                        rfl

theorem cell23_6476860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_6476860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476860 prefixEnd_6476860 := by exact prefixLift 6476860
  have htrace : WordTrace (prefixWord ++ tailWord_6476860) baseStart_6476860 baseEnd_6476860 := by
    simpa [prefixWord, tailWord_6476860, baseEnd_6476860] using wordTrace_append hprefix tailTrace_6476860
  have hstable : (prefixWord ++ tailWord_6476860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476860).length < 2 ^ (prefixWord ++ tailWord_6476860).sum := by decide
  have hdescent : baseEnd_6476860 < baseStart_6476860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476863 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 3]
def baseStart_6476863 : Nat := 118140960795 + 6476863 * 2 ^ 59
def prefixEnd_6476863 : Nat := 4983230072969 + 3 ^ 40 * 6476863 * 2
def baseEnd_6476863 : Nat := 3325743852321597977425955

theorem tailTrace_6476863 : CollatzResearch.WordTrace tailWord_6476863 prefixEnd_6476863 3325743852321597977425955 := by
  unfold tailWord_6476863
  simp only [CollatzResearch.WordTrace]
  refine ⟨236230600734438985979603243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157487067156292657319735495 236230600734438985979603243)
  ·
    refine ⟨354345901101658478969404865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236230600734438985979603243 354345901101658478969404865)
    ·
      refine ⟨265759425826243859227053649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354345901101658478969404865 265759425826243859227053649)
      ·
        refine ⟨199319569369682894420290237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265759425826243859227053649 199319569369682894420290237)
        ·
          refine ⟨74744838513631085407608839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199319569369682894420290237 74744838513631085407608839)
          ·
            refine ⟨112117257770446628111413259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74744838513631085407608839 112117257770446628111413259)
            ·
              refine ⟨168175886655669942167119889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112117257770446628111413259 168175886655669942167119889)
              ·
                refine ⟨126131914991752456625339917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168175886655669942167119889 126131914991752456625339917)
                ·
                  refine ⟨47299468121907171234502469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126131914991752456625339917 47299468121907171234502469)
                  ·
                    refine ⟨8868650272857594606469213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47299468121907171234502469 8868650272857594606469213)
                    ·
                      refine ⟨3325743852321597977425955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8868650272857594606469213 3325743852321597977425955)
                      ·
                        rfl

theorem cell23_6476863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_6476863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476863 prefixEnd_6476863 := by exact prefixLift 6476863
  have htrace : WordTrace (prefixWord ++ tailWord_6476863) baseStart_6476863 baseEnd_6476863 := by
    simpa [prefixWord, tailWord_6476863, baseEnd_6476863] using wordTrace_append hprefix tailTrace_6476863
  have hstable : (prefixWord ++ tailWord_6476863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476863).length < 2 ^ (prefixWord ++ tailWord_6476863).sum := by decide
  have hdescent : baseEnd_6476863 < baseStart_6476863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476877 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_6476877 : Nat := 118140960795 + 6476877 * 2 ^ 59
def prefixEnd_6476877 : Nat := 4983230072969 + 3 ^ 40 * 6476877 * 2
def baseEnd_6476877 : Nat := 3325751041050760922650891

theorem tailTrace_6476877 : CollatzResearch.WordTrace tailWord_6476877 prefixEnd_6476877 3325751041050760922650891 := by
  unfold tailWord_6476877
  simp only [CollatzResearch.WordTrace]
  refine ⟨236231111356388266370612885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157487407570925510913741923 236231111356388266370612885)
  ·
    refine ⟨11073333344830699986122479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 236231111356388266370612885 11073333344830699986122479)
    ·
      refine ⟨16610000017246049979183719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11073333344830699986122479 16610000017246049979183719)
      ·
        refine ⟨24915000025869074968775579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16610000017246049979183719 24915000025869074968775579)
        ·
          refine ⟨37372500038803612453163369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24915000025869074968775579 37372500038803612453163369)
          ·
            refine ⟨28029375029102709339872527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37372500038803612453163369 28029375029102709339872527)
            ·
              refine ⟨42044062543654064009808791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28029375029102709339872527 42044062543654064009808791)
              ·
                refine ⟨63066093815481096014713187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42044062543654064009808791 63066093815481096014713187)
                ·
                  refine ⟨94599140723221644022069781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63066093815481096014713187 94599140723221644022069781)
                  ·
                    refine ⟨4434334721401014563534521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94599140723221644022069781 4434334721401014563534521)
                    ·
                      refine ⟨3325751041050760922650891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434334721401014563534521 3325751041050760922650891)
                      ·
                        rfl

theorem cell23_6476877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_6476877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476877 prefixEnd_6476877 := by exact prefixLift 6476877
  have htrace : WordTrace (prefixWord ++ tailWord_6476877) baseStart_6476877 baseEnd_6476877 := by
    simpa [prefixWord, tailWord_6476877, baseEnd_6476877] using wordTrace_append hprefix tailTrace_6476877
  have hstable : (prefixWord ++ tailWord_6476877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476877).length < 2 ^ (prefixWord ++ tailWord_6476877).sum := by decide
  have hdescent : baseEnd_6476877 < baseStart_6476877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476894 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_6476894 : Nat := 118140960795 + 6476894 * 2 ^ 59
def prefixEnd_6476894 : Nat := 4983230072969 + 3 ^ 40 * 6476894 * 2
def baseEnd_6476894 : Nat := 3325759770221887356138313

theorem tailTrace_6476894 : CollatzResearch.WordTrace tailWord_6476894 prefixEnd_6476894 3325759770221887356138313 := by
  unfold tailWord_6476894
  simp only [CollatzResearch.WordTrace]
  refine ⟨29528966424665834784247717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157487820931551118849321157 29528966424665834784247717)
  ·
    refine ⟨5536681204624844022046447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29528966424665834784247717 5536681204624844022046447)
    ·
      refine ⟨8305021806937266033069671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5536681204624844022046447 8305021806937266033069671)
      ·
        refine ⟨12457532710405899049604507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8305021806937266033069671 12457532710405899049604507)
        ·
          refine ⟨18686299065608848574406761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12457532710405899049604507 18686299065608848574406761)
          ·
            refine ⟨14014724299206636430805071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18686299065608848574406761 14014724299206636430805071)
            ·
              refine ⟨21022086448809954646207607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14014724299206636430805071 21022086448809954646207607)
              ·
                refine ⟨31533129673214931969311411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21022086448809954646207607 31533129673214931969311411)
                ·
                  refine ⟨47299694509822397953967117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31533129673214931969311411 47299694509822397953967117)
                  ·
                    refine ⟨17737385441183399232737669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47299694509822397953967117 17737385441183399232737669)
                    ·
                      refine ⟨3325759770221887356138313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17737385441183399232737669 3325759770221887356138313)
                      ·
                        rfl

theorem cell23_6476894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_6476894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476894 prefixEnd_6476894 := by exact prefixLift 6476894
  have htrace : WordTrace (prefixWord ++ tailWord_6476894) baseStart_6476894 baseEnd_6476894 := by
    simpa [prefixWord, tailWord_6476894, baseEnd_6476894] using wordTrace_append hprefix tailTrace_6476894
  have hstable : (prefixWord ++ tailWord_6476894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476894).length < 2 ^ (prefixWord ++ tailWord_6476894).sum := by decide
  have hdescent : baseEnd_6476894 < baseStart_6476894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476913 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 5, 5]
def baseStart_6476913 : Nat := 118140960795 + 6476913 * 2 ^ 59
def prefixEnd_6476913 : Nat := 4983230072969 + 3 ^ 40 * 6476913 * 2
def baseEnd_6476913 : Nat := 1108589842118107593933575

theorem tailTrace_6476913 : CollatzResearch.WordTrace tailWord_6476913 prefixEnd_6476913 1108589842118107593933575 := by
  unfold tailWord_6476913
  simp only [CollatzResearch.WordTrace]
  refine ⟨236232424384257844518923393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157488282922838563012615595 236232424384257844518923393)
  ·
    refine ⟨177174318288193383389192545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236232424384257844518923393 177174318288193383389192545)
    ·
      refine ⟨132880738716145037541894409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177174318288193383389192545 132880738716145037541894409)
      ·
        refine ⟨99660554037108778156420807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132880738716145037541894409 99660554037108778156420807)
        ·
          refine ⟨149490831055663167234631211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99660554037108778156420807 149490831055663167234631211)
          ·
            refine ⟨224236246583494750851946817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149490831055663167234631211 224236246583494750851946817)
            ·
              refine ⟨168177184937621063138960113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224236246583494750851946817 168177184937621063138960113)
              ·
                refine ⟨126132888703215797354220085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168177184937621063138960113 126132888703215797354220085)
                ·
                  refine ⟨11824958315926481001958133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126132888703215797354220085 11824958315926481001958133)
                  ·
                    refine ⟨1108589842118107593933575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11824958315926481001958133 1108589842118107593933575)
                    ·
                      rfl

theorem cell23_6476913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_6476913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476913 prefixEnd_6476913 := by exact prefixLift 6476913
  have htrace : WordTrace (prefixWord ++ tailWord_6476913) baseStart_6476913 baseEnd_6476913 := by
    simpa [prefixWord, tailWord_6476913, baseEnd_6476913] using wordTrace_append hprefix tailTrace_6476913
  have hstable : (prefixWord ++ tailWord_6476913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476913).length < 2 ^ (prefixWord ++ tailWord_6476913).sum := by decide
  have hdescent : baseEnd_6476913 < baseStart_6476913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476917 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 8]
def baseStart_6476917 : Nat := 118140960795 + 6476917 * 2 ^ 59
def prefixEnd_6476917 : Nat := 4983230072969 + 3 ^ 40 * 6476917 * 2
def baseEnd_6476917 : Nat := 369530175586326751794523

theorem tailTrace_6476917 : CollatzResearch.WordTrace tailWord_6476917 prefixEnd_6476917 369530175586326751794523 := by
  unfold tailWord_6476917
  simp only [CollatzResearch.WordTrace]
  refine ⟨236232570276243353202069005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157488380184162235468046003 236232570276243353202069005)
  ·
    refine ⟨88587213853591257450775877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236232570276243353202069005 88587213853591257450775877)
    ·
      refine ⟨16610102597548360772020477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88587213853591257450775877 16610102597548360772020477)
      ·
        refine ⟨6228788474080635289507679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16610102597548360772020477 6228788474080635289507679)
        ·
          refine ⟨9343182711120952934261519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6228788474080635289507679 9343182711120952934261519)
          ·
            refine ⟨14014774066681429401392279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9343182711120952934261519 14014774066681429401392279)
            ·
              refine ⟨21022161100022144102088419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14014774066681429401392279 21022161100022144102088419)
              ·
                refine ⟨31533241650033216153132629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21022161100022144102088419 31533241650033216153132629)
                ·
                  refine ⟨369530175586326751794523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31533241650033216153132629 369530175586326751794523)
                  ·
                    rfl

theorem cell23_6476917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_6476917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476917 prefixEnd_6476917 := by exact prefixLift 6476917
  have htrace : WordTrace (prefixWord ++ tailWord_6476917) baseStart_6476917 baseEnd_6476917 := by
    simpa [prefixWord, tailWord_6476917, baseEnd_6476917] using wordTrace_append hprefix tailTrace_6476917
  have hstable : (prefixWord ++ tailWord_6476917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476917).length < 2 ^ (prefixWord ++ tailWord_6476917).sum := by decide
  have hdescent : baseEnd_6476917 < baseStart_6476917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476960 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 6, 4]
def baseStart_6476960 : Nat := 118140960795 + 6476960 * 2 ^ 59
def prefixEnd_6476960 : Nat := 4983230072969 + 3 ^ 40 * 6476960 * 2
def baseEnd_6476960 : Nat := 1108597886648361365971003

theorem tailTrace_6476960 : CollatzResearch.WordTrace tailWord_6476960 prefixEnd_6476960 1108597886648361365971003 := by
  unfold tailWord_6476960
  simp only [CollatzResearch.WordTrace]
  refine ⟨118117069307543785772942167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157489425743391714363922889 118117069307543785772942167)
  ·
    refine ⟨177175603961315678659413251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118117069307543785772942167 177175603961315678659413251)
    ·
      refine ⟨265763405941973517989119877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177175603961315678659413251 265763405941973517989119877)
      ·
        refine ⟨49830638614120034622959977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265763405941973517989119877 49830638614120034622959977)
        ·
          refine ⟨37372978960590025967219983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49830638614120034622959977 37372978960590025967219983)
          ·
            refine ⟨56059468440885038950829975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37372978960590025967219983 56059468440885038950829975)
            ·
              refine ⟨84089202661327558426244963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56059468440885038950829975 84089202661327558426244963)
              ·
                refine ⟨126133803991991337639367445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84089202661327558426244963 126133803991991337639367445)
                ·
                  refine ⟨5912522062124593951845349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126133803991991337639367445 5912522062124593951845349)
                  ·
                    refine ⟨1108597886648361365971003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5912522062124593951845349 1108597886648361365971003)
                    ·
                      rfl

theorem cell23_6476960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6, 4].length) (baseStart_6476960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476960 prefixEnd_6476960 := by exact prefixLift 6476960
  have htrace : WordTrace (prefixWord ++ tailWord_6476960) baseStart_6476960 baseEnd_6476960 := by
    simpa [prefixWord, tailWord_6476960, baseEnd_6476960] using wordTrace_append hprefix tailTrace_6476960
  have hstable : (prefixWord ++ tailWord_6476960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476960).length < 2 ^ (prefixWord ++ tailWord_6476960).sum := by decide
  have hdescent : baseEnd_6476960 < baseStart_6476960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476977 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 4, 4]
def baseStart_6476977 : Nat := 118140960795 + 6476977 * 2 ^ 59
def prefixEnd_6476977 : Nat := 4983230072969 + 3 ^ 40 * 6476977 * 2
def baseEnd_6476977 : Nat := 1108600796372070177133477

theorem tailTrace_6476977 : CollatzResearch.WordTrace tailWord_6476977 prefixEnd_6476977 1108600796372070177133477 := by
  unfold tailWord_6476977
  simp only [CollatzResearch.WordTrace]
  refine ⟨236234758656025983449253185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157489839104017322299502123 236234758656025983449253185)
  ·
    refine ⟨177176068992019487586939889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236234758656025983449253185 177176068992019487586939889)
    ·
      refine ⟨132882051744014615690204917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177176068992019487586939889 132882051744014615690204917)
      ·
        refine ⟨12457692351001370220956711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132882051744014615690204917 12457692351001370220956711)
        ·
          refine ⟨18686538526502055331435067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12457692351001370220956711 18686538526502055331435067)
          ·
            refine ⟨28029807789753082997152601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18686538526502055331435067 28029807789753082997152601)
            ·
              refine ⟨21022355842314812247864451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28029807789753082997152601 21022355842314812247864451)
              ·
                refine ⟨31533533763472218371796677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21022355842314812247864451 31533533763472218371796677)
                ·
                  refine ⟨5912537580651040944711877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31533533763472218371796677 5912537580651040944711877)
                  ·
                    refine ⟨1108600796372070177133477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5912537580651040944711877 1108600796372070177133477)
                    ·
                      rfl

theorem cell23_6476977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_6476977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476977 prefixEnd_6476977 := by exact prefixLift 6476977
  have htrace : WordTrace (prefixWord ++ tailWord_6476977) baseStart_6476977 baseEnd_6476977 := by
    simpa [prefixWord, tailWord_6476977, baseEnd_6476977] using wordTrace_append hprefix tailTrace_6476977
  have hstable : (prefixWord ++ tailWord_6476977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476977).length < 2 ^ (prefixWord ++ tailWord_6476977).sum := by decide
  have hdescent : baseEnd_6476977 < baseStart_6476977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476990 : List Nat := [4, 2, 1, 1, 3, 1, 1, 10]
def baseStart_6476990 : Nat := 118140960795 + 6476990 * 2 ^ 59
def prefixEnd_6476990 : Nat := 4983230072969 + 3 ^ 40 * 6476990 * 2
def baseEnd_6476990 : Nat := 123178113494989591871773

theorem tailTrace_6476990 : CollatzResearch.WordTrace tailWord_6476990 prefixEnd_6476990 123178113494989591871773 := by
  unfold tailWord_6476990
  simp only [CollatzResearch.WordTrace]
  refine ⟨29529404100622360833684553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157490155203319257779650949 29529404100622360833684553)
  ·
    refine ⟨22147053075466770625263415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29529404100622360833684553 22147053075466770625263415)
    ·
      refine ⟨33220579613200155937895123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22147053075466770625263415 33220579613200155937895123)
      ·
        refine ⟨49830869419800233906842685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33220579613200155937895123 49830869419800233906842685)
        ·
          refine ⟨18686576032425087715066007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49830869419800233906842685 18686576032425087715066007)
          ·
            refine ⟨28029864048637631572599011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18686576032425087715066007 28029864048637631572599011)
            ·
              refine ⟨42044796072956447358898517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28029864048637631572599011 42044796072956447358898517)
              ·
                refine ⟨123178113494989591871773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42044796072956447358898517 123178113494989591871773)
                ·
                  rfl

theorem cell23_6476990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_6476990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476990 prefixEnd_6476990 := by exact prefixLift 6476990
  have htrace : WordTrace (prefixWord ++ tailWord_6476990) baseStart_6476990 baseEnd_6476990 := by
    simpa [prefixWord, tailWord_6476990, baseEnd_6476990] using wordTrace_append hprefix tailTrace_6476990
  have hstable : (prefixWord ++ tailWord_6476990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476990).length < 2 ^ (prefixWord ++ tailWord_6476990).sum := by decide
  have hdescent : baseEnd_6476990 < baseStart_6476990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477003 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 4, 7]
def baseStart_6477003 : Nat := 118140960795 + 6477003 * 2 ^ 59
def prefixEnd_6477003 : Nat := 4983230072969 + 3 ^ 40 * 6477003 * 2
def baseEnd_6477003 : Nat := 1108605246537742476558437

theorem tailTrace_6477003 : CollatzResearch.WordTrace tailWord_6477003 prefixEnd_6477003 1108605246537742476558437 := by
  unfold tailWord_6477003
  simp only [CollatzResearch.WordTrace]
  refine ⟨236235706953931789889699663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157490471302621193259799775 236235706953931789889699663)
  ·
    refine ⟨354353560430897684834549495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236235706953931789889699663 354353560430897684834549495)
    ·
      refine ⟨531530340646346527251824243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354353560430897684834549495 531530340646346527251824243)
      ·
        refine ⟨797295510969519790877736365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531530340646346527251824243 797295510969519790877736365)
        ·
          refine ⟨298985816613569921579151137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 797295510969519790877736365 298985816613569921579151137)
          ·
            refine ⟨224239362460177441184363353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298985816613569921579151137 224239362460177441184363353)
            ·
              refine ⟨168179521845133080888272515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224239362460177441184363353 168179521845133080888272515)
              ·
                refine ⟨252269282767699621332408773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168179521845133080888272515 252269282767699621332408773)
                ·
                  refine ⟨47300490518943678999826645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252269282767699621332408773 47300490518943678999826645)
                  ·
                    refine ⟨1108605246537742476558437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47300490518943678999826645 1108605246537742476558437)
                    ·
                      rfl

theorem cell23_6477003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 7].length) (baseStart_6477003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477003 prefixEnd_6477003 := by exact prefixLift 6477003
  have htrace : WordTrace (prefixWord ++ tailWord_6477003) baseStart_6477003 baseEnd_6477003 := by
    simpa [prefixWord, tailWord_6477003, baseEnd_6477003] using wordTrace_append hprefix tailTrace_6477003
  have hstable : (prefixWord ++ tailWord_6477003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477003).length < 2 ^ (prefixWord ++ tailWord_6477003).sum := by decide
  have hdescent : baseEnd_6477003 < baseStart_6477003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477021 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_6477021 : Nat := 118140960795 + 6477021 * 2 ^ 59
def prefixEnd_6477021 : Nat := 4983230072969 + 3 ^ 40 * 6477021 * 2
def baseEnd_6477021 : Nat := 3325824982265008359250229

theorem tailTrace_6477021 : CollatzResearch.WordTrace tailWord_6477021 prefixEnd_6477021 3325824982265008359250229 := by
  unfold tailWord_6477021
  simp only [CollatzResearch.WordTrace]
  refine ⟨236236363467866578963854917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157490908978577719309236611 236236363467866578963854917)
  ·
    refine ⟨44294318150224983555722797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236236363467866578963854917 44294318150224983555722797)
    ·
      refine ⟨16610369306334368833396049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44294318150224983555722797 16610369306334368833396049)
      ·
        refine ⟨12457776979750776625047037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16610369306334368833396049 12457776979750776625047037)
        ·
          refine ⟨4671666367406541234392639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12457776979750776625047037 4671666367406541234392639)
          ·
            refine ⟨7007499551109811851588959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4671666367406541234392639 7007499551109811851588959)
            ·
              refine ⟨10511249326664717777383439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7007499551109811851588959 10511249326664717777383439)
              ·
                refine ⟨15766873989997076666075159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10511249326664717777383439 15766873989997076666075159)
                ·
                  refine ⟨23650310984995614999112739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15766873989997076666075159 23650310984995614999112739)
                  ·
                    refine ⟨35475466477493422498669109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23650310984995614999112739 35475466477493422498669109)
                    ·
                      refine ⟨3325824982265008359250229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35475466477493422498669109 3325824982265008359250229)
                      ·
                        rfl

theorem cell23_6477021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_6477021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477021 prefixEnd_6477021 := by exact prefixLift 6477021
  have htrace : WordTrace (prefixWord ++ tailWord_6477021) baseStart_6477021 baseEnd_6477021 := by
    simpa [prefixWord, tailWord_6477021, baseEnd_6477021] using wordTrace_append hprefix tailTrace_6477021
  have hstable : (prefixWord ++ tailWord_6477021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477021).length < 2 ^ (prefixWord ++ tailWord_6477021).sum := by decide
  have hdescent : baseEnd_6477021 < baseStart_6477021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477034 : List Nat := [3, 1, 3, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_6477034 : Nat := 118140960795 + 6477034 * 2 ^ 59
def prefixEnd_6477034 : Nat := 4983230072969 + 3 ^ 40 * 6477034 * 2
def baseEnd_6477034 : Nat := 3325831657513516808387669

theorem tailTrace_6477034 : CollatzResearch.WordTrace tailWord_6477034 prefixEnd_6477034 3325831657513516808387669 := by
  unfold tailWord_6477034
  simp only [CollatzResearch.WordTrace]
  refine ⟨59059209404204870546019539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157491225077879654789385437 59059209404204870546019539)
  ·
    refine ⟨88588814106307305819029309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59059209404204870546019539 88588814106307305819029309)
    ·
      refine ⟨33220805289865239682135991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88588814106307305819029309 33220805289865239682135991)
      ·
        refine ⟨49831207934797859523203987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33220805289865239682135991 49831207934797859523203987)
        ·
          refine ⟨74746811902196789284805981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49831207934797859523203987 74746811902196789284805981)
          ·
            refine ⟨28030054463323795981802243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74746811902196789284805981 28030054463323795981802243)
            ·
              refine ⟨42045081694985693972703365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28030054463323795981802243 42045081694985693972703365)
              ·
                refine ⟨7883452817809817619881881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42045081694985693972703365 7883452817809817619881881)
                ·
                  refine ⟨5912589613357363214911411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7883452817809817619881881 5912589613357363214911411)
                  ·
                    refine ⟨8868884420036044822367117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5912589613357363214911411 8868884420036044822367117)
                    ·
                      refine ⟨3325831657513516808387669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8868884420036044822367117 3325831657513516808387669)
                      ·
                        rfl

theorem cell23_6477034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_6477034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477034 prefixEnd_6477034 := by exact prefixLift 6477034
  have htrace : WordTrace (prefixWord ++ tailWord_6477034) baseStart_6477034 baseEnd_6477034 := by
    simpa [prefixWord, tailWord_6477034, baseEnd_6477034] using wordTrace_append hprefix tailTrace_6477034
  have hstable : (prefixWord ++ tailWord_6477034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477034).length < 2 ^ (prefixWord ++ tailWord_6477034).sum := by decide
  have hdescent : baseEnd_6477034 < baseStart_6477034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477050 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 2, 6]
def baseStart_6477050 : Nat := 118140960795 + 6477050 * 2 ^ 59
def prefixEnd_6477050 : Nat := 4983230072969 + 3 ^ 40 * 6477050 * 2
def baseEnd_6477050 : Nat := 1108613291067996248595865

theorem tailTrace_6477050 : CollatzResearch.WordTrace tailWord_6477050 prefixEnd_6477050 1108613291067996248595865 := by
  unfold tailWord_6477050
  simp only [CollatzResearch.WordTrace]
  refine ⟨59059355296190379229165151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157491614123174344611107069 59059355296190379229165151)
  ·
    refine ⟨88589032944285568843747727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59059355296190379229165151 88589032944285568843747727)
    ·
      refine ⟨132883549416428353265621591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88589032944285568843747727 132883549416428353265621591)
      ·
        refine ⟨199325324124642529898432387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132883549416428353265621591 199325324124642529898432387)
        ·
          refine ⟨298987986186963794847648581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199325324124642529898432387 298987986186963794847648581)
          ·
            refine ⟨56060247410055711533934109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 298987986186963794847648581 56060247410055711533934109)
            ·
              refine ⟨21022592778770891825225291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56060247410055711533934109 21022592778770891825225291)
              ·
                refine ⟨31533889168156337737837937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21022592778770891825225291 31533889168156337737837937)
                ·
                  refine ⟨23650416876117253303378453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31533889168156337737837937 23650416876117253303378453)
                  ·
                    refine ⟨1108613291067996248595865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23650416876117253303378453 1108613291067996248595865)
                    ·
                      rfl

theorem cell23_6477050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_6477050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477050 prefixEnd_6477050 := by exact prefixLift 6477050
  have htrace : WordTrace (prefixWord ++ tailWord_6477050) baseStart_6477050 baseEnd_6477050 := by
    simpa [prefixWord, tailWord_6477050, baseEnd_6477050] using wordTrace_append hprefix tailTrace_6477050
  have hstable : (prefixWord ++ tailWord_6477050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477050).length < 2 ^ (prefixWord ++ tailWord_6477050).sum := by decide
  have hdescent : baseEnd_6477050 < baseStart_6477050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477091 : List Nat := [1, 1, 1, 4, 2, 3, 3, 2, 2, 2, 2]
def baseStart_6477091 : Nat := 118140960795 + 6477091 * 2 ^ 59
def prefixEnd_6477091 : Nat := 4983230072969 + 3 ^ 40 * 6477091 * 2
def baseEnd_6477091 : Nat := 3325860925910823085374907

theorem tailTrace_6477091 : CollatzResearch.WordTrace tailWord_6477091 prefixEnd_6477091 3325860925910823085374907 := by
  unfold tailWord_6477091
  simp only [CollatzResearch.WordTrace]
  refine ⟨236238916577612980918903127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157492611051741987279268751 236238916577612980918903127)
  ·
    refine ⟨354358374866419471378354691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236238916577612980918903127 354358374866419471378354691)
    ·
      refine ⟨531537562299629207067532037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354358374866419471378354691 531537562299629207067532037)
      ·
        refine ⟨99663292931180476325162257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 531537562299629207067532037 99663292931180476325162257)
        ·
          refine ⟨74747469698385357243871693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99663292931180476325162257 74747469698385357243871693)
          ·
            refine ⟨28030301136894508966451885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74747469698385357243871693 28030301136894508966451885)
            ·
              refine ⟨10511362926335440862419457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28030301136894508966451885 10511362926335440862419457)
              ·
                refine ⟨7883522194751580646814593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10511362926335440862419457 7883522194751580646814593)
                ·
                  refine ⟨5912641646063685485110945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7883522194751580646814593 5912641646063685485110945)
                  ·
                    refine ⟨4434481234547764113833209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5912641646063685485110945 4434481234547764113833209)
                    ·
                      refine ⟨3325860925910823085374907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434481234547764113833209 3325860925910823085374907)
                      ·
                        rfl

theorem cell23_6477091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_6477091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477091 prefixEnd_6477091 := by exact prefixLift 6477091
  have htrace : WordTrace (prefixWord ++ tailWord_6477091) baseStart_6477091 baseEnd_6477091 := by
    simpa [prefixWord, tailWord_6477091, baseEnd_6477091] using wordTrace_append hprefix tailTrace_6477091
  have hstable : (prefixWord ++ tailWord_6477091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477091).length < 2 ^ (prefixWord ++ tailWord_6477091).sum := by decide
  have hdescent : baseEnd_6477091 < baseStart_6477091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477107 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 3]
def baseStart_6477107 : Nat := 118140960795 + 6477107 * 2 ^ 59
def prefixEnd_6477107 : Nat := 4983230072969 + 3 ^ 40 * 6477107 * 2
def baseEnd_6477107 : Nat := 3325869141601295022774833

theorem tailTrace_6477107 : CollatzResearch.WordTrace tailWord_6477107 prefixEnd_6477107 3325869141601295022774833 := by
  unfold tailWord_6477107
  simp only [CollatzResearch.WordTrace]
  refine ⟨236239500145555015651485575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157493000097036677100990383 236239500145555015651485575)
  ·
    refine ⟨354359250218332523477228363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236239500145555015651485575 354359250218332523477228363)
    ·
      refine ⟨531538875327498785215842545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354359250218332523477228363 531538875327498785215842545)
      ·
        refine ⟨398654156495624088911881909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531538875327498785215842545 398654156495624088911881909)
        ·
          refine ⟨37373827171464758335488929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 398654156495624088911881909 37373827171464758335488929)
          ·
            refine ⟨28030370378598568751616697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37373827171464758335488929 28030370378598568751616697)
            ·
              refine ⟨21022777783948926563712523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28030370378598568751616697 21022777783948926563712523)
              ·
                refine ⟨31534166675923389845568785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21022777783948926563712523 31534166675923389845568785)
                ·
                  refine ⟨23650625006942542384176589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31534166675923389845568785 23650625006942542384176589)
                  ·
                    refine ⟨8868984377603453394066221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23650625006942542384176589 8868984377603453394066221)
                    ·
                      refine ⟨3325869141601295022774833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8868984377603453394066221 3325869141601295022774833)
                      ·
                        rfl

theorem cell23_6477107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 3].length) (baseStart_6477107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477107 prefixEnd_6477107 := by exact prefixLift 6477107
  have htrace : WordTrace (prefixWord ++ tailWord_6477107) baseStart_6477107 baseEnd_6477107 := by
    simpa [prefixWord, tailWord_6477107, baseEnd_6477107] using wordTrace_append hprefix tailTrace_6477107
  have hstable : (prefixWord ++ tailWord_6477107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477107).length < 2 ^ (prefixWord ++ tailWord_6477107).sum := by decide
  have hdescent : baseEnd_6477107 < baseStart_6477107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477167 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 3]
def baseStart_6477167 : Nat := 118140960795 + 6477167 * 2 ^ 59
def prefixEnd_6477167 : Nat := 4983230072969 + 3 ^ 40 * 6477167 * 2
def baseEnd_6477167 : Nat := 3325899950440564788024557

theorem tailTrace_6477167 : CollatzResearch.WordTrace tailWord_6477167 prefixEnd_6477167 3325899950440564788024557 := by
  unfold tailWord_6477167
  simp only [CollatzResearch.WordTrace]
  refine ⟨236241688525337645898669755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157494459016891763932446503 236241688525337645898669755)
  ·
    refine ⟨354362532788006468848004633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236241688525337645898669755 354362532788006468848004633)
    ·
      refine ⟨265771899591004851636003475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354362532788006468848004633 265771899591004851636003475)
      ·
        refine ⟨398657849386507277454005213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265771899591004851636003475 398657849386507277454005213)
        ·
          refine ⟨149496693519940229045251955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398657849386507277454005213 149496693519940229045251955)
          ·
            refine ⟨224245040279910343567877933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149496693519940229045251955 224245040279910343567877933)
            ·
              refine ⟨84091890104966378837954225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224245040279910343567877933 84091890104966378837954225)
              ·
                refine ⟨63068917578724784128465669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84091890104966378837954225 63068917578724784128465669)
                ·
                  refine ⟨11825422046010897024087313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63068917578724784128465669 11825422046010897024087313)
                  ·
                    refine ⟨8869066534508172768065485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11825422046010897024087313 8869066534508172768065485)
                    ·
                      refine ⟨3325899950440564788024557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8869066534508172768065485 3325899950440564788024557)
                      ·
                        rfl

theorem cell23_6477167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 3].length) (baseStart_6477167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477167 prefixEnd_6477167 := by exact prefixLift 6477167
  have htrace : WordTrace (prefixWord ++ tailWord_6477167) baseStart_6477167 baseEnd_6477167 := by
    simpa [prefixWord, tailWord_6477167, baseEnd_6477167] using wordTrace_append hprefix tailTrace_6477167
  have hstable : (prefixWord ++ tailWord_6477167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477167).length < 2 ^ (prefixWord ++ tailWord_6477167).sum := by decide
  have hdescent : baseEnd_6477167 < baseStart_6477167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477204 : List Nat := [2, 4, 2, 1, 2, 1, 1, 4, 6]
def baseStart_6477204 : Nat := 118140960795 + 6477204 * 2 ^ 59
def prefixEnd_6477204 : Nat := 4983230072969 + 3 ^ 40 * 6477204 * 2
def baseEnd_6477204 : Nat := 369546549913864571473543

theorem tailTrace_6477204 : CollatzResearch.WordTrace tailWord_6477204 prefixEnd_6477204 369546549913864571473543 := by
  unfold tailWord_6477204
  simp only [CollatzResearch.WordTrace]
  refine ⟨118121519013101800608883333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157495358684135734145177777 118121519013101800608883333)
  ·
    refine ⟨22147784814956587614165625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118121519013101800608883333 22147784814956587614165625)
    ·
      refine ⟨16610838611217440710624219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22147784814956587614165625 16610838611217440710624219)
      ·
        refine ⟨24916257916826161065936329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16610838611217440710624219 24916257916826161065936329)
        ·
          refine ⟨18687193437619620799452247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24916257916826161065936329 18687193437619620799452247)
          ·
            refine ⟨28030790156429431199178371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18687193437619620799452247 28030790156429431199178371)
            ·
              refine ⟨42046185234644146798767557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28030790156429431199178371 42046185234644146798767557)
              ·
                refine ⟨7883659731495777524768917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42046185234644146798767557 7883659731495777524768917)
                ·
                  refine ⟨369546549913864571473543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7883659731495777524768917 369546549913864571473543)
                  ·
                    rfl

theorem cell23_6477204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_6477204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477204 prefixEnd_6477204 := by exact prefixLift 6477204
  have htrace : WordTrace (prefixWord ++ tailWord_6477204) baseStart_6477204 baseEnd_6477204 := by
    simpa [prefixWord, tailWord_6477204, baseEnd_6477204] using wordTrace_append hprefix tailTrace_6477204
  have hstable : (prefixWord ++ tailWord_6477204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477204).length < 2 ^ (prefixWord ++ tailWord_6477204).sum := by decide
  have hdescent : baseEnd_6477204 < baseStart_6477204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477208 : List Nat := [2, 1, 2, 5, 2, 1, 1, 4, 1, 4]
def baseStart_6477208 : Nat := 118140960795 + 6477208 * 2 ^ 59
def prefixEnd_6477208 : Nat := 4983230072969 + 3 ^ 40 * 6477208 * 2
def baseEnd_6477208 : Nat := 1108640334382466375870623

theorem tailTrace_6477208 : CollatzResearch.WordTrace tailWord_6477208 prefixEnd_6477208 1108640334382466375870623 := by
  unfold tailWord_6477208
  simp only [CollatzResearch.WordTrace]
  refine ⟨118121591959094554950456139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157495455945459406600608185 118121591959094554950456139)
  ·
    refine ⟨177182387938641832425684209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118121591959094554950456139 177182387938641832425684209)
    ·
      refine ⟨132886790953981374319263157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177182387938641832425684209 132886790953981374319263157)
      ·
        refine ⟨12458136651935753842430921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132886790953981374319263157 12458136651935753842430921)
        ·
          refine ⟨9343602488951815381823191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12458136651935753842430921 9343602488951815381823191)
          ·
            refine ⟨14015403733427723072734787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9343602488951815381823191 14015403733427723072734787)
            ·
              refine ⟨21023105600141584609102181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14015403733427723072734787 21023105600141584609102181)
              ·
                refine ⟨3941832300026547114206659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21023105600141584609102181 3941832300026547114206659)
                ·
                  refine ⟨5912748450039820671309989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941832300026547114206659 5912748450039820671309989)
                  ·
                    refine ⟨1108640334382466375870623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5912748450039820671309989 1108640334382466375870623)
                    ·
                      rfl

theorem cell23_6477208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_6477208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477208 prefixEnd_6477208 := by exact prefixLift 6477208
  have htrace : WordTrace (prefixWord ++ tailWord_6477208) baseStart_6477208 baseEnd_6477208 := by
    simpa [prefixWord, tailWord_6477208, baseEnd_6477208] using wordTrace_append hprefix tailTrace_6477208
  have hstable : (prefixWord ++ tailWord_6477208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477208).length < 2 ^ (prefixWord ++ tailWord_6477208).sum := by decide
  have hdescent : baseEnd_6477208 < baseStart_6477208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477241 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 1, 5, 2]
def baseStart_6477241 : Nat := 118140960795 + 6477241 * 2 ^ 59
def prefixEnd_6477241 : Nat := 4983230072969 + 3 ^ 40 * 6477241 * 2
def baseEnd_6477241 : Nat := 3325937948008997498499217

theorem tailTrace_6477241 : CollatzResearch.WordTrace tailWord_6477241 prefixEnd_6477241 3325937948008997498499217 := by
  unfold tailWord_6477241
  simp only [CollatzResearch.WordTrace]
  refine ⟨236244387527069556536863577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157496258351379704357909051 236244387527069556536863577)
  ·
    refine ⟨177183290645302167402647683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236244387527069556536863577 177183290645302167402647683)
    ·
      refine ⟨265774935967953251103971525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177183290645302167402647683 265774935967953251103971525)
      ·
        refine ⟨49832800493991234581994661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265774935967953251103971525 49832800493991234581994661)
        ·
          refine ⟨9343650092623356484123999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49832800493991234581994661 9343650092623356484123999)
          ·
            refine ⟨14015475138935034726185999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9343650092623356484123999 14015475138935034726185999)
            ·
              refine ⟨21023212708402552089278999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14015475138935034726185999 21023212708402552089278999)
              ·
                refine ⟨31534819062603828133918499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21023212708402552089278999 31534819062603828133918499)
                ·
                  refine ⟨47302228593905742200877749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31534819062603828133918499 47302228593905742200877749)
                  ·
                    refine ⟨4434583930678663331332289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47302228593905742200877749 4434583930678663331332289)
                    ·
                      refine ⟨3325937948008997498499217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434583930678663331332289 3325937948008997498499217)
                      ·
                        rfl

theorem cell23_6477241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_6477241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477241 prefixEnd_6477241 := by exact prefixLift 6477241
  have htrace : WordTrace (prefixWord ++ tailWord_6477241) baseStart_6477241 baseEnd_6477241 := by
    simpa [prefixWord, tailWord_6477241, baseEnd_6477241] using wordTrace_append hprefix tailTrace_6477241
  have hstable : (prefixWord ++ tailWord_6477241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477241).length < 2 ^ (prefixWord ++ tailWord_6477241).sum := by decide
  have hdescent : baseEnd_6477241 < baseStart_6477241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477257 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 5]
def baseStart_6477257 : Nat := 118140960795 + 6477257 * 2 ^ 59
def prefixEnd_6477257 : Nat := 4983230072969 + 3 ^ 40 * 6477257 * 2
def baseEnd_6477257 : Nat := 3325946163699469435899143

theorem tailTrace_6477257 : CollatzResearch.WordTrace tailWord_6477257 prefixEnd_6477257 3325946163699469435899143 := by
  unfold tailWord_6477257
  simp only [CollatzResearch.WordTrace]
  refine ⟨236244971095011591269446025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157496647396674394179630683 236244971095011591269446025)
  ·
    refine ⟨177183728321258693452084519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236244971095011591269446025 177183728321258693452084519)
    ·
      refine ⟨265775592481888040178126779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177183728321258693452084519 265775592481888040178126779)
      ·
        refine ⟨398663388722832060267190169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265775592481888040178126779 398663388722832060267190169)
        ·
          refine ⟨298997541542124045200392627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398663388722832060267190169 298997541542124045200392627)
          ·
            refine ⟨448496312313186067800588941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298997541542124045200392627 448496312313186067800588941)
            ·
              refine ⟨168186117117444775425220853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 448496312313186067800588941 168186117117444775425220853)
              ·
                refine ⟨15767448479760447696114455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168186117117444775425220853 15767448479760447696114455)
                ·
                  refine ⟨23651172719640671544171683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15767448479760447696114455 23651172719640671544171683)
                  ·
                    refine ⟨35476759079461007316257525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23651172719640671544171683 35476759079461007316257525)
                    ·
                      refine ⟨3325946163699469435899143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35476759079461007316257525 3325946163699469435899143)
                      ·
                        rfl

theorem cell23_6477257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_6477257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477257 prefixEnd_6477257 := by exact prefixLift 6477257
  have htrace : WordTrace (prefixWord ++ tailWord_6477257) baseStart_6477257 baseEnd_6477257 := by
    simpa [prefixWord, tailWord_6477257, baseEnd_6477257] using wordTrace_append hprefix tailTrace_6477257
  have hstable : (prefixWord ++ tailWord_6477257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477257).length < 2 ^ (prefixWord ++ tailWord_6477257).sum := by decide
  have hdescent : baseEnd_6477257 < baseStart_6477257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477274 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_6477274 : Nat := 118140960795 + 6477274 * 2 ^ 59
def prefixEnd_6477274 : Nat := 4983230072969 + 3 ^ 40 * 6477274 * 2
def baseEnd_6477274 : Nat := 3325954892870595869386565

theorem tailTrace_6477274 : CollatzResearch.WordTrace tailWord_6477274 prefixEnd_6477274 3325954892870595869386565 := by
  unfold tailWord_6477274
  simp only [CollatzResearch.WordTrace]
  refine ⟨59061397783987500793203719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157497060757300002115209917 59061397783987500793203719)
  ·
    refine ⟨88592096675981251189805579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59061397783987500793203719 88592096675981251189805579)
    ·
      refine ⟨132888145013971876784708369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88592096675981251189805579 132888145013971876784708369)
      ·
        refine ⟨99666108760478907588531277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132888145013971876784708369 99666108760478907588531277)
        ·
          refine ⟨37374790785179590345699229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99666108760478907588531277 37374790785179590345699229)
          ·
            refine ⟨14015546544442346379637211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37374790785179590345699229 14015546544442346379637211)
            ·
              refine ⟨21023319816663519569455817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14015546544442346379637211 21023319816663519569455817)
              ·
                refine ⟨15767489862497639677091863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21023319816663519569455817 15767489862497639677091863)
                ·
                  refine ⟨23651234793746459515637795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15767489862497639677091863 23651234793746459515637795)
                  ·
                    refine ⟨35476852190619689273456693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23651234793746459515637795 35476852190619689273456693)
                    ·
                      refine ⟨3325954892870595869386565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35476852190619689273456693 3325954892870595869386565)
                      ·
                        rfl

theorem cell23_6477274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_6477274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477274 prefixEnd_6477274 := by exact prefixLift 6477274
  have htrace : WordTrace (prefixWord ++ tailWord_6477274) baseStart_6477274 baseEnd_6477274 := by
    simpa [prefixWord, tailWord_6477274, baseEnd_6477274] using wordTrace_append hprefix tailTrace_6477274
  have hstable : (prefixWord ++ tailWord_6477274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477274).length < 2 ^ (prefixWord ++ tailWord_6477274).sum := by decide
  have hdescent : baseEnd_6477274 < baseStart_6477274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477317 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_6477317 : Nat := 118140960795 + 6477317 * 2 ^ 59
def prefixEnd_6477317 : Nat := 4983230072969 + 3 ^ 40 * 6477317 * 2
def baseEnd_6477317 : Nat := 3325976972538739201148867

theorem tailTrace_6477317 : CollatzResearch.WordTrace tailWord_6477317 prefixEnd_6477317 3325976972538739201148867 := by
  unfold tailWord_6477317
  simp only [CollatzResearch.WordTrace]
  refine ⟨236247159474794221516630205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157498106316529481011086803 236247159474794221516630205)
  ·
    refine ⟨88592684803047833068736327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236247159474794221516630205 88592684803047833068736327)
    ·
      refine ⟨132889027204571749603104491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88592684803047833068736327 132889027204571749603104491)
      ·
        refine ⟨199333540806857624404656737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132889027204571749603104491 199333540806857624404656737)
        ·
          refine ⟨149500155605143218303492553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199333540806857624404656737 149500155605143218303492553)
          ·
            refine ⟨112125116703857413727619415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149500155605143218303492553 112125116703857413727619415)
            ·
              refine ⟨168187675055786120591429123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112125116703857413727619415 168187675055786120591429123)
              ·
                refine ⟨252281512583679180887143685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168187675055786120591429123 252281512583679180887143685)
                ·
                  refine ⟨47302783609439846416339441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252281512583679180887143685 47302783609439846416339441)
                  ·
                    refine ⟨35477087707079884812254581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47302783609439846416339441 35477087707079884812254581)
                    ·
                      refine ⟨3325976972538739201148867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35477087707079884812254581 3325976972538739201148867)
                      ·
                        rfl

theorem cell23_6477317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_6477317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477317 prefixEnd_6477317 := by exact prefixLift 6477317
  have htrace : WordTrace (prefixWord ++ tailWord_6477317) baseStart_6477317 baseEnd_6477317 := by
    simpa [prefixWord, tailWord_6477317, baseEnd_6477317] using wordTrace_append hprefix tailTrace_6477317
  have hstable : (prefixWord ++ tailWord_6477317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477317).length < 2 ^ (prefixWord ++ tailWord_6477317).sum := by decide
  have hdescent : baseEnd_6477317 < baseStart_6477317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477321 : List Nat := [1, 2, 1, 1, 3, 1, 4, 4, 2, 1, 3]
def baseStart_6477321 : Nat := 118140960795 + 6477321 * 2 ^ 59
def prefixEnd_6477321 : Nat := 4983230072969 + 3 ^ 40 * 6477321 * 2
def baseEnd_6477321 : Nat := 3325979026461357185498849

theorem tailTrace_6477321 : CollatzResearch.WordTrace tailWord_6477321 prefixEnd_6477321 3325979026461357185498849 := by
  unfold tailWord_6477321
  simp only [CollatzResearch.WordTrace]
  refine ⟨236247305366779730199775817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157498203577853153466517211 236247305366779730199775817)
  ·
    refine ⟨177185479025084797649831863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236247305366779730199775817 177185479025084797649831863)
    ·
      refine ⟨265778218537627196474747795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177185479025084797649831863 265778218537627196474747795)
      ·
        refine ⟨398667327806440794712121693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265778218537627196474747795 398667327806440794712121693)
        ·
          refine ⟨149500247927415298017045635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398667327806440794712121693 149500247927415298017045635)
          ·
            refine ⟨224250371891122947025568453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149500247927415298017045635 224250371891122947025568453)
            ·
              refine ⟨42046944729585552567294085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224250371891122947025568453 42046944729585552567294085)
              ·
                refine ⟨7883802136797291106367641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42046944729585552567294085 7883802136797291106367641)
                ·
                  refine ⟨5912851602597968329775731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7883802136797291106367641 5912851602597968329775731)
                  ·
                    refine ⟨8869277403896952494663597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5912851602597968329775731 8869277403896952494663597)
                    ·
                      refine ⟨3325979026461357185498849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8869277403896952494663597 3325979026461357185498849)
                      ·
                        rfl

theorem cell23_6477321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 1, 3].length) (baseStart_6477321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477321 prefixEnd_6477321 := by exact prefixLift 6477321
  have htrace : WordTrace (prefixWord ++ tailWord_6477321) baseStart_6477321 baseEnd_6477321 := by
    simpa [prefixWord, tailWord_6477321, baseEnd_6477321] using wordTrace_append hprefix tailTrace_6477321
  have hstable : (prefixWord ++ tailWord_6477321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477321).length < 2 ^ (prefixWord ++ tailWord_6477321).sum := by decide
  have hdescent : baseEnd_6477321 < baseStart_6477321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477322 : List Nat := [3, 1, 2, 2, 2, 3, 3, 2, 1, 2, 2]
def baseStart_6477322 : Nat := 118140960795 + 6477322 * 2 ^ 59
def prefixEnd_6477322 : Nat := 4983230072969 + 3 ^ 40 * 6477322 * 2
def baseEnd_6477322 : Nat := 3325979539942011681586345

theorem tailTrace_6477322 : CollatzResearch.WordTrace tailWord_6477322 prefixEnd_6477322 3325979539942011681586345 := by
  unfold tailWord_6477322
  simp only [CollatzResearch.WordTrace]
  refine ⟨59061835459944026842640555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157498227893184071580374813 59061835459944026842640555)
  ·
    refine ⟨88592753189916040263960833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59061835459944026842640555 88592753189916040263960833)
    ·
      refine ⟨66444564892437030197970625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88592753189916040263960833 66444564892437030197970625)
      ·
        refine ⟨49833423669327772648477969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66444564892437030197970625 49833423669327772648477969)
        ·
          refine ⟨37375067751995829486358477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49833423669327772648477969 37375067751995829486358477)
          ·
            refine ⟨14015650406998436057384429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37375067751995829486358477 14015650406998436057384429)
            ·
              refine ⟨5255868902624413521519161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14015650406998436057384429 5255868902624413521519161)
              ·
                refine ⟨3941901676968310141139371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5255868902624413521519161 3941901676968310141139371)
                ·
                  refine ⟨5912852515452465211709057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941901676968310141139371 5912852515452465211709057)
                  ·
                    refine ⟨4434639386589348908781793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5912852515452465211709057 4434639386589348908781793)
                    ·
                      refine ⟨3325979539942011681586345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434639386589348908781793 3325979539942011681586345)
                      ·
                        rfl

theorem cell23_6477322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_6477322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477322 prefixEnd_6477322 := by exact prefixLift 6477322
  have htrace : WordTrace (prefixWord ++ tailWord_6477322) baseStart_6477322 baseEnd_6477322 := by
    simpa [prefixWord, tailWord_6477322, baseEnd_6477322] using wordTrace_append hprefix tailTrace_6477322
  have hstable : (prefixWord ++ tailWord_6477322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477322).length < 2 ^ (prefixWord ++ tailWord_6477322).sum := by decide
  have hdescent : baseEnd_6477322 < baseStart_6477322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477332 : List Nat := [2, 4, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_6477332 : Nat := 118140960795 + 6477332 * 2 ^ 59
def prefixEnd_6477332 : Nat := 4983230072969 + 3 ^ 40 * 6477332 * 2
def baseEnd_6477332 : Nat := 1108661558249518880820433

theorem tailTrace_6477332 : CollatzResearch.WordTrace tailWord_6477332 prefixEnd_6477332 1108661558249518880820433 := by
  unfold tailWord_6477332
  simp only [CollatzResearch.WordTrace]
  refine ⟨118123853284869939539213125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157498471046493252718950833 118123853284869939539213125)
  ·
    refine ⟨22148222490913113663602461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118123853284869939539213125 22148222490913113663602461)
    ·
      refine ⟨8305583434092417623850923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22148222490913113663602461 8305583434092417623850923)
      ·
        refine ⟨12458375151138626435776385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8305583434092417623850923 12458375151138626435776385)
        ·
          refine ⟨9343781363353969826832289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12458375151138626435776385 9343781363353969826832289)
          ·
            refine ⟨7007836022515477370124217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9343781363353969826832289 7007836022515477370124217)
            ·
              refine ⟨5255877016886608027593163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7007836022515477370124217 5255877016886608027593163)
              ·
                refine ⟨7883815525329912041389745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255877016886608027593163 7883815525329912041389745)
                ·
                  refine ⟨5912861643997434031042309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7883815525329912041389745 5912861643997434031042309)
                  ·
                    refine ⟨1108661558249518880820433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5912861643997434031042309 1108661558249518880820433)
                    ·
                      rfl

theorem cell23_6477332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_6477332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477332 prefixEnd_6477332 := by exact prefixLift 6477332
  have htrace : WordTrace (prefixWord ++ tailWord_6477332) baseStart_6477332 baseEnd_6477332 := by
    simpa [prefixWord, tailWord_6477332, baseEnd_6477332] using wordTrace_append hprefix tailTrace_6477332
  have hstable : (prefixWord ++ tailWord_6477332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477332).length < 2 ^ (prefixWord ++ tailWord_6477332).sum := by decide
  have hdescent : baseEnd_6477332 < baseStart_6477332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477342 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_6477342 : Nat := 118140960795 + 6477342 * 2 ^ 59
def prefixEnd_6477342 : Nat := 4983230072969 + 3 ^ 40 * 6477342 * 2
def baseEnd_6477342 : Nat := 3325989809555101603336253

theorem tailTrace_6477342 : CollatzResearch.WordTrace tailWord_6477342 prefixEnd_6477342 3325989809555101603336253 := by
  unfold tailWord_6477342
  simp only [CollatzResearch.WordTrace]
  refine ⟨29531008912462956348286285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157498714199802433857526853 29531008912462956348286285)
  ·
    refine ⟨11074128342173608630607357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29531008912462956348286285 11074128342173608630607357)
    ·
      refine ⟨4152798128315103236477759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11074128342173608630607357 4152798128315103236477759)
      ·
        refine ⟨6229197192472654854716639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4152798128315103236477759 6229197192472654854716639)
        ·
          refine ⟨9343795788708982282074959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6229197192472654854716639 9343795788708982282074959)
          ·
            refine ⟨14015693683063473423112439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9343795788708982282074959 14015693683063473423112439)
            ·
              refine ⟨21023540524595210134668659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14015693683063473423112439 21023540524595210134668659)
              ·
                refine ⟨31535310786892815202002989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21023540524595210134668659 31535310786892815202002989)
                ·
                  refine ⟨11825741545084805700751121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31535310786892815202002989 11825741545084805700751121)
                  ·
                    refine ⟨8869306158813604275563341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11825741545084805700751121 8869306158813604275563341)
                    ·
                      refine ⟨3325989809555101603336253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8869306158813604275563341 3325989809555101603336253)
                      ·
                        rfl

theorem cell23_6477342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_6477342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477342 prefixEnd_6477342 := by exact prefixLift 6477342
  have htrace : WordTrace (prefixWord ++ tailWord_6477342) baseStart_6477342 baseEnd_6477342 := by
    simpa [prefixWord, tailWord_6477342, baseEnd_6477342] using wordTrace_append hprefix tailTrace_6477342
  have hstable : (prefixWord ++ tailWord_6477342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477342).length < 2 ^ (prefixWord ++ tailWord_6477342).sum := by decide
  have hdescent : baseEnd_6477342 < baseStart_6477342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477365 : List Nat := [1, 3, 3, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_6477365 : Nat := 118140960795 + 6477365 * 2 ^ 59
def prefixEnd_6477365 : Nat := 4983230072969 + 3 ^ 40 * 6477365 * 2
def baseEnd_6477365 : Nat := 3326001619610155013348647

theorem tailTrace_6477365 : CollatzResearch.WordTrace tailWord_6477365 prefixEnd_6477365 3326001619610155013348647 := by
  unfold tailWord_6477365
  simp only [CollatzResearch.WordTrace]
  refine ⟨236248910178620325714377549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157499273452413550476251699 236248910178620325714377549)
  ·
    refine ⟨88593341316982622142891581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236248910178620325714377549 88593341316982622142891581)
    ·
      refine ⟨33222502993868483303584343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88593341316982622142891581 33222502993868483303584343)
      ·
        refine ⟨49833754490802724955376515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33222502993868483303584343 49833754490802724955376515)
        ·
          refine ⟨74750631736204087433064773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49833754490802724955376515 74750631736204087433064773)
          ·
            refine ⟨14015743450538266393699645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74750631736204087433064773 14015743450538266393699645)
            ·
              refine ⟨5255903793951849897637367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14015743450538266393699645 5255903793951849897637367)
              ·
                refine ⟨7883855690927774846456051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255903793951849897637367 7883855690927774846456051)
                ·
                  refine ⟨11825783536391662269684077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7883855690927774846456051 11825783536391662269684077)
                  ·
                    refine ⟨4434668826146873351131529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11825783536391662269684077 4434668826146873351131529)
                    ·
                      refine ⟨3326001619610155013348647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434668826146873351131529 3326001619610155013348647)
                      ·
                        rfl

theorem cell23_6477365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_6477365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477365 prefixEnd_6477365 := by exact prefixLift 6477365
  have htrace : WordTrace (prefixWord ++ tailWord_6477365) baseStart_6477365 baseEnd_6477365 := by
    simpa [prefixWord, tailWord_6477365, baseEnd_6477365] using wordTrace_append hprefix tailTrace_6477365
  have hstable : (prefixWord ++ tailWord_6477365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477365).length < 2 ^ (prefixWord ++ tailWord_6477365).sum := by decide
  have hdescent : baseEnd_6477365 < baseStart_6477365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477387 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 8]
def baseStart_6477387 : Nat := 118140960795 + 6477387 * 2 ^ 59
def prefixEnd_6477387 : Nat := 4983230072969 + 3 ^ 40 * 6477387 * 2
def baseEnd_6477387 : Nat := 3326012916184553927273545

theorem tailTrace_6477387 : CollatzResearch.WordTrace tailWord_6477387 prefixEnd_6477387 3326012916184553927273545 := by
  unfold tailWord_6477387
  simp only [CollatzResearch.WordTrace]
  refine ⟨236249712584540623471678415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157499808389693748981118943 236249712584540623471678415)
  ·
    refine ⟨354374568876810935207517623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236249712584540623471678415 354374568876810935207517623)
    ·
      refine ⟨531561853315216402811276435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354374568876810935207517623 531561853315216402811276435)
      ·
        refine ⟨797342779972824604216914653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531561853315216402811276435 797342779972824604216914653)
        ·
          refine ⟨299003542489809226581342995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 797342779972824604216914653 299003542489809226581342995)
          ·
            refine ⟨448505313734713839872014493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299003542489809226581342995 448505313734713839872014493)
            ·
              refine ⟨168189492650517689952005435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 448505313734713839872014493 168189492650517689952005435)
              ·
                refine ⟨252284238975776534928008153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168189492650517689952005435 252284238975776534928008153)
                ·
                  refine ⟨189213179231832401196006115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252284238975776534928008153 189213179231832401196006115)
                  ·
                    refine ⟨283819768847748601794009173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 189213179231832401196006115 283819768847748601794009173)
                    ·
                      refine ⟨3326012916184553927273545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 283819768847748601794009173 3326012916184553927273545)
                      ·
                        rfl

theorem cell23_6477387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_6477387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477387 prefixEnd_6477387 := by exact prefixLift 6477387
  have htrace : WordTrace (prefixWord ++ tailWord_6477387) baseStart_6477387 baseEnd_6477387 := by
    simpa [prefixWord, tailWord_6477387, baseEnd_6477387] using wordTrace_append hprefix tailTrace_6477387
  have hstable : (prefixWord ++ tailWord_6477387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477387).length < 2 ^ (prefixWord ++ tailWord_6477387).sum := by decide
  have hdescent : baseEnd_6477387 < baseStart_6477387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477418 : List Nat := [3, 1, 3, 2, 1, 3, 2, 3, 5]
def baseStart_6477418 : Nat := 118140960795 + 6477418 * 2 ^ 59
def prefixEnd_6477418 : Nat := 4983230072969 + 3 ^ 40 * 6477418 * 2
def baseEnd_6477418 : Nat := 369558759342760367331767

theorem tailTrace_6477418 : CollatzResearch.WordTrace tailWord_6477418 prefixEnd_6477418 369558759342760367331767 := by
  unfold tailWord_6477418
  simp only [CollatzResearch.WordTrace]
  refine ⟨59062710811857078941514227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157500562164952210510704605 59062710811857078941514227)
  ·
    refine ⟨88594066217785618412271341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59062710811857078941514227 88594066217785618412271341)
    ·
      refine ⟨33222774831669606904601753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88594066217785618412271341 33222774831669606904601753)
      ·
        refine ⟨24917081123752205178451315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33222774831669606904601753 24917081123752205178451315)
        ·
          refine ⟨37375621685628307767676973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24917081123752205178451315 37375621685628307767676973)
          ·
            refine ⟨14015858132110615412878865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37375621685628307767676973 14015858132110615412878865)
            ·
              refine ⟨10511893599082961559659149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14015858132110615412878865 10511893599082961559659149)
              ·
                refine ⟨3941960099656110584872181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10511893599082961559659149 3941960099656110584872181)
                ·
                  refine ⟨369558759342760367331767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3941960099656110584872181 369558759342760367331767)
                  ·
                    rfl

theorem cell23_6477418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 5].length) (baseStart_6477418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477418 prefixEnd_6477418 := by exact prefixLift 6477418
  have htrace : WordTrace (prefixWord ++ tailWord_6477418) baseStart_6477418 baseEnd_6477418 := by
    simpa [prefixWord, tailWord_6477418, baseEnd_6477418] using wordTrace_append hprefix tailTrace_6477418
  have hstable : (prefixWord ++ tailWord_6477418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477418).length < 2 ^ (prefixWord ++ tailWord_6477418).sum := by decide
  have hdescent : baseEnd_6477418 < baseStart_6477418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477451 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 2, 4, 2]
def baseStart_6477451 : Nat := 118140960795 + 6477451 * 2 ^ 59
def prefixEnd_6477451 : Nat := 4983230072969 + 3 ^ 40 * 6477451 * 2
def baseEnd_6477451 : Nat := 3326045778946441676873251

theorem tailTrace_6477451 : CollatzResearch.WordTrace tailWord_6477451 prefixEnd_6477451 3326045778946441676873251 := by
  unfold tailWord_6477451
  simp only [CollatzResearch.WordTrace]
  refine ⟨236252046856308762402008207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157501364570872508268005471 236252046856308762402008207)
  ·
    refine ⟨354378070284463143603012311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236252046856308762402008207 354378070284463143603012311)
    ·
      refine ⟨531567105426694715404518467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354378070284463143603012311 531567105426694715404518467)
      ·
        refine ⟨797350658140042073106777701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531567105426694715404518467 797350658140042073106777701)
        ·
          refine ⟨149503248401257888707520819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 797350658140042073106777701 149503248401257888707520819)
          ·
            refine ⟨224254872601886833061281229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149503248401257888707520819 224254872601886833061281229)
            ·
              refine ⟨84095577225707562397980461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224254872601886833061281229 84095577225707562397980461)
              ·
                refine ⟨31535841459640335899242673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84095577225707562397980461 31535841459640335899242673)
                ·
                  refine ⟨23651881094730251924432005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31535841459640335899242673 23651881094730251924432005)
                  ·
                    refine ⟨4434727705261922235831001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23651881094730251924432005 4434727705261922235831001)
                    ·
                      refine ⟨3326045778946441676873251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434727705261922235831001 3326045778946441676873251)
                      ·
                        rfl

theorem cell23_6477451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 4, 2].length) (baseStart_6477451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477451 prefixEnd_6477451 := by exact prefixLift 6477451
  have htrace : WordTrace (prefixWord ++ tailWord_6477451) baseStart_6477451 baseEnd_6477451 := by
    simpa [prefixWord, tailWord_6477451, baseEnd_6477451] using wordTrace_append hprefix tailTrace_6477451
  have hstable : (prefixWord ++ tailWord_6477451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477451).length < 2 ^ (prefixWord ++ tailWord_6477451).sum := by decide
  have hdescent : baseEnd_6477451 < baseStart_6477451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477518 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_6477518 : Nat := 118140960795 + 6477518 * 2 ^ 59
def prefixEnd_6477518 : Nat := 4983230072969 + 3 ^ 40 * 6477518 * 2
def baseEnd_6477518 : Nat := 3326080182150292914735443

theorem tailTrace_6477518 : CollatzResearch.WordTrace tailWord_6477518 prefixEnd_6477518 3326080182150292914735443 := by
  unfold tailWord_6477518
  simp only [CollatzResearch.WordTrace]
  refine ⟨29531811318383254105587151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157502993698044021896464805 29531811318383254105587151)
  ·
    refine ⟨44297716977574881158380727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29531811318383254105587151 44297716977574881158380727)
    ·
      refine ⟨66446575466362321737571091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44297716977574881158380727 66446575466362321737571091)
      ·
        refine ⟨99669863199543482606356637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66446575466362321737571091 99669863199543482606356637)
        ·
          refine ⟨37376198699828805977383739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99669863199543482606356637 37376198699828805977383739)
          ·
            refine ⟨56064298049743208966075609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37376198699828805977383739 56064298049743208966075609)
            ·
              refine ⟨42048223537307406724556707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56064298049743208966075609 42048223537307406724556707)
              ·
                refine ⟨63072335305961110086835061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42048223537307406724556707 63072335305961110086835061)
                ·
                  refine ⟨5913031434933854070640787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63072335305961110086835061 5913031434933854070640787)
                  ·
                    refine ⟨8869547152400781105961181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5913031434933854070640787 8869547152400781105961181)
                    ·
                      refine ⟨3326080182150292914735443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8869547152400781105961181 3326080182150292914735443)
                      ·
                        rfl

theorem cell23_6477518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_6477518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477518 prefixEnd_6477518 := by exact prefixLift 6477518
  have htrace : WordTrace (prefixWord ++ tailWord_6477518) baseStart_6477518 baseEnd_6477518 := by
    simpa [prefixWord, tailWord_6477518, baseEnd_6477518] using wordTrace_append hprefix tailTrace_6477518
  have hstable : (prefixWord ++ tailWord_6477518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477518).length < 2 ^ (prefixWord ++ tailWord_6477518).sum := by decide
  have hdescent : baseEnd_6477518 < baseStart_6477518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477521 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 3, 5]
def baseStart_6477521 : Nat := 118140960795 + 6477521 * 2 ^ 59
def prefixEnd_6477521 : Nat := 4983230072969 + 3 ^ 40 * 6477521 * 2
def baseEnd_6477521 : Nat := 1108693907530752134332643

theorem tailTrace_6477521 : CollatzResearch.WordTrace tailWord_6477521 prefixEnd_6477521 1108693907530752134332643 := by
  unfold tailWord_6477521
  simp only [CollatzResearch.WordTrace]
  refine ⟨236254599966055164357056417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157503066644036776238037611 236254599966055164357056417)
  ·
    refine ⟨177190949974541373267792313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236254599966055164357056417 177190949974541373267792313)
    ·
      refine ⟨132893212480906029950844235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177190949974541373267792313 132893212480906029950844235)
      ·
        refine ⟨199339818721359044926266353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132893212480906029950844235 199339818721359044926266353)
        ·
          refine ⟨149504864041019283694699765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199339818721359044926266353 149504864041019283694699765)
          ·
            refine ⟨14016081003845557846378103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149504864041019283694699765 14016081003845557846378103)
            ·
              refine ⟨21024121505768336769567155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14016081003845557846378103 21024121505768336769567155)
              ·
                refine ⟨31536182258652505154350733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21024121505768336769567155 31536182258652505154350733)
                ·
                  refine ⟨11826068346994689432881525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31536182258652505154350733 11826068346994689432881525)
                  ·
                    refine ⟨1108693907530752134332643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11826068346994689432881525 1108693907530752134332643)
                    ·
                      rfl

theorem cell23_6477521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_6477521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477521 prefixEnd_6477521 := by exact prefixLift 6477521
  have htrace : WordTrace (prefixWord ++ tailWord_6477521) baseStart_6477521 baseEnd_6477521 := by
    simpa [prefixWord, tailWord_6477521, baseEnd_6477521] using wordTrace_append hprefix tailTrace_6477521
  have hstable : (prefixWord ++ tailWord_6477521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477521).length < 2 ^ (prefixWord ++ tailWord_6477521).sum := by decide
  have hdescent : baseEnd_6477521 < baseStart_6477521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477535 : List Nat := [1, 1, 2, 3, 2, 2, 2, 5, 1, 1, 3]
def baseStart_6477535 : Nat := 118140960795 + 6477535 * 2 ^ 59
def prefixEnd_6477535 : Nat := 4983230072969 + 3 ^ 40 * 6477535 * 2
def baseEnd_6477535 : Nat := 3326088911321419348222865

theorem tailTrace_6477535 : CollatzResearch.WordTrace tailWord_6477535 prefixEnd_6477535 3326088911321419348222865 := by
  unfold tailWord_6477535
  simp only [CollatzResearch.WordTrace]
  refine ⟨236255110588004444748066059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157503407058669629832044039 236255110588004444748066059)
  ·
    refine ⟨354382665882006667122099089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236255110588004444748066059 354382665882006667122099089)
    ·
      refine ⟨265786999411505000341574317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354382665882006667122099089 265786999411505000341574317)
      ·
        refine ⟨99670124779314375128090369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265786999411505000341574317 99670124779314375128090369)
        ·
          refine ⟨74752593584485781346067777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99670124779314375128090369 74752593584485781346067777)
          ·
            refine ⟨56064445188364336009550833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74752593584485781346067777 56064445188364336009550833)
            ·
              refine ⟨42048333891273252007163125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56064445188364336009550833 42048333891273252007163125)
              ·
                refine ⟨3942031302306867375671543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42048333891273252007163125 3942031302306867375671543)
                ·
                  refine ⟨5913046953460301063507315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3942031302306867375671543 5913046953460301063507315)
                  ·
                    refine ⟨8869570430190451595260973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5913046953460301063507315 8869570430190451595260973)
                    ·
                      refine ⟨3326088911321419348222865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8869570430190451595260973 3326088911321419348222865)
                      ·
                        rfl

theorem cell23_6477535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_6477535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477535 prefixEnd_6477535 := by exact prefixLift 6477535
  have htrace : WordTrace (prefixWord ++ tailWord_6477535) baseStart_6477535 baseEnd_6477535 := by
    simpa [prefixWord, tailWord_6477535, baseEnd_6477535] using wordTrace_append hprefix tailTrace_6477535
  have hstable : (prefixWord ++ tailWord_6477535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477535).length < 2 ^ (prefixWord ++ tailWord_6477535).sum := by decide
  have hdescent : baseEnd_6477535 < baseStart_6477535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477558 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_6477558 : Nat := 118140960795 + 6477558 * 2 ^ 59
def prefixEnd_6477558 : Nat := 4983230072969 + 3 ^ 40 * 6477558 * 2
def baseEnd_6477558 : Nat := 3326100721376472758235259

theorem tailTrace_6477558 : CollatzResearch.WordTrace tailWord_6477558 prefixEnd_6477558 3326100721376472758235259 := by
  unfold tailWord_6477558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14765996841682569979759583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157503966311280746450768885 14765996841682569979759583)
  ·
    refine ⟨22148995262523854969639375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14765996841682569979759583 22148995262523854969639375)
    ·
      refine ⟨33223492893785782454459063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22148995262523854969639375 33223492893785782454459063)
      ·
        refine ⟨49835239340678673681688595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33223492893785782454459063 49835239340678673681688595)
        ·
          refine ⟨74752859011018010522532893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49835239340678673681688595 74752859011018010522532893)
          ·
            refine ⟨28032322129131753945949835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74752859011018010522532893 28032322129131753945949835)
            ·
              refine ⟨42048483193697630918924753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28032322129131753945949835 42048483193697630918924753)
              ·
                refine ⟨31536362395273223189193565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42048483193697630918924753 31536362395273223189193565)
                ·
                  refine ⟨11826135898227458695947587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31536362395273223189193565 11826135898227458695947587)
                  ·
                    refine ⟨17739203847341188043921381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11826135898227458695947587 17739203847341188043921381)
                    ·
                      refine ⟨3326100721376472758235259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17739203847341188043921381 3326100721376472758235259)
                      ·
                        rfl

theorem cell23_6477558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_6477558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477558 prefixEnd_6477558 := by exact prefixLift 6477558
  have htrace : WordTrace (prefixWord ++ tailWord_6477558) baseStart_6477558 baseEnd_6477558 := by
    simpa [prefixWord, tailWord_6477558, baseEnd_6477558] using wordTrace_append hprefix tailTrace_6477558
  have hstable : (prefixWord ++ tailWord_6477558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477558).length < 2 ^ (prefixWord ++ tailWord_6477558).sum := by decide
  have hdescent : baseEnd_6477558 < baseStart_6477558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477571 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 4]
def baseStart_6477571 : Nat := 118140960795 + 6477571 * 2 ^ 59
def prefixEnd_6477571 : Nat := 4983230072969 + 3 ^ 40 * 6477571 * 2
def baseEnd_6477571 : Nat := 3326107396624981207372699

theorem tailTrace_6477571 : CollatzResearch.WordTrace tailWord_6477571 prefixEnd_6477571 3326107396624981207372699 := by
  unfold tailWord_6477571
  simp only [CollatzResearch.WordTrace]
  refine ⟨236256423615874022896376567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157504282410582681930917711 236256423615874022896376567)
  ·
    refine ⟨354384635423811034344564851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236256423615874022896376567 354384635423811034344564851)
    ·
      refine ⟨531576953135716551516847277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354384635423811034344564851 531576953135716551516847277)
      ·
        refine ⟨199341357425893706818817729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 531576953135716551516847277 199341357425893706818817729)
        ·
          refine ⟨149506018069420280114113297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199341357425893706818817729 149506018069420280114113297)
          ·
            refine ⟨112129513552065210085584973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149506018069420280114113297 112129513552065210085584973)
            ·
              refine ⟨42048567582024453782094365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112129513552065210085584973 42048567582024453782094365)
              ·
                refine ⟨15768212843259170168285387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42048567582024453782094365 15768212843259170168285387)
                ·
                  refine ⟨23652319264888755252428081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15768212843259170168285387 23652319264888755252428081)
                  ·
                    refine ⟨17739239448666566439321061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23652319264888755252428081 17739239448666566439321061)
                    ·
                      refine ⟨3326107396624981207372699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17739239448666566439321061 3326107396624981207372699)
                      ·
                        rfl

theorem cell23_6477571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_6477571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477571 prefixEnd_6477571 := by exact prefixLift 6477571
  have htrace : WordTrace (prefixWord ++ tailWord_6477571) baseStart_6477571 baseEnd_6477571 := by
    simpa [prefixWord, tailWord_6477571, baseEnd_6477571] using wordTrace_append hprefix tailTrace_6477571
  have hstable : (prefixWord ++ tailWord_6477571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477571).length < 2 ^ (prefixWord ++ tailWord_6477571).sum := by decide
  have hdescent : baseEnd_6477571 < baseStart_6477571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477578 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_6477578 : Nat := 118140960795 + 6477578 * 2 ^ 59
def prefixEnd_6477578 : Nat := 4983230072969 + 3 ^ 40 * 6477578 * 2
def baseEnd_6477578 : Nat := 3326110990989562679985167

theorem tailTrace_6477578 : CollatzResearch.WordTrace tailWord_6477578 prefixEnd_6477578 3326110990989562679985167 := by
  unfold tailWord_6477578
  simp only [CollatzResearch.WordTrace]
  refine ⟨59064169731712165772970347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157504452617899108727920925 59064169731712165772970347)
  ·
    refine ⟨88596254597568248659455521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59064169731712165772970347 88596254597568248659455521)
    ·
      refine ⟨66447190948176186494591641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88596254597568248659455521 66447190948176186494591641)
      ·
        refine ⟨49835393211132139870943731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66447190948176186494591641 49835393211132139870943731)
        ·
          refine ⟨74753089816698209806415597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49835393211132139870943731 74753089816698209806415597)
          ·
            refine ⟨28032408681261828677405849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74753089816698209806415597 28032408681261828677405849)
            ·
              refine ⟨21024306510946371508054387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28032408681261828677405849 21024306510946371508054387)
              ·
                refine ⟨31536459766419557262081581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21024306510946371508054387 31536459766419557262081581)
                ·
                  refine ⟨11826172412407333973280593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31536459766419557262081581 11826172412407333973280593)
                  ·
                    refine ⟨8869629309305500479960445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11826172412407333973280593 8869629309305500479960445)
                    ·
                      refine ⟨3326110990989562679985167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8869629309305500479960445 3326110990989562679985167)
                      ·
                        rfl

theorem cell23_6477578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_6477578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477578 prefixEnd_6477578 := by exact prefixLift 6477578
  have htrace : WordTrace (prefixWord ++ tailWord_6477578) baseStart_6477578 baseEnd_6477578 := by
    simpa [prefixWord, tailWord_6477578, baseEnd_6477578] using wordTrace_append hprefix tailTrace_6477578
  have hstable : (prefixWord ++ tailWord_6477578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477578).length < 2 ^ (prefixWord ++ tailWord_6477578).sum := by decide
  have hdescent : baseEnd_6477578 < baseStart_6477578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477592 : List Nat := [2, 1, 2, 3, 1, 1, 3, 5, 1, 2, 2]
def baseStart_6477592 : Nat := 118140960795 + 6477592 * 2 ^ 59
def prefixEnd_6477592 : Nat := 4983230072969 + 3 ^ 40 * 6477592 * 2
def baseEnd_6477592 : Nat := 3326118179718725625210103

theorem tailTrace_6477592 : CollatzResearch.WordTrace tailWord_6477592 prefixEnd_6477592 3326118179718725625210103 := by
  unfold tailWord_6477592
  simp only [CollatzResearch.WordTrace]
  refine ⟨118128594774398971741445515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157504793032531962321927353 118128594774398971741445515)
  ·
    refine ⟨177192892161598457612168273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118128594774398971741445515 177192892161598457612168273)
    ·
      refine ⟨132894669121198843209126205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177192892161598457612168273 132894669121198843209126205)
      ·
        refine ⟨49835500920449566203422327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132894669121198843209126205 49835500920449566203422327)
        ·
          refine ⟨74753251380674349305133491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49835500920449566203422327 74753251380674349305133491)
          ·
            refine ⟨112129877071011523957700237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74753251380674349305133491 112129877071011523957700237)
            ·
              refine ⟨42048703901629321484137589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112129877071011523957700237 42048703901629321484137589)
              ·
                refine ⟨3942065990777748889137899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42048703901629321484137589 3942065990777748889137899)
                ·
                  refine ⟨5913098986166623333706849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3942065990777748889137899 5913098986166623333706849)
                  ·
                    refine ⟨4434824239624967500280137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5913098986166623333706849 4434824239624967500280137)
                    ·
                      refine ⟨3326118179718725625210103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434824239624967500280137 3326118179718725625210103)
                      ·
                        rfl

theorem cell23_6477592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_6477592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477592 prefixEnd_6477592 := by exact prefixLift 6477592
  have htrace : WordTrace (prefixWord ++ tailWord_6477592) baseStart_6477592 baseEnd_6477592 := by
    simpa [prefixWord, tailWord_6477592, baseEnd_6477592] using wordTrace_append hprefix tailTrace_6477592
  have hstable : (prefixWord ++ tailWord_6477592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477592).length < 2 ^ (prefixWord ++ tailWord_6477592).sum := by decide
  have hdescent : baseEnd_6477592 < baseStart_6477592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477622 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_6477622 : Nat := 118140960795 + 6477622 * 2 ^ 59
def prefixEnd_6477622 : Nat := 4983230072969 + 3 ^ 40 * 6477622 * 2
def baseEnd_6477622 : Nat := 3326133584138360507834965

theorem tailTrace_6477622 : CollatzResearch.WordTrace tailWord_6477622 prefixEnd_6477622 3326133584138360507834965 := by
  unfold tailWord_6477622
  simp only [CollatzResearch.WordTrace]
  refine ⟨14766142733668078662905195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157505522492459505737655413 14766142733668078662905195)
  ·
    refine ⟨22149214100502117994357793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14766142733668078662905195 22149214100502117994357793)
    ·
      refine ⟨16611910575376588495768345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22149214100502117994357793 16611910575376588495768345)
      ·
        refine ⟨12458932931532441371826259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16611910575376588495768345 12458932931532441371826259)
        ·
          refine ⟨18688399397298662057739389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12458932931532441371826259 18688399397298662057739389)
          ·
            refine ⟨7008149773986998271652271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18688399397298662057739389 7008149773986998271652271)
            ·
              refine ⟨10512224660980497407478407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7008149773986998271652271 10512224660980497407478407)
              ·
                refine ⟨15768336991470746111217611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10512224660980497407478407 15768336991470746111217611)
                ·
                  refine ⟨23652505487206119166826417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15768336991470746111217611 23652505487206119166826417)
                  ·
                    refine ⟨17739379115404589375119813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23652505487206119166826417 17739379115404589375119813)
                    ·
                      refine ⟨3326133584138360507834965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17739379115404589375119813 3326133584138360507834965)
                      ·
                        rfl

theorem cell23_6477622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_6477622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477622 prefixEnd_6477622 := by exact prefixLift 6477622
  have htrace : WordTrace (prefixWord ++ tailWord_6477622) baseStart_6477622 baseEnd_6477622 := by
    simpa [prefixWord, tailWord_6477622, baseEnd_6477622] using wordTrace_append hprefix tailTrace_6477622
  have hstable : (prefixWord ++ tailWord_6477622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477622).length < 2 ^ (prefixWord ++ tailWord_6477622).sum := by decide
  have hdescent : baseEnd_6477622 < baseStart_6477622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477635 : List Nat := [1, 1, 1, 3, 1, 5, 1, 4, 1, 3, 2]
def baseStart_6477635 : Nat := 118140960795 + 6477635 * 2 ^ 59
def prefixEnd_6477635 : Nat := 4983230072969 + 3 ^ 40 * 6477635 * 2
def baseEnd_6477635 : Nat := 3326140259386868956972405

theorem tailTrace_6477635 : CollatzResearch.WordTrace tailWord_6477635 prefixEnd_6477635 3326140259386868956972405 := by
  unfold tailWord_6477635
  simp only [CollatzResearch.WordTrace]
  refine ⟨236258757887642161826706359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157505838591761441217804239 236258757887642161826706359)
  ·
    refine ⟨354388136831463242740059539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236258757887642161826706359 354388136831463242740059539)
    ·
      refine ⟨531582205247194864110089309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354388136831463242740059539 531582205247194864110089309)
      ·
        refine ⟨199343326967698074041283491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 531582205247194864110089309 199343326967698074041283491)
        ·
          refine ⟨299014990451547111061925237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199343326967698074041283491 299014990451547111061925237)
          ·
            refine ⟨28032655354832541662055491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 299014990451547111061925237 28032655354832541662055491)
            ·
              refine ⟨42048983032248812493083237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28032655354832541662055491 42048983032248812493083237)
              ·
                refine ⟨7884184318546652342453107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42048983032248812493083237 7884184318546652342453107)
                ·
                  refine ⟨11826276477819978513679661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7884184318546652342453107 11826276477819978513679661)
                  ·
                    refine ⟨4434853679182491942629873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11826276477819978513679661 4434853679182491942629873)
                    ·
                      refine ⟨3326140259386868956972405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434853679182491942629873 3326140259386868956972405)
                      ·
                        rfl

theorem cell23_6477635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 3, 2].length) (baseStart_6477635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477635 prefixEnd_6477635 := by exact prefixLift 6477635
  have htrace : WordTrace (prefixWord ++ tailWord_6477635) baseStart_6477635 baseEnd_6477635 := by
    simpa [prefixWord, tailWord_6477635, baseEnd_6477635] using wordTrace_append hprefix tailTrace_6477635
  have hstable : (prefixWord ++ tailWord_6477635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477635).length < 2 ^ (prefixWord ++ tailWord_6477635).sum := by decide
  have hdescent : baseEnd_6477635 < baseStart_6477635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477648 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 3, 4, 2]
def baseStart_6477648 : Nat := 118140960795 + 6477648 * 2 ^ 59
def prefixEnd_6477648 : Nat := 4983230072969 + 3 ^ 40 * 6477648 * 2
def baseEnd_6477648 : Nat := 3326146934635377406109845

theorem tailTrace_6477648 : CollatzResearch.WordTrace tailWord_6477648 prefixEnd_6477648 3326146934635377406109845 := by
  unfold tailWord_6477648
  simp only [CollatzResearch.WordTrace]
  refine ⟨118129616018297532523464799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157506154691063376697953065 118129616018297532523464799)
  ·
    refine ⟨177194424027446298785197199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118129616018297532523464799 177194424027446298785197199)
    ·
      refine ⟨265791636041169448177795799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177194424027446298785197199 265791636041169448177795799)
      ·
        refine ⟨398687454061754172266693699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265791636041169448177795799 398687454061754172266693699)
        ·
          refine ⟨598031181092631258400040549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398687454061754172266693699 598031181092631258400040549)
          ·
            refine ⟨112130846454868360950007603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 598031181092631258400040549 112130846454868360950007603)
            ·
              refine ⟨168196269682302541425011405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112130846454868360950007603 168196269682302541425011405)
              ·
                refine ⟨63073601130863453034379277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168196269682302541425011405 63073601130863453034379277)
                ·
                  refine ⟨23652600424073794887892229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63073601130863453034379277 23652600424073794887892229)
                  ·
                    refine ⟨4434862579513836541479793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23652600424073794887892229 4434862579513836541479793)
                    ·
                      refine ⟨3326146934635377406109845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434862579513836541479793 3326146934635377406109845)
                      ·
                        rfl

theorem cell23_6477648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 4, 2].length) (baseStart_6477648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477648 prefixEnd_6477648 := by exact prefixLift 6477648
  have htrace : WordTrace (prefixWord ++ tailWord_6477648) baseStart_6477648 baseEnd_6477648 := by
    simpa [prefixWord, tailWord_6477648, baseEnd_6477648] using wordTrace_append hprefix tailTrace_6477648
  have hstable : (prefixWord ++ tailWord_6477648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477648).length < 2 ^ (prefixWord ++ tailWord_6477648).sum := by decide
  have hdescent : baseEnd_6477648 < baseStart_6477648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477651 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 3]
def baseStart_6477651 : Nat := 118140960795 + 6477651 * 2 ^ 59
def prefixEnd_6477651 : Nat := 4983230072969 + 3 ^ 40 * 6477651 * 2
def baseEnd_6477651 : Nat := 3326148475077340894372331

theorem tailTrace_6477651 : CollatzResearch.WordTrace tailWord_6477651 prefixEnd_6477651 3326148475077340894372331 := by
  unfold tailWord_6477651
  simp only [CollatzResearch.WordTrace]
  refine ⟨236259341455584196559288807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157506227637056131039525871 236259341455584196559288807)
  ·
    refine ⟨354389012183376294838933211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236259341455584196559288807 354389012183376294838933211)
    ·
      refine ⟨531583518275064442258399817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354389012183376294838933211 531583518275064442258399817)
      ·
        refine ⟨398687638706298331693799863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531583518275064442258399817 398687638706298331693799863)
        ·
          refine ⟨598031458059447497540699795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398687638706298331693799863 598031458059447497540699795)
          ·
            refine ⟨897047187089171246311049693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598031458059447497540699795 897047187089171246311049693)
            ·
              refine ⟨336392695158439217366643635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 897047187089171246311049693 336392695158439217366643635)
              ·
                refine ⟨504589042737658826049965453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336392695158439217366643635 504589042737658826049965453)
                ·
                  refine ⟨189220891026622059768737045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504589042737658826049965453 189220891026622059768737045)
                  ·
                    refine ⟨8869729266872909051659549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 189220891026622059768737045 8869729266872909051659549)
                    ·
                      refine ⟨3326148475077340894372331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8869729266872909051659549 3326148475077340894372331)
                      ·
                        rfl

theorem cell23_6477651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 3].length) (baseStart_6477651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477651 prefixEnd_6477651 := by exact prefixLift 6477651
  have htrace : WordTrace (prefixWord ++ tailWord_6477651) baseStart_6477651 baseEnd_6477651 := by
    simpa [prefixWord, tailWord_6477651, baseEnd_6477651] using wordTrace_append hprefix tailTrace_6477651
  have hstable : (prefixWord ++ tailWord_6477651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477651).length < 2 ^ (prefixWord ++ tailWord_6477651).sum := by decide
  have hdescent : baseEnd_6477651 < baseStart_6477651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477652 : List Nat := [2, 4, 1, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_6477652 : Nat := 118140960795 + 6477652 * 2 ^ 59
def prefixEnd_6477652 : Nat := 4983230072969 + 3 ^ 40 * 6477652 * 2
def baseEnd_6477652 : Nat := 3326148988557995390459827

theorem tailTrace_6477652 : CollatzResearch.WordTrace tailWord_6477652 prefixEnd_6477652 3326148988557995390459827 := by
  unfold tailWord_6477652
  simp only [CollatzResearch.WordTrace]
  refine ⟨118129688964290286865037605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157506251952387049153383473 118129688964290286865037605)
  ·
    refine ⟨22149316680804428787194551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118129688964290286865037605 22149316680804428787194551)
    ·
      refine ⟨33223975021206643180791827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22149316680804428787194551 33223975021206643180791827)
      ·
        refine ⟨49835962531809964771187741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33223975021206643180791827 49835962531809964771187741)
        ·
          refine ⟨18688485949428736789195403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49835962531809964771187741 18688485949428736789195403)
          ·
            refine ⟨28032728924143105183793105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18688485949428736789195403 28032728924143105183793105)
            ·
              refine ⟨21024546693107328887844829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28032728924143105183793105 21024546693107328887844829)
              ·
                refine ⟨7884205009915248332941811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21024546693107328887844829 7884205009915248332941811)
                ·
                  refine ⟨11826307514872872499412717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7884205009915248332941811 11826307514872872499412717)
                  ·
                    refine ⟨4434865318077327187279769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11826307514872872499412717 4434865318077327187279769)
                    ·
                      refine ⟨3326148988557995390459827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434865318077327187279769 3326148988557995390459827)
                      ·
                        rfl

theorem cell23_6477652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_6477652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477652 prefixEnd_6477652 := by exact prefixLift 6477652
  have htrace : WordTrace (prefixWord ++ tailWord_6477652) baseStart_6477652 baseEnd_6477652 := by
    simpa [prefixWord, tailWord_6477652, baseEnd_6477652] using wordTrace_append hprefix tailTrace_6477652
  have hstable : (prefixWord ++ tailWord_6477652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477652).length < 2 ^ (prefixWord ++ tailWord_6477652).sum := by decide
  have hdescent : baseEnd_6477652 < baseStart_6477652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477665 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 4, 2, 2]
def baseStart_6477665 : Nat := 118140960795 + 6477665 * 2 ^ 59
def prefixEnd_6477665 : Nat := 4983230072969 + 3 ^ 40 * 6477665 * 2
def baseEnd_6477665 : Nat := 3326155663806503839597267

theorem tailTrace_6477665 : CollatzResearch.WordTrace tailWord_6477665 prefixEnd_6477665 3326155663806503839597267 := by
  unfold tailWord_6477665
  simp only [CollatzResearch.WordTrace]
  refine ⟨236259852077533476950298449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157506568051688984633532299 236259852077533476950298449)
  ·
    refine ⟨177194889058150107712723837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236259852077533476950298449 177194889058150107712723837)
    ·
      refine ⟨66448083396806290392271439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177194889058150107712723837 66448083396806290392271439)
      ·
        refine ⟨99672125095209435588407159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66448083396806290392271439 99672125095209435588407159)
        ·
          refine ⟨149508187642814153382610739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99672125095209435588407159 149508187642814153382610739)
          ·
            refine ⟨224262281464221230073916109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149508187642814153382610739 224262281464221230073916109)
            ·
              refine ⟨84098355549082961277718541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224262281464221230073916109 84098355549082961277718541)
              ·
                refine ⟨31536883330906110479144453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84098355549082961277718541 31536883330906110479144453)
                ·
                  refine ⟨5913165624544895714839585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31536883330906110479144453 5913165624544895714839585)
                  ·
                    refine ⟨4434874218408671786129689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5913165624544895714839585 4434874218408671786129689)
                    ·
                      refine ⟨3326155663806503839597267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434874218408671786129689 3326155663806503839597267)
                      ·
                        rfl

theorem cell23_6477665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_6477665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477665 prefixEnd_6477665 := by exact prefixLift 6477665
  have htrace : WordTrace (prefixWord ++ tailWord_6477665) baseStart_6477665 baseEnd_6477665 := by
    simpa [prefixWord, tailWord_6477665, baseEnd_6477665] using wordTrace_append hprefix tailTrace_6477665
  have hstable : (prefixWord ++ tailWord_6477665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477665).length < 2 ^ (prefixWord ++ tailWord_6477665).sum := by decide
  have hdescent : baseEnd_6477665 < baseStart_6477665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477686 : List Nat := [5, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_6477686 : Nat := 118140960795 + 6477686 * 2 ^ 59
def prefixEnd_6477686 : Nat := 4983230072969 + 3 ^ 40 * 6477686 * 2
def baseEnd_6477686 : Nat := 3326166446900248257434671

theorem tailTrace_6477686 : CollatzResearch.WordTrace tailWord_6477686 prefixEnd_6477686 3326166446900248257434671 := by
  unfold tailWord_6477686
  simp only [CollatzResearch.WordTrace]
  refine ⟨14766288625653587346050807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157507078673638265024541941 14766288625653587346050807)
  ·
    refine ⟨22149432938480381019076211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14766288625653587346050807 22149432938480381019076211)
    ·
      refine ⟨33224149407720571528614317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22149432938480381019076211 33224149407720571528614317)
      ·
        refine ⟨12459056027895214323230369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33224149407720571528614317 12459056027895214323230369)
        ·
          refine ⟨9344292020921410742422777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12459056027895214323230369 9344292020921410742422777)
          ·
            refine ⟨7008219015691058056817083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9344292020921410742422777 7008219015691058056817083)
            ·
              refine ⟨10512328523536587085225625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7008219015691058056817083 10512328523536587085225625)
              ·
                refine ⟨7884246392652440313919219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10512328523536587085225625 7884246392652440313919219)
                ·
                  refine ⟨11826369588978660470878829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7884246392652440313919219 11826369588978660470878829)
                  ·
                    refine ⟨4434888595866997676579561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11826369588978660470878829 4434888595866997676579561)
                    ·
                      refine ⟨3326166446900248257434671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434888595866997676579561 3326166446900248257434671)
                      ·
                        rfl

theorem cell23_6477686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_6477686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477686 prefixEnd_6477686 := by exact prefixLift 6477686
  have htrace : WordTrace (prefixWord ++ tailWord_6477686) baseStart_6477686 baseEnd_6477686 := by
    simpa [prefixWord, tailWord_6477686, baseEnd_6477686] using wordTrace_append hprefix tailTrace_6477686
  have hstable : (prefixWord ++ tailWord_6477686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477686).length < 2 ^ (prefixWord ++ tailWord_6477686).sum := by decide
  have hdescent : baseEnd_6477686 < baseStart_6477686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477722 : List Nat := [3, 1, 1, 4, 2, 1, 4, 2, 5]
def baseStart_6477722 : Nat := 118140960795 + 6477722 * 2 ^ 59
def prefixEnd_6477722 : Nat := 4983230072969 + 3 ^ 40 * 6477722 * 2
def baseEnd_6477722 : Nat := 369576103578201124064945

theorem tailTrace_6477722 : CollatzResearch.WordTrace tailWord_6477722 prefixEnd_6477722 369576103578201124064945 := by
  unfold tailWord_6477722
  simp only [CollatzResearch.WordTrace]
  refine ⟨59065482759581743921280855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157507954025551317123415613 59065482759581743921280855)
  ·
    refine ⟨88598224139372615881921283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59065482759581743921280855 88598224139372615881921283)
    ·
      refine ⟨132897336209058923822881925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88598224139372615881921283 132897336209058923822881925)
      ·
        refine ⟨24918250539198548216790361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132897336209058923822881925 24918250539198548216790361)
        ·
          refine ⟨18688687904398911162592771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24918250539198548216790361 18688687904398911162592771)
          ·
            refine ⟨28033031856598366743889157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18688687904398911162592771 28033031856598366743889157)
            ·
              refine ⟨5256193473112193764479217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28033031856598366743889157 5256193473112193764479217)
              ·
                refine ⟨3942145104834145323359413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5256193473112193764479217 3942145104834145323359413)
                ·
                  refine ⟨369576103578201124064945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3942145104834145323359413 369576103578201124064945)
                  ·
                    rfl

theorem cell23_6477722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 5].length) (baseStart_6477722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477722 prefixEnd_6477722 := by exact prefixLift 6477722
  have htrace : WordTrace (prefixWord ++ tailWord_6477722) baseStart_6477722 baseEnd_6477722 := by
    simpa [prefixWord, tailWord_6477722, baseEnd_6477722] using wordTrace_append hprefix tailTrace_6477722
  have hstable : (prefixWord ++ tailWord_6477722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477722).length < 2 ^ (prefixWord ++ tailWord_6477722).sum := by decide
  have hdescent : baseEnd_6477722 < baseStart_6477722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477725 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_6477725 : Nat := 118140960795 + 6477725 * 2 ^ 59
def prefixEnd_6477725 : Nat := 4983230072969 + 3 ^ 40 * 6477725 * 2
def baseEnd_6477725 : Nat := 3326186472645773604846991

theorem tailTrace_6477725 : CollatzResearch.WordTrace tailWord_6477725 prefixEnd_6477725 3326186472645773604846991 := by
  unfold tailWord_6477725
  simp only [CollatzResearch.WordTrace]
  refine ⟨236262040457316107197482629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157508026971544071464988419 236262040457316107197482629)
  ·
    refine ⟨44299132585746770099527993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236262040457316107197482629 44299132585746770099527993)
    ·
      refine ⟨33224349439310077574645995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44299132585746770099527993 33224349439310077574645995)
      ·
        refine ⟨49836524158965116361968993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33224349439310077574645995 49836524158965116361968993)
        ·
          refine ⟨37377393119223837271476745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49836524158965116361968993 37377393119223837271476745)
          ·
            refine ⟨28033044839417877953607559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37377393119223837271476745 28033044839417877953607559)
            ·
              refine ⟨42049567259126816930411339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28033044839417877953607559 42049567259126816930411339)
              ·
                refine ⟨63074350888690225395617009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42049567259126816930411339 63074350888690225395617009)
                ·
                  refine ⟨47305763166517669046712757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63074350888690225395617009 47305763166517669046712757)
                  ·
                    refine ⟨4434915296861031473129321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47305763166517669046712757 4434915296861031473129321)
                    ·
                      refine ⟨3326186472645773604846991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434915296861031473129321 3326186472645773604846991)
                      ·
                        rfl

theorem cell23_6477725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_6477725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477725 prefixEnd_6477725 := by exact prefixLift 6477725
  have htrace : WordTrace (prefixWord ++ tailWord_6477725) baseStart_6477725 baseEnd_6477725 := by
    simpa [prefixWord, tailWord_6477725, baseEnd_6477725] using wordTrace_append hprefix tailTrace_6477725
  have hstable : (prefixWord ++ tailWord_6477725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477725).length < 2 ^ (prefixWord ++ tailWord_6477725).sum := by decide
  have hdescent : baseEnd_6477725 < baseStart_6477725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477731 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 2, 8]
def baseStart_6477731 : Nat := 118140960795 + 6477731 * 2 ^ 59
def prefixEnd_6477731 : Nat := 4983230072969 + 3 ^ 40 * 6477731 * 2
def baseEnd_6477731 : Nat := 1108729851176566860457321

theorem tailTrace_6477731 : CollatzResearch.WordTrace tailWord_6477731 prefixEnd_6477731 1108729851176566860457321 := by
  unfold tailWord_6477731
  simp only [CollatzResearch.WordTrace]
  refine ⟨236262259295294370222201047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157508172863529580148134031 236262259295294370222201047)
  ·
    refine ⟨354393388942941555333301571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236262259295294370222201047 354393388942941555333301571)
    ·
      refine ⟨531590083414412332999952357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354393388942941555333301571 531590083414412332999952357)
      ·
        refine ⟨99673140640202312437491067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 531590083414412332999952357 99673140640202312437491067)
        ·
          refine ⟨149509710960303468656236601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99673140640202312437491067 149509710960303468656236601)
          ·
            refine ⟨112132283220227601492177451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149509710960303468656236601 112132283220227601492177451)
            ·
              refine ⟨168198424830341402238266177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112132283220227601492177451 168198424830341402238266177)
              ·
                refine ⟨126148818622756051678699633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168198424830341402238266177 126148818622756051678699633)
                ·
                  refine ⟨94611613967067038759024725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126148818622756051678699633 94611613967067038759024725)
                  ·
                    refine ⟨1108729851176566860457321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94611613967067038759024725 1108729851176566860457321)
                    ·
                      rfl

theorem cell23_6477731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 8].length) (baseStart_6477731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477731 prefixEnd_6477731 := by exact prefixLift 6477731
  have htrace : WordTrace (prefixWord ++ tailWord_6477731) baseStart_6477731 baseEnd_6477731 := by
    simpa [prefixWord, tailWord_6477731, baseEnd_6477731] using wordTrace_append hprefix tailTrace_6477731
  have hstable : (prefixWord ++ tailWord_6477731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477731).length < 2 ^ (prefixWord ++ tailWord_6477731).sum := by decide
  have hdescent : baseEnd_6477731 < baseStart_6477731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477768 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_6477768 : Nat := 118140960795 + 6477768 * 2 ^ 59
def prefixEnd_6477768 : Nat := 4983230072969 + 3 ^ 40 * 6477768 * 2
def baseEnd_6477768 : Nat := 3326208552313916936609293

theorem tailTrace_6477768 : CollatzResearch.WordTrace tailWord_6477768 prefixEnd_6477768 3326208552313916936609293 := by
  unfold tailWord_6477768
  simp only [CollatzResearch.WordTrace]
  refine ⟨118131804398080162770648979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157509072530773550360865305 118131804398080162770648979)
  ·
    refine ⟨177197706597120244155973469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118131804398080162770648979 177197706597120244155973469)
    ·
      refine ⟨66449139973920091558490051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177197706597120244155973469 66449139973920091558490051)
      ·
        refine ⟨99673709960880137337735077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66449139973920091558490051 99673709960880137337735077)
        ·
          refine ⟨18688820617665025750825327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99673709960880137337735077 18688820617665025750825327)
          ·
            refine ⟨28033230926497538626237991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18688820617665025750825327 28033230926497538626237991)
            ·
              refine ⟨42049846389746307939356987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28033230926497538626237991 42049846389746307939356987)
              ·
                refine ⟨63074769584619461909035481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42049846389746307939356987 63074769584619461909035481)
                ·
                  refine ⟨47306077188464596431776611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63074769584619461909035481 47306077188464596431776611)
                  ·
                    refine ⟨70959115782696894647664917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47306077188464596431776611 70959115782696894647664917)
                    ·
                      refine ⟨3326208552313916936609293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70959115782696894647664917 3326208552313916936609293)
                      ·
                        rfl

theorem cell23_6477768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_6477768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477768 prefixEnd_6477768 := by exact prefixLift 6477768
  have htrace : WordTrace (prefixWord ++ tailWord_6477768) baseStart_6477768 baseEnd_6477768 := by
    simpa [prefixWord, tailWord_6477768, baseEnd_6477768] using wordTrace_append hprefix tailTrace_6477768
  have hstable : (prefixWord ++ tailWord_6477768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477768).length < 2 ^ (prefixWord ++ tailWord_6477768).sum := by decide
  have hdescent : baseEnd_6477768 < baseStart_6477768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477808 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 3, 5]
def baseStart_6477808 : Nat := 118140960795 + 6477808 * 2 ^ 59
def prefixEnd_6477808 : Nat := 4983230072969 + 3 ^ 40 * 6477808 * 2
def baseEnd_6477808 : Nat := 1108743030513365593369703

theorem tailTrace_6477808 : CollatzResearch.WordTrace tailWord_6477808 prefixEnd_6477808 1108743030513365593369703 := by
  unfold tailWord_6477808
  simp only [CollatzResearch.WordTrace]
  refine ⟨118132533858007706186377039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157510045144010274915169385 118132533858007706186377039)
  ·
    refine ⟨177198800787011559279565559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118132533858007706186377039 177198800787011559279565559)
    ·
      refine ⟨265798201180517338919348339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177198800787011559279565559 265798201180517338919348339)
      ·
        refine ⟨398697301770776008379022509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265798201180517338919348339 398697301770776008379022509)
        ·
          refine ⟨149511488164041003142133441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398697301770776008379022509 149511488164041003142133441)
          ·
            refine ⟨112133616123030752356600081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149511488164041003142133441 112133616123030752356600081)
            ·
              refine ⟨84100212092273064267450061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112133616123030752356600081 84100212092273064267450061)
              ·
                refine ⟨31537579534602399100293773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84100212092273064267450061 31537579534602399100293773)
                ·
                  refine ⟨11826592325475899662610165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31537579534602399100293773 11826592325475899662610165)
                  ·
                    refine ⟨1108743030513365593369703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11826592325475899662610165 1108743030513365593369703)
                    ·
                      rfl

theorem cell23_6477808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3, 5].length) (baseStart_6477808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477808 prefixEnd_6477808 := by exact prefixLift 6477808
  have htrace : WordTrace (prefixWord ++ tailWord_6477808) baseStart_6477808 baseEnd_6477808 := by
    simpa [prefixWord, tailWord_6477808, baseEnd_6477808] using wordTrace_append hprefix tailTrace_6477808
  have hstable : (prefixWord ++ tailWord_6477808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477808).length < 2 ^ (prefixWord ++ tailWord_6477808).sum := by decide
  have hdescent : baseEnd_6477808 < baseStart_6477808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477815 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 8, 3, 2]
def baseStart_6477815 : Nat := 118140960795 + 6477815 * 2 ^ 59
def prefixEnd_6477815 : Nat := 4983230072969 + 3 ^ 40 * 6477815 * 2
def baseEnd_6477815 : Nat := 3326232685904678252721577

theorem tailTrace_6477815 : CollatzResearch.WordTrace tailWord_6477815 prefixEnd_6477815 3326232685904678252721577 := by
  unfold tailWord_6477815
  simp only [CollatzResearch.WordTrace]
  refine ⟨236265323026990052568258899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157510215351326701712172599 236265323026990052568258899)
  ·
    refine ⟨354397984540485078852388349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236265323026990052568258899 354397984540485078852388349)
    ·
      refine ⟨132899244202681904569645631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354397984540485078852388349 132899244202681904569645631)
      ·
        refine ⟨199348866304022856854468447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132899244202681904569645631 199348866304022856854468447)
        ·
          refine ⟨299023299456034285281702671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199348866304022856854468447 299023299456034285281702671)
          ·
            refine ⟨448534949184051427922554007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299023299456034285281702671 448534949184051427922554007)
            ·
              refine ⟨672802423776077141883831011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448534949184051427922554007 672802423776077141883831011)
              ·
                refine ⟨1009203635664115712825746517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672802423776077141883831011 1009203635664115712825746517)
                ·
                  refine ⟨11826605105438856009676717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1009203635664115712825746517 11826605105438856009676717)
                  ·
                    refine ⟨4434976914539571003628769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11826605105438856009676717 4434976914539571003628769)
                    ·
                      refine ⟨3326232685904678252721577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434976914539571003628769 3326232685904678252721577)
                      ·
                        rfl

theorem cell23_6477815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 3, 2].length) (baseStart_6477815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477815 prefixEnd_6477815 := by exact prefixLift 6477815
  have htrace : WordTrace (prefixWord ++ tailWord_6477815) baseStart_6477815 baseEnd_6477815 := by
    simpa [prefixWord, tailWord_6477815, baseEnd_6477815] using wordTrace_append hprefix tailTrace_6477815
  have hstable : (prefixWord ++ tailWord_6477815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477815).length < 2 ^ (prefixWord ++ tailWord_6477815).sum := by decide
  have hdescent : baseEnd_6477815 < baseStart_6477815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477825 : List Nat := [1, 2, 4, 1, 2, 1, 1, 5, 1, 5]
def baseStart_6477825 : Nat := 118140960795 + 6477825 * 2 ^ 59
def prefixEnd_6477825 : Nat := 4983230072969 + 3 ^ 40 * 6477825 * 2
def baseEnd_6477825 : Nat := 1108745940237074404532177

theorem tailTrace_6477825 : CollatzResearch.WordTrace tailWord_6477825 prefixEnd_6477825 1108745940237074404532177 := by
  unfold tailWord_6477825
  simp only [CollatzResearch.WordTrace]
  refine ⟨236265687756953824276122929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157510458504635882850748619 236265687756953824276122929)
  ·
    refine ⟨177199265817715368207092197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236265687756953824276122929 177199265817715368207092197)
    ·
      refine ⟨33224862340821631538829787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177199265817715368207092197 33224862340821631538829787)
      ·
        refine ⟨49837293511232447308244681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33224862340821631538829787 49837293511232447308244681)
        ·
          refine ⟨37377970133424335481183511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49837293511232447308244681 37377970133424335481183511)
          ·
            refine ⟨56066955200136503221775267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37377970133424335481183511 56066955200136503221775267)
            ·
              refine ⟨84100432800204754832662901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56066955200136503221775267 84100432800204754832662901)
              ·
                refine ⟨7884415575019195765562147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84100432800204754832662901 7884415575019195765562147)
                ·
                  refine ⟨11826623362528793648343221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7884415575019195765562147 11826623362528793648343221)
                  ·
                    refine ⟨1108745940237074404532177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11826623362528793648343221 1108745940237074404532177)
                    ·
                      rfl

theorem cell23_6477825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_6477825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477825 prefixEnd_6477825 := by exact prefixLift 6477825
  have htrace : WordTrace (prefixWord ++ tailWord_6477825) baseStart_6477825 baseEnd_6477825 := by
    simpa [prefixWord, tailWord_6477825, baseEnd_6477825] using wordTrace_append hprefix tailTrace_6477825
  have hstable : (prefixWord ++ tailWord_6477825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477825).length < 2 ^ (prefixWord ++ tailWord_6477825).sum := by decide
  have hdescent : baseEnd_6477825 < baseStart_6477825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477832 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 2, 3, 2]
def baseStart_6477832 : Nat := 118140960795 + 6477832 * 2 ^ 59
def prefixEnd_6477832 : Nat := 4983230072969 + 3 ^ 40 * 6477832 * 2
def baseEnd_6477832 : Nat := 3326241415075804686208999

theorem tailTrace_6477832 : CollatzResearch.WordTrace tailWord_6477832 prefixEnd_6477832 3326241415075804686208999 := by
  unfold tailWord_6477832
  simp only [CollatzResearch.WordTrace]
  refine ⟨118132971533964232235813875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157510628711952309647751833 118132971533964232235813875)
  ·
    refine ⟨177199457300946348353720813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118132971533964232235813875 177199457300946348353720813)
    ·
      refine ⟨66449796487854880632645305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177199457300946348353720813 66449796487854880632645305)
      ·
        refine ⟨49837347365891160474483979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66449796487854880632645305 49837347365891160474483979)
        ·
          refine ⟨74756021048836740711725969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49837347365891160474483979 74756021048836740711725969)
          ·
            refine ⟨56067015786627555533794477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74756021048836740711725969 56067015786627555533794477)
            ·
              refine ⟨21025130919985333325172929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56067015786627555533794477 21025130919985333325172929)
              ·
                refine ⟨15768848189988999993879697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21025130919985333325172929 15768848189988999993879697)
                ·
                  refine ⟨11826636142491749995409773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15768848189988999993879697 11826636142491749995409773)
                  ·
                    refine ⟨4434988553434406248278665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11826636142491749995409773 4434988553434406248278665)
                    ·
                      refine ⟨3326241415075804686208999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434988553434406248278665 3326241415075804686208999)
                      ·
                        rfl

theorem cell23_6477832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_6477832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477832 prefixEnd_6477832 := by exact prefixLift 6477832
  have htrace : WordTrace (prefixWord ++ tailWord_6477832) baseStart_6477832 baseEnd_6477832 := by
    simpa [prefixWord, tailWord_6477832, baseEnd_6477832] using wordTrace_append hprefix tailTrace_6477832
  have hstable : (prefixWord ++ tailWord_6477832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477832).length < 2 ^ (prefixWord ++ tailWord_6477832).sum := by decide
  have hdescent : baseEnd_6477832 < baseStart_6477832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477876 : List Nat := [2, 5, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_6477876 : Nat := 118140960795 + 6477876 * 2 ^ 59
def prefixEnd_6477876 : Nat := 4983230072969 + 3 ^ 40 * 6477876 * 2
def baseEnd_6477876 : Nat := 1108754669408200838019599

theorem tailTrace_6477876 : CollatzResearch.WordTrace tailWord_6477876 prefixEnd_6477876 1108754669408200838019599 := by
  unfold tailWord_6477876
  simp only [CollatzResearch.WordTrace]
  refine ⟨118133773939884529993114741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157511698586512706657486321 118133773939884529993114741)
  ·
    refine ⟨11075041306864174686854507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118133773939884529993114741 11075041306864174686854507)
    ·
      refine ⟨16612561960296262030281761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11075041306864174686854507 16612561960296262030281761)
      ·
        refine ⟨12459421470222196522711321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16612561960296262030281761 12459421470222196522711321)
        ·
          refine ⟨9344566102666647392033491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12459421470222196522711321 9344566102666647392033491)
          ·
            refine ⟨14016849153999971088050237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9344566102666647392033491 14016849153999971088050237)
            ·
              refine ⟨5256318432749989158018839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14016849153999971088050237 5256318432749989158018839)
              ·
                refine ⟨7884477649124983737028259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5256318432749989158018839 7884477649124983737028259)
                ·
                  refine ⟨11826716473687475605542389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7884477649124983737028259 11826716473687475605542389)
                  ·
                    refine ⟨1108754669408200838019599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11826716473687475605542389 1108754669408200838019599)
                    ·
                      rfl

theorem cell23_6477876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_6477876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477876 prefixEnd_6477876 := by exact prefixLift 6477876
  have htrace : WordTrace (prefixWord ++ tailWord_6477876) baseStart_6477876 baseEnd_6477876 := by
    simpa [prefixWord, tailWord_6477876, baseEnd_6477876] using wordTrace_append hprefix tailTrace_6477876
  have hstable : (prefixWord ++ tailWord_6477876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477876).length < 2 ^ (prefixWord ++ tailWord_6477876).sum := by decide
  have hdescent : baseEnd_6477876 < baseStart_6477876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477889 : List Nat := [1, 2, 5, 1, 2, 2, 2, 2, 2, 4]
def baseStart_6477889 : Nat := 118140960795 + 6477889 * 2 ^ 59
def prefixEnd_6477889 : Nat := 4983230072969 + 3 ^ 40 * 6477889 * 2
def baseEnd_6477889 : Nat := 1108756894491036987732079

theorem tailTrace_6477889 : CollatzResearch.WordTrace tailWord_6477889 prefixEnd_6477889 1108756894491036987732079 := by
  unfold tailWord_6477889
  simp only [CollatzResearch.WordTrace]
  refine ⟨236268022028721963206452721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157512014685814642137635147 236268022028721963206452721)
  ·
    refine ⟨177201016521541472404839541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236268022028721963206452721 177201016521541472404839541)
    ·
      refine ⟨16612595298894513037953707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177201016521541472404839541 16612595298894513037953707)
      ·
        refine ⟨24918892948341769556930561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16612595298894513037953707 24918892948341769556930561)
        ·
          refine ⟨18689169711256327167697921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24918892948341769556930561 18689169711256327167697921)
          ·
            refine ⟨14016877283442245375773441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18689169711256327167697921 14016877283442245375773441)
            ·
              refine ⟨10512657962581684031830081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14016877283442245375773441 10512657962581684031830081)
              ·
                refine ⟨7884493471936263023872561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10512657962581684031830081 7884493471936263023872561)
                ·
                  refine ⟨5913370103952197267904421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7884493471936263023872561 5913370103952197267904421)
                  ·
                    refine ⟨1108756894491036987732079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5913370103952197267904421 1108756894491036987732079)
                    ·
                      rfl

theorem cell23_6477889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_6477889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477889 prefixEnd_6477889 := by exact prefixLift 6477889
  have htrace : WordTrace (prefixWord ++ tailWord_6477889) baseStart_6477889 baseEnd_6477889 := by
    simpa [prefixWord, tailWord_6477889, baseEnd_6477889] using wordTrace_append hprefix tailTrace_6477889
  have hstable : (prefixWord ++ tailWord_6477889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477889).length < 2 ^ (prefixWord ++ tailWord_6477889).sum := by decide
  have hdescent : baseEnd_6477889 < baseStart_6477889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477895 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_6477895 : Nat := 118140960795 + 6477895 * 2 ^ 59
def prefixEnd_6477895 : Nat := 4983230072969 + 3 ^ 40 * 6477895 * 2
def baseEnd_6477895 : Nat := 3326273764357037939721209

theorem tailTrace_6477895 : CollatzResearch.WordTrace tailWord_6477895 prefixEnd_6477895 3326273764357037939721209 := by
  unfold tailWord_6477895
  simp only [CollatzResearch.WordTrace]
  refine ⟨236268240866700226231171139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157512160577800150820780759 236268240866700226231171139)
  ·
    refine ⟨354402361300050339346756709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236268240866700226231171139 354402361300050339346756709)
    ·
      refine ⟨66450442743759438627516883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354402361300050339346756709 66450442743759438627516883)
      ·
        refine ⟨99675664115639157941275325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66450442743759438627516883 99675664115639157941275325)
        ·
          refine ⟨37378374043364684227978247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99675664115639157941275325 37378374043364684227978247)
          ·
            refine ⟨56067561065047026341967371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37378374043364684227978247 56067561065047026341967371)
            ·
              refine ⟨84101341597570539512951057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56067561065047026341967371 84101341597570539512951057)
              ·
                refine ⟨63076006198177904634713293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84101341597570539512951057 63076006198177904634713293)
                ·
                  refine ⟨23653502324316714238017485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63076006198177904634713293 23653502324316714238017485)
                  ·
                    refine ⟨8870063371618767839256557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23653502324316714238017485 8870063371618767839256557)
                    ·
                      refine ⟨3326273764357037939721209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8870063371618767839256557 3326273764357037939721209)
                      ·
                        rfl

theorem cell23_6477895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_6477895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477895 prefixEnd_6477895 := by exact prefixLift 6477895
  have htrace : WordTrace (prefixWord ++ tailWord_6477895) baseStart_6477895 baseEnd_6477895 := by
    simpa [prefixWord, tailWord_6477895, baseEnd_6477895] using wordTrace_append hprefix tailTrace_6477895
  have hstable : (prefixWord ++ tailWord_6477895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477895).length < 2 ^ (prefixWord ++ tailWord_6477895).sum := by decide
  have hdescent : baseEnd_6477895 < baseStart_6477895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477912 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 1, 3, 3]
def baseStart_6477912 : Nat := 118140960795 + 6477912 * 2 ^ 59
def prefixEnd_6477912 : Nat := 4983230072969 + 3 ^ 40 * 6477912 * 2
def baseEnd_6477912 : Nat := 3326282493528164373208631

theorem tailTrace_6477912 : CollatzResearch.WordTrace tailWord_6477912 prefixEnd_6477912 3326282493528164373208631 := by
  unfold tailWord_6477912
  simp only [CollatzResearch.WordTrace]
  refine ⟨118134430453819319067269995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157512573938425758756359993 118134430453819319067269995)
  ·
    refine ⟨177201645680728978600904993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118134430453819319067269995 177201645680728978600904993)
    ·
      refine ⟨132901234260546733950678745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177201645680728978600904993 132901234260546733950678745)
      ·
        refine ⟨99675925695410050463009059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132901234260546733950678745 99675925695410050463009059)
        ·
          refine ⟨149513888543115075694513589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99675925695410050463009059 149513888543115075694513589)
          ·
            refine ⟨14016927050917038346360649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149513888543115075694513589 14016927050917038346360649)
            ·
              refine ⟨10512695288187778759770487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14016927050917038346360649 10512695288187778759770487)
              ·
                refine ⟨15769042932281668139655731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10512695288187778759770487 15769042932281668139655731)
                ·
                  refine ⟨23653564398422502209483597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15769042932281668139655731 23653564398422502209483597)
                  ·
                    refine ⟨8870086649408438328556349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23653564398422502209483597 8870086649408438328556349)
                    ·
                      refine ⟨3326282493528164373208631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8870086649408438328556349 3326282493528164373208631)
                      ·
                        rfl

theorem cell23_6477912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_6477912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477912 prefixEnd_6477912 := by exact prefixLift 6477912
  have htrace : WordTrace (prefixWord ++ tailWord_6477912) baseStart_6477912 baseEnd_6477912 := by
    simpa [prefixWord, tailWord_6477912, baseEnd_6477912] using wordTrace_append hprefix tailTrace_6477912
  have hstable : (prefixWord ++ tailWord_6477912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477912).length < 2 ^ (prefixWord ++ tailWord_6477912).sum := by decide
  have hdescent : baseEnd_6477912 < baseStart_6477912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477945 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 2, 6]
def baseStart_6477945 : Nat := 118140960795 + 6477945 * 2 ^ 59
def prefixEnd_6477945 : Nat := 4983230072969 + 3 ^ 40 * 6477945 * 2
def baseEnd_6477945 : Nat := 1108766479463254248031993

theorem tailTrace_6477945 : CollatzResearch.WordTrace tailWord_6477945 prefixEnd_6477945 1108766479463254248031993 := by
  unfold tailWord_6477945
  simp only [CollatzResearch.WordTrace]
  refine ⟨236270064516519084770491289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157513376344346056513660859 236270064516519084770491289)
  ·
    refine ⟨177202548387389313577868467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236270064516519084770491289 177202548387389313577868467)
    ·
      refine ⟨265803822581083970366802701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177202548387389313577868467 265803822581083970366802701)
      ·
        refine ⟨99676433467906488887551013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265803822581083970366802701 99676433467906488887551013)
        ·
          refine ⟨18689331275232466666415815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99676433467906488887551013 18689331275232466666415815)
          ·
            refine ⟨28033996912848699999623723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18689331275232466666415815 28033996912848699999623723)
            ·
              refine ⟨42050995369273049999435585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28033996912848699999623723 42050995369273049999435585)
              ·
                refine ⟨31538246526954787499576689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42050995369273049999435585 31538246526954787499576689)
                ·
                  refine ⟨23653684895216090624682517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31538246526954787499576689 23653684895216090624682517)
                  ·
                    refine ⟨1108766479463254248031993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23653684895216090624682517 1108766479463254248031993)
                    ·
                      rfl

theorem cell23_6477945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_6477945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477945 prefixEnd_6477945 := by exact prefixLift 6477945
  have htrace : WordTrace (prefixWord ++ tailWord_6477945) baseStart_6477945 baseEnd_6477945 := by
    simpa [prefixWord, tailWord_6477945, baseEnd_6477945] using wordTrace_append hprefix tailTrace_6477945
  have hstable : (prefixWord ++ tailWord_6477945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477945).length < 2 ^ (prefixWord ++ tailWord_6477945).sum := by decide
  have hdescent : baseEnd_6477945 < baseStart_6477945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6477986 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_6477986 : Nat := 118140960795 + 6477986 * 2 ^ 59
def prefixEnd_6477986 : Nat := 4983230072969 + 3 ^ 40 * 6477986 * 2
def baseEnd_6477986 : Nat := 3326320491096597083683291

theorem tailTrace_6477986 : CollatzResearch.WordTrace tailWord_6477986 prefixEnd_6477986 3326320491096597083683291 := by
  unfold tailWord_6477986
  simp only [CollatzResearch.WordTrace]
  refine ⟨59067889977342637193183453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157514373272913699181822541 59067889977342637193183453)
  ·
    refine ⟨22150458741503488947443795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59067889977342637193183453 22150458741503488947443795)
    ·
      refine ⟨33225688112255233421165693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22150458741503488947443795 33225688112255233421165693)
      ·
        refine ⟨12459633042095712532937135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33225688112255233421165693 12459633042095712532937135)
        ·
          refine ⟨18689449563143568799405703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12459633042095712532937135 18689449563143568799405703)
          ·
            refine ⟨28034174344715353199108555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18689449563143568799405703 28034174344715353199108555)
            ·
              refine ⟨42051261517073029798662833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28034174344715353199108555 42051261517073029798662833)
              ·
                refine ⟨31538446137804772348997125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42051261517073029798662833 31538446137804772348997125)
                ·
                  refine ⟨5913458650838394815436961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31538446137804772348997125 5913458650838394815436961)
                  ·
                    refine ⟨4435093988128796111577721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5913458650838394815436961 4435093988128796111577721)
                    ·
                      refine ⟨3326320491096597083683291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4435093988128796111577721 3326320491096597083683291)
                      ·
                        rfl

theorem cell23_6477986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_6477986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6477986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6477986 prefixEnd_6477986 := by exact prefixLift 6477986
  have htrace : WordTrace (prefixWord ++ tailWord_6477986) baseStart_6477986 baseEnd_6477986 := by
    simpa [prefixWord, tailWord_6477986, baseEnd_6477986] using wordTrace_append hprefix tailTrace_6477986
  have hstable : (prefixWord ++ tailWord_6477986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6477986).length < 2 ^ (prefixWord ++ tailWord_6477986).sum := by decide
  have hdescent : baseEnd_6477986 < baseStart_6477986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6477986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478009 : List Nat := [1, 2, 1, 4, 1, 2, 5, 2, 5]
def baseStart_6478009 : Nat := 118140960795 + 6478009 * 2 ^ 59
def prefixEnd_6478009 : Nat := 4983230072969 + 3 ^ 40 * 6478009 * 2
def baseEnd_6478009 : Nat := 369592477905738943743965

theorem tailTrace_6478009 : CollatzResearch.WordTrace tailWord_6478009 prefixEnd_6478009 369592477905738943743965 := by
  unfold tailWord_6478009
  simp only [CollatzResearch.WordTrace]
  refine ⟨236272398788287223700821081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157514932525524815800547387 236272398788287223700821081)
  ·
    refine ⟨177204299091215417775615811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236272398788287223700821081 177204299091215417775615811)
    ·
      refine ⟨265806448636823126663423717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177204299091215417775615811 265806448636823126663423717)
      ·
        refine ⟨49838709119404336249391947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265806448636823126663423717 49838709119404336249391947)
        ·
          refine ⟨74758063679106504374087921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49838709119404336249391947 74758063679106504374087921)
          ·
            refine ⟨56068547759329878280565941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74758063679106504374087921 56068547759329878280565941)
            ·
              refine ⟨5256426352437176088803057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56068547759329878280565941 5256426352437176088803057)
              ·
                refine ⟨3942319764327882066602293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5256426352437176088803057 3942319764327882066602293)
                ·
                  refine ⟨369592477905738943743965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3942319764327882066602293 369592477905738943743965)
                  ·
                    rfl

theorem cell23_6478009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 5].length) (baseStart_6478009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478009 prefixEnd_6478009 := by exact prefixLift 6478009
  have htrace : WordTrace (prefixWord ++ tailWord_6478009) baseStart_6478009 baseEnd_6478009 := by
    simpa [prefixWord, tailWord_6478009, baseEnd_6478009] using wordTrace_append hprefix tailTrace_6478009
  have hstable : (prefixWord ++ tailWord_6478009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478009).length < 2 ^ (prefixWord ++ tailWord_6478009).sum := by decide
  have hdescent : baseEnd_6478009 < baseStart_6478009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478020 : List Nat := [2, 3, 3, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_6478020 : Nat := 118140960795 + 6478020 * 2 ^ 59
def prefixEnd_6478020 : Nat := 4983230072969 + 3 ^ 40 * 6478020 * 2
def baseEnd_6478020 : Nat := 3326337949438849950658135

theorem tailTrace_6478020 : CollatzResearch.WordTrace tailWord_6478020 prefixEnd_6478020 3326337949438849950658135 := by
  unfold tailWord_6478020
  simp only [CollatzResearch.WordTrace]
  refine ⟨118136399995623686289735757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157515199994164915052981009 118136399995623686289735757)
  ·
    refine ⟨44301149998358882358650909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118136399995623686289735757 44301149998358882358650909)
    ·
      refine ⟨16612931249384580884494091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44301149998358882358650909 16612931249384580884494091)
      ·
        refine ⟨24919396874076871326741137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16612931249384580884494091 24919396874076871326741137)
        ·
          refine ⟨18689547655557653495055853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24919396874076871326741137 18689547655557653495055853)
          ·
            refine ⟨7008580370834120060645945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18689547655557653495055853 7008580370834120060645945)
            ·
              refine ⟨5256435278125590045484459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7008580370834120060645945 5256435278125590045484459)
              ·
                refine ⟨7884652917188385068226689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5256435278125590045484459 7884652917188385068226689)
                ·
                  refine ⟨5913489687891288801170017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7884652917188385068226689 5913489687891288801170017)
                  ·
                    refine ⟨4435117265918466600877513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5913489687891288801170017 4435117265918466600877513)
                    ·
                      refine ⟨3326337949438849950658135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4435117265918466600877513 3326337949438849950658135)
                      ·
                        rfl

theorem cell23_6478020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_6478020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478020 prefixEnd_6478020 := by exact prefixLift 6478020
  have htrace : WordTrace (prefixWord ++ tailWord_6478020) baseStart_6478020 baseEnd_6478020 := by
    simpa [prefixWord, tailWord_6478020, baseEnd_6478020] using wordTrace_append hprefix tailTrace_6478020
  have hstable : (prefixWord ++ tailWord_6478020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478020).length < 2 ^ (prefixWord ++ tailWord_6478020).sum := by decide
  have hdescent : baseEnd_6478020 < baseStart_6478020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478025 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 1, 3, 4]
def baseStart_6478025 : Nat := 118140960795 + 6478025 * 2 ^ 59
def prefixEnd_6478025 : Nat := 4983230072969 + 3 ^ 40 * 6478025 * 2
def baseEnd_6478025 : Nat := 3326340516842122431095611

theorem tailTrace_6478025 : CollatzResearch.WordTrace tailWord_6478025 prefixEnd_6478025 3326340516842122431095611 := by
  unfold tailWord_6478025
  simp only [CollatzResearch.WordTrace]
  refine ⟨236272982356229258433403529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157515321570819505622269019 236272982356229258433403529)
  ·
    refine ⟨177204736767171943825052647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236272982356229258433403529 177204736767171943825052647)
    ·
      refine ⟨265807105150757915737578971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177204736767171943825052647 265807105150757915737578971)
      ·
        refine ⟨398710657726136873606368457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265807105150757915737578971 398710657726136873606368457)
        ·
          refine ⟨299032993294602655204776343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398710657726136873606368457 299032993294602655204776343)
          ·
            refine ⟨448549489941903982807164515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299032993294602655204776343 448549489941903982807164515)
            ·
              refine ⟨672824234912855974210746773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448549489941903982807164515 672824234912855974210746773)
              ·
                refine ⟨31538636011540123791128755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 672824234912855974210746773 31538636011540123791128755)
                ·
                  refine ⟨47307954017310185686693133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31538636011540123791128755 47307954017310185686693133)
                  ·
                    refine ⟨17740482756491319632509925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47307954017310185686693133 17740482756491319632509925)
                    ·
                      refine ⟨3326340516842122431095611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17740482756491319632509925 3326340516842122431095611)
                      ·
                        rfl

theorem cell23_6478025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_6478025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478025 prefixEnd_6478025 := by exact prefixLift 6478025
  have htrace : WordTrace (prefixWord ++ tailWord_6478025) baseStart_6478025 baseEnd_6478025 := by
    simpa [prefixWord, tailWord_6478025, baseEnd_6478025] using wordTrace_append hprefix tailTrace_6478025
  have hstable : (prefixWord ++ tailWord_6478025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478025).length < 2 ^ (prefixWord ++ tailWord_6478025).sum := by decide
  have hdescent : baseEnd_6478025 < baseStart_6478025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478042 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_6478042 : Nat := 118140960795 + 6478042 * 2 ^ 59
def prefixEnd_6478042 : Nat := 4983230072969 + 3 ^ 40 * 6478042 * 2
def baseEnd_6478042 : Nat := 3326349246013248864583033

theorem tailTrace_6478042 : CollatzResearch.WordTrace tailWord_6478042 prefixEnd_6478042 3326349246013248864583033 := by
  unfold tailWord_6478042
  simp only [CollatzResearch.WordTrace]
  refine ⟨59068400599291917584193095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157515734931445113557848253 59068400599291917584193095)
  ·
    refine ⟨88602600898937876376289643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59068400599291917584193095 88602600898937876376289643)
    ·
      refine ⟨132903901348406814564434465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88602600898937876376289643 132903901348406814564434465)
      ·
        refine ⟨99677926011305110923325849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132903901348406814564434465 99677926011305110923325849)
        ·
          refine ⟨74758444508478833192494387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99677926011305110923325849 74758444508478833192494387)
          ·
            refine ⟨112137666762718249788741581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74758444508478833192494387 112137666762718249788741581)
            ·
              refine ⟨42051625036019343670778093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112137666762718249788741581 42051625036019343670778093)
              ·
                refine ⟨15769359388507253876541785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42051625036019343670778093 15769359388507253876541785)
                ·
                  refine ⟨11827019541380440407406339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15769359388507253876541785 11827019541380440407406339)
                  ·
                    refine ⟨17740529312070660611109509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11827019541380440407406339 17740529312070660611109509)
                    ·
                      refine ⟨3326349246013248864583033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17740529312070660611109509 3326349246013248864583033)
                      ·
                        rfl

theorem cell23_6478042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_6478042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478042 prefixEnd_6478042 := by exact prefixLift 6478042
  have htrace : WordTrace (prefixWord ++ tailWord_6478042) baseStart_6478042 baseEnd_6478042 := by
    simpa [prefixWord, tailWord_6478042, baseEnd_6478042] using wordTrace_append hprefix tailTrace_6478042
  have hstable : (prefixWord ++ tailWord_6478042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478042).length < 2 ^ (prefixWord ++ tailWord_6478042).sum := by decide
  have hdescent : baseEnd_6478042 < baseStart_6478042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478062 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_6478062 : Nat := 118140960795 + 6478062 * 2 ^ 59
def prefixEnd_6478062 : Nat := 4983230072969 + 3 ^ 40 * 6478062 * 2
def baseEnd_6478062 : Nat := 3326359515626338786332941

theorem tailTrace_6478062 : CollatzResearch.WordTrace tailWord_6478062 prefixEnd_6478062 3326359515626338786332941 := by
  unfold tailWord_6478062
  simp only [CollatzResearch.WordTrace]
  refine ⟨29534291482136901719062555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157516221238063475835000293 29534291482136901719062555)
  ·
    refine ⟨44301437223205352578593833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29534291482136901719062555 44301437223205352578593833)
    ·
      refine ⟨33226077917404014433945375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44301437223205352578593833 33226077917404014433945375)
      ·
        refine ⟨49839116876106021650918063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33226077917404014433945375 49839116876106021650918063)
        ·
          refine ⟨74758675314159032476377095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49839116876106021650918063 74758675314159032476377095)
          ·
            refine ⟨112138012971238548714565643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74758675314159032476377095 112138012971238548714565643)
            ·
              refine ⟨168207019456857823071848465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112138012971238548714565643 168207019456857823071848465)
              ·
                refine ⟨126155264592643367303886349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168207019456857823071848465 126155264592643367303886349)
                ·
                  refine ⟨47308224222241262738957381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126155264592643367303886349 47308224222241262738957381)
                  ·
                    refine ⟨8870292041670236763554509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47308224222241262738957381 8870292041670236763554509)
                    ·
                      refine ⟨3326359515626338786332941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8870292041670236763554509 3326359515626338786332941)
                      ·
                        rfl

theorem cell23_6478062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_6478062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478062 prefixEnd_6478062 := by exact prefixLift 6478062
  have htrace : WordTrace (prefixWord ++ tailWord_6478062) baseStart_6478062 baseEnd_6478062 := by
    simpa [prefixWord, tailWord_6478062, baseEnd_6478062] using wordTrace_append hprefix tailTrace_6478062
  have hstable : (prefixWord ++ tailWord_6478062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478062).length < 2 ^ (prefixWord ++ tailWord_6478062).sum := by decide
  have hdescent : baseEnd_6478062 < baseStart_6478062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478065 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 8]
def baseStart_6478065 : Nat := 118140960795 + 6478065 * 2 ^ 59
def prefixEnd_6478065 : Nat := 4983230072969 + 3 ^ 40 * 6478065 * 2
def baseEnd_6478065 : Nat := 369595672896478030510603

theorem tailTrace_6478065 : CollatzResearch.WordTrace tailWord_6478065 prefixEnd_6478065 369595672896478030510603 := by
  unfold tailWord_6478065
  simp only [CollatzResearch.WordTrace]
  refine ⟨236274441276084345264859649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157516294184056230176573099 236274441276084345264859649)
  ·
    refine ⟨177205830957063258948644737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236274441276084345264859649 177205830957063258948644737)
    ·
      refine ⟨132904373217797444211483553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177205830957063258948644737 132904373217797444211483553)
      ·
        refine ⟨99678279913348083158612665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132904373217797444211483553 99678279913348083158612665)
        ·
          refine ⟨74758709935011062368959499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99678279913348083158612665 74758709935011062368959499)
          ·
            refine ⟨112138064902516593553439249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74758709935011062368959499 112138064902516593553439249)
            ·
              refine ⟨84103548676887445165079437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112138064902516593553439249 84103548676887445165079437)
              ·
                refine ⟨31538830753832791936904789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84103548676887445165079437 31538830753832791936904789)
                ·
                  refine ⟨369595672896478030510603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31538830753832791936904789 369595672896478030510603)
                  ·
                    rfl

theorem cell23_6478065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 8].length) (baseStart_6478065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478065 prefixEnd_6478065 := by exact prefixLift 6478065
  have htrace : WordTrace (prefixWord ++ tailWord_6478065) baseStart_6478065 baseEnd_6478065 := by
    simpa [prefixWord, tailWord_6478065, baseEnd_6478065] using wordTrace_append hprefix tailTrace_6478065
  have hstable : (prefixWord ++ tailWord_6478065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478065).length < 2 ^ (prefixWord ++ tailWord_6478065).sum := by decide
  have hdescent : baseEnd_6478065 < baseStart_6478065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478085 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_6478085 : Nat := 118140960795 + 6478085 * 2 ^ 59
def prefixEnd_6478085 : Nat := 4983230072969 + 3 ^ 40 * 6478085 * 2
def baseEnd_6478085 : Nat := 3326371325681392196345335

theorem tailTrace_6478085 : CollatzResearch.WordTrace tailWord_6478085 prefixEnd_6478085 3326371325681392196345335 := by
  unfold tailWord_6478085
  simp only [CollatzResearch.WordTrace]
  refine ⟨236275170736011888680587709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157516780490674592453725139 236275170736011888680587709)
  ·
    refine ⟨88603189026004458255220391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236275170736011888680587709 88603189026004458255220391)
    ·
      refine ⟨132904783539006687382830587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88603189026004458255220391 132904783539006687382830587)
      ·
        refine ⟨199357175308510031074245881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132904783539006687382830587 199357175308510031074245881)
        ·
          refine ⟨149517881481382523305684411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199357175308510031074245881 149517881481382523305684411)
          ·
            refine ⟨224276822222073784958526617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149517881481382523305684411 224276822222073784958526617)
            ·
              refine ⟨168207616666555338718894963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224276822222073784958526617 168207616666555338718894963)
              ·
                refine ⟨252311424999833008078342445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168207616666555338718894963 252311424999833008078342445)
                ·
                  refine ⟨94616784374937378029378417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252311424999833008078342445 94616784374937378029378417)
                  ·
                    refine ⟨70962588281203033522033813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94616784374937378029378417 70962588281203033522033813)
                    ·
                      refine ⟨3326371325681392196345335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70962588281203033522033813 3326371325681392196345335)
                      ·
                        rfl

theorem cell23_6478085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_6478085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478085 prefixEnd_6478085 := by exact prefixLift 6478085
  have htrace : WordTrace (prefixWord ++ tailWord_6478085) baseStart_6478085 baseEnd_6478085 := by
    simpa [prefixWord, tailWord_6478085, baseEnd_6478085] using wordTrace_append hprefix tailTrace_6478085
  have hstable : (prefixWord ++ tailWord_6478085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478085).length < 2 ^ (prefixWord ++ tailWord_6478085).sum := by decide
  have hdescent : baseEnd_6478085 < baseStart_6478085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478183 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_6478183 : Nat := 118140960795 + 6478183 * 2 ^ 59
def prefixEnd_6478183 : Nat := 4983230072969 + 3 ^ 40 * 6478183 * 2
def baseEnd_6478183 : Nat := 3326421646785532812919885

theorem tailTrace_6478183 : CollatzResearch.WordTrace tailWord_6478183 prefixEnd_6478183 3326421646785532812919885 := by
  unfold tailWord_6478183
  simp only [CollatzResearch.WordTrace]
  refine ⟨236278745089656851417655203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157519163393104567611770135 236278745089656851417655203)
  ·
    refine ⟨354418117634485277126482805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236278745089656851417655203 354418117634485277126482805)
    ·
      refine ⟨33226698528232994730607763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 354418117634485277126482805 33226698528232994730607763)
      ·
        refine ⟨49840047792349492095911645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33226698528232994730607763 49840047792349492095911645)
        ·
          refine ⟨18690017922131059535966867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49840047792349492095911645 18690017922131059535966867)
          ·
            refine ⟨28035026883196589303950301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18690017922131059535966867 28035026883196589303950301)
            ·
              refine ⟨10513135081198720988981363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28035026883196589303950301 10513135081198720988981363)
              ·
                refine ⟨15769702621798081483472045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10513135081198720988981363 15769702621798081483472045)
                ·
                  refine ⟨5913638483174280556302017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15769702621798081483472045 5913638483174280556302017)
                  ·
                    refine ⟨4435228862380710417226513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5913638483174280556302017 4435228862380710417226513)
                    ·
                      refine ⟨3326421646785532812919885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4435228862380710417226513 3326421646785532812919885)
                      ·
                        rfl

theorem cell23_6478183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_6478183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478183 prefixEnd_6478183 := by exact prefixLift 6478183
  have htrace : WordTrace (prefixWord ++ tailWord_6478183) baseStart_6478183 baseEnd_6478183 := by
    simpa [prefixWord, tailWord_6478183, baseEnd_6478183] using wordTrace_append hprefix tailTrace_6478183
  have hstable : (prefixWord ++ tailWord_6478183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478183).length < 2 ^ (prefixWord ++ tailWord_6478183).sum := by decide
  have hdescent : baseEnd_6478183 < baseStart_6478183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478199 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 6, 1, 3]
def baseStart_6478199 : Nat := 118140960795 + 6478199 * 2 ^ 59
def prefixEnd_6478199 : Nat := 4983230072969 + 3 ^ 40 * 6478199 * 2
def baseEnd_6478199 : Nat := 3326429862476004750319811

theorem tailTrace_6478199 : CollatzResearch.WordTrace tailWord_6478199 prefixEnd_6478199 3326429862476004750319811 := by
  unfold tailWord_6478199
  simp only [CollatzResearch.WordTrace]
  refine ⟨236279328657598886150237651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157519552438399257433491767 236279328657598886150237651)
  ·
    refine ⟨354418992986398329225356477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236279328657598886150237651 354418992986398329225356477)
    ·
      refine ⟨132907122369899373459508679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354418992986398329225356477 132907122369899373459508679)
      ·
        refine ⟨199360683554849060189263019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132907122369899373459508679 199360683554849060189263019)
        ·
          refine ⟨299041025332273590283894529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199360683554849060189263019 299041025332273590283894529)
          ·
            refine ⟨224280768999205192712920897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299041025332273590283894529 224280768999205192712920897)
            ·
              refine ⟨168210576749403894534690673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224280768999205192712920897 168210576749403894534690673)
              ·
                refine ⟨126157932562052920901018005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168210576749403894534690673 126157932562052920901018005)
                ·
                  refine ⟨5913653088846230667235219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126157932562052920901018005 5913653088846230667235219)
                  ·
                    refine ⟨8870479633269346000852829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5913653088846230667235219 8870479633269346000852829)
                    ·
                      refine ⟨3326429862476004750319811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8870479633269346000852829 3326429862476004750319811)
                      ·
                        rfl

theorem cell23_6478199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_6478199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478199 prefixEnd_6478199 := by exact prefixLift 6478199
  have htrace : WordTrace (prefixWord ++ tailWord_6478199) baseStart_6478199 baseEnd_6478199 := by
    simpa [prefixWord, tailWord_6478199, baseEnd_6478199] using wordTrace_append hprefix tailTrace_6478199
  have hstable : (prefixWord ++ tailWord_6478199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478199).length < 2 ^ (prefixWord ++ tailWord_6478199).sum := by decide
  have hdescent : baseEnd_6478199 < baseStart_6478199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478272 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 7]
def baseStart_6478272 : Nat := 118140960795 + 6478272 * 2 ^ 59
def prefixEnd_6478272 : Nat := 4983230072969 + 3 ^ 40 * 6478272 * 2
def baseEnd_6478272 : Nat := 3326467346563782964706975

theorem tailTrace_6478272 : CollatzResearch.WordTrace tailWord_6478272 prefixEnd_6478272 3326467346563782964706975 := by
  unfold tailWord_6478272
  simp only [CollatzResearch.WordTrace]
  refine ⟨118140995593167209808822535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157521327457556279745096713 118140995593167209808822535)
  ·
    refine ⟨177211493389750814713233803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118140995593167209808822535 177211493389750814713233803)
    ·
      refine ⟨265817240084626222069850705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177211493389750814713233803 265817240084626222069850705)
      ·
        refine ⟨199362930063469666552388029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265817240084626222069850705 199362930063469666552388029)
        ·
          refine ⟨74761098773801124957145511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199362930063469666552388029 74761098773801124957145511)
          ·
            refine ⟨112141648160701687435718267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74761098773801124957145511 112141648160701687435718267)
            ·
              refine ⟨168212472241052531153577401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112141648160701687435718267 168212472241052531153577401)
              ·
                refine ⟨126159354180789398365183051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168212472241052531153577401 126159354180789398365183051)
                ·
                  refine ⟨189239031271184097547774577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126159354180789398365183051 189239031271184097547774577)
                  ·
                    refine ⟨141929273453388073160830933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 189239031271184097547774577 141929273453388073160830933)
                    ·
                      refine ⟨3326467346563782964706975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141929273453388073160830933 3326467346563782964706975)
                      ·
                        rfl

theorem cell23_6478272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_6478272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478272 prefixEnd_6478272 := by exact prefixLift 6478272
  have htrace : WordTrace (prefixWord ++ tailWord_6478272) baseStart_6478272 baseEnd_6478272 := by
    simpa [prefixWord, tailWord_6478272, baseEnd_6478272] using wordTrace_append hprefix tailTrace_6478272
  have hstable : (prefixWord ++ tailWord_6478272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478272).length < 2 ^ (prefixWord ++ tailWord_6478272).sum := by decide
  have hdescent : baseEnd_6478272 < baseStart_6478272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478307 : List Nat := [1, 1, 1, 6, 3, 1, 3, 1, 2, 2, 2]
def baseStart_6478307 : Nat := 118140960795 + 6478307 * 2 ^ 59
def prefixEnd_6478307 : Nat := 4983230072969 + 3 ^ 40 * 6478307 * 2
def baseEnd_6478307 : Nat := 3326485318386690327769315

theorem tailTrace_6478307 : CollatzResearch.WordTrace tailWord_6478307 prefixEnd_6478307 3326485318386690327769315 := by
  unfold tailWord_6478307
  simp only [CollatzResearch.WordTrace]
  refine ⟨236283267741207620595169175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157522178494138413730112783 236283267741207620595169175)
  ·
    refine ⟨354424901611811430892753763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236283267741207620595169175 354424901611811430892753763)
    ·
      refine ⟨531637352417717146339130645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354424901611811430892753763 531637352417717146339130645)
      ·
        refine ⟨24920500894580491234646749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 531637352417717146339130645 24920500894580491234646749)
        ·
          refine ⟨9345187835467684212992531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24920500894580491234646749 9345187835467684212992531)
          ·
            refine ⟨14017781753201526319488797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9345187835467684212992531 14017781753201526319488797)
            ·
              refine ⟨5256668157450572369808299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14017781753201526319488797 5256668157450572369808299)
              ·
                refine ⟨7885002236175858554712449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5256668157450572369808299 7885002236175858554712449)
                ·
                  refine ⟨5913751677131893916034337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7885002236175858554712449 5913751677131893916034337)
                  ·
                    refine ⟨4435313757848920437025753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5913751677131893916034337 4435313757848920437025753)
                    ·
                      refine ⟨3326485318386690327769315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4435313757848920437025753 3326485318386690327769315)
                      ·
                        rfl

theorem cell23_6478307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_6478307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478307 prefixEnd_6478307 := by exact prefixLift 6478307
  have htrace : WordTrace (prefixWord ++ tailWord_6478307) baseStart_6478307 baseEnd_6478307 := by
    simpa [prefixWord, tailWord_6478307, baseEnd_6478307] using wordTrace_append hprefix tailTrace_6478307
  have hstable : (prefixWord ++ tailWord_6478307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478307).length < 2 ^ (prefixWord ++ tailWord_6478307).sum := by decide
  have hdescent : baseEnd_6478307 < baseStart_6478307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478326 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_6478326 : Nat := 118140960795 + 6478326 * 2 ^ 59
def prefixEnd_6478326 : Nat := 4983230072969 + 3 ^ 40 * 6478326 * 2
def baseEnd_6478326 : Nat := 1108831691506375251143909

theorem tailTrace_6478326 : CollatzResearch.WordTrace tailWord_6478326 prefixEnd_6478326 1108831691506375251143909 := by
  unfold tailWord_6478326
  simp only [CollatzResearch.WordTrace]
  refine ⟨14767747545508674177506927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157522640485425857893407221 14767747545508674177506927)
  ·
    refine ⟨22151621318263011266260391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14767747545508674177506927 22151621318263011266260391)
    ·
      refine ⟨33227431977394516899390587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22151621318263011266260391 33227431977394516899390587)
      ·
        refine ⟨49841147966091775349085881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33227431977394516899390587 49841147966091775349085881)
        ·
          refine ⟨37380860974568831511814411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49841147966091775349085881 37380860974568831511814411)
          ·
            refine ⟨56071291461853247267721617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37380860974568831511814411 56071291461853247267721617)
            ·
              refine ⟨42053468596389935450791213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56071291461853247267721617 42053468596389935450791213)
              ·
                refine ⟨15770050723646225794046705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42053468596389935450791213 15770050723646225794046705)
                ·
                  refine ⟨11827538042734669345535029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15770050723646225794046705 11827538042734669345535029)
                  ·
                    refine ⟨1108831691506375251143909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11827538042734669345535029 1108831691506375251143909)
                    ·
                      rfl

theorem cell23_6478326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_6478326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478326 prefixEnd_6478326 := by exact prefixLift 6478326
  have htrace : WordTrace (prefixWord ++ tailWord_6478326) baseStart_6478326 baseEnd_6478326 := by
    simpa [prefixWord, tailWord_6478326, baseEnd_6478326] using wordTrace_append hprefix tailTrace_6478326
  have hstable : (prefixWord ++ tailWord_6478326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478326).length < 2 ^ (prefixWord ++ tailWord_6478326).sum := by decide
  have hdescent : baseEnd_6478326 < baseStart_6478326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478329 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 1, 3, 4]
def baseStart_6478329 : Nat := 118140960795 + 6478329 * 2 ^ 59
def prefixEnd_6478329 : Nat := 4983230072969 + 3 ^ 40 * 6478329 * 2
def baseEnd_6478329 : Nat := 3326496614961089241694213

theorem tailTrace_6478329 : CollatzResearch.WordTrace tailWord_6478329 prefixEnd_6478329 3326496614961089241694213 := by
  unfold tailWord_6478329
  simp only [CollatzResearch.WordTrace]
  refine ⟨236284070147127918352470041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157522713431418612234980027 236284070147127918352470041)
  ·
    refine ⟨177213052610345938764352531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236284070147127918352470041 177213052610345938764352531)
    ·
      refine ⟨265819578915518908146528797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177213052610345938764352531 265819578915518908146528797)
      ·
        refine ⟨99682342093319590554948299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265819578915518908146528797 99682342093319590554948299)
        ·
          refine ⟨149523513139979385832422449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99682342093319590554948299 149523513139979385832422449)
          ·
            refine ⟨112142634854984539374316837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149523513139979385832422449 112142634854984539374316837)
            ·
              refine ⟨21026744035309601132684407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112142634854984539374316837 21026744035309601132684407)
              ·
                refine ⟨31540116052964401699026611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21026744035309601132684407 31540116052964401699026611)
                ·
                  refine ⟨47310174079446602548539917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31540116052964401699026611 47310174079446602548539917)
                  ·
                    refine ⟨17741315279792475955702469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47310174079446602548539917 17741315279792475955702469)
                    ·
                      refine ⟨3326496614961089241694213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17741315279792475955702469 3326496614961089241694213)
                      ·
                        rfl

theorem cell23_6478329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_6478329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478329 prefixEnd_6478329 := by exact prefixLift 6478329
  have htrace : WordTrace (prefixWord ++ tailWord_6478329) baseStart_6478329 baseEnd_6478329 := by
    simpa [prefixWord, tailWord_6478329, baseEnd_6478329] using wordTrace_append hprefix tailTrace_6478329
  have hstable : (prefixWord ++ tailWord_6478329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478329).length < 2 ^ (prefixWord ++ tailWord_6478329).sum := by decide
  have hdescent : baseEnd_6478329 < baseStart_6478329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478346 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_6478346 : Nat := 118140960795 + 6478346 * 2 ^ 59
def prefixEnd_6478346 : Nat := 4983230072969 + 3 ^ 40 * 6478346 * 2
def baseEnd_6478346 : Nat := 3326505344132215675181635

theorem tailTrace_6478346 : CollatzResearch.WordTrace tailWord_6478346 prefixEnd_6478346 3326505344132215675181635 := by
  unfold tailWord_6478346
  simp only [CollatzResearch.WordTrace]
  refine ⟨59071172547016582563959723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157523126792044220170559261 59071172547016582563959723)
  ·
    refine ⟨88606758820524873845939585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59071172547016582563959723 88606758820524873845939585)
    ·
      refine ⟨66455069115393655384454689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88606758820524873845939585 66455069115393655384454689)
      ·
        refine ⟨49841301836545241538341017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66455069115393655384454689 49841301836545241538341017)
        ·
          refine ⟨37380976377408931153755763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49841301836545241538341017 37380976377408931153755763)
          ·
            refine ⟨56071464566113396730633645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37380976377408931153755763 56071464566113396730633645)
            ·
              refine ⟨21026799212292523773987617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56071464566113396730633645 21026799212292523773987617)
              ·
                refine ⟨15770099409219392830490713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21026799212292523773987617 15770099409219392830490713)
                ·
                  refine ⟨11827574556914544622868035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15770099409219392830490713 11827574556914544622868035)
                  ·
                    refine ⟨17741361835371816934302053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11827574556914544622868035 17741361835371816934302053)
                    ·
                      refine ⟨3326505344132215675181635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17741361835371816934302053 3326505344132215675181635)
                      ·
                        rfl

theorem cell23_6478346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_6478346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478346 prefixEnd_6478346 := by exact prefixLift 6478346
  have htrace : WordTrace (prefixWord ++ tailWord_6478346) baseStart_6478346 baseEnd_6478346 := by
    simpa [prefixWord, tailWord_6478346, baseEnd_6478346] using wordTrace_append hprefix tailTrace_6478346
  have hstable : (prefixWord ++ tailWord_6478346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478346).length < 2 ^ (prefixWord ++ tailWord_6478346).sum := by decide
  have hdescent : baseEnd_6478346 < baseStart_6478346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478379 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 3]
def baseStart_6478379 : Nat := 118140960795 + 6478379 * 2 ^ 59
def prefixEnd_6478379 : Nat := 4983230072969 + 3 ^ 40 * 6478379 * 2
def baseEnd_6478379 : Nat := 3326522288993814046068983

theorem tailTrace_6478379 : CollatzResearch.WordTrace tailWord_6478379 prefixEnd_6478379 3326522288993814046068983 := by
  unfold tailWord_6478379
  simp only [CollatzResearch.WordTrace]
  refine ⟨236285893796946776891790191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157523929197964517927860127 236285893796946776891790191)
  ·
    refine ⟨354428840695420165337685287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236285893796946776891790191 354428840695420165337685287)
    ·
      refine ⟨531643261043130248006527931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354428840695420165337685287 531643261043130248006527931)
      ·
        refine ⟨797464891564695372009791897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531643261043130248006527931 797464891564695372009791897)
        ·
          refine ⟨598098668673521529007343923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 797464891564695372009791897 598098668673521529007343923)
          ·
            refine ⟨897148003010282293511015885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598098668673521529007343923 897148003010282293511015885)
            ·
              refine ⟨336430501128855860066630957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 897148003010282293511015885 336430501128855860066630957)
              ·
                refine ⟨126161437923320947524986609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 336430501128855860066630957 126161437923320947524986609)
                ·
                  refine ⟨94621078442490710643739957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126161437923320947524986609 94621078442490710643739957)
                  ·
                    refine ⟨8870726103983504122850621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94621078442490710643739957 8870726103983504122850621)
                    ·
                      refine ⟨3326522288993814046068983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8870726103983504122850621 3326522288993814046068983)
                      ·
                        rfl

theorem cell23_6478379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 3].length) (baseStart_6478379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478379 prefixEnd_6478379 := by exact prefixLift 6478379
  have htrace : WordTrace (prefixWord ++ tailWord_6478379) baseStart_6478379 baseEnd_6478379 := by
    simpa [prefixWord, tailWord_6478379, baseEnd_6478379] using wordTrace_append hprefix tailTrace_6478379
  have hstable : (prefixWord ++ tailWord_6478379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478379).length < 2 ^ (prefixWord ++ tailWord_6478379).sum := by decide
  have hdescent : baseEnd_6478379 < baseStart_6478379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478407 : List Nat := [1, 1, 4, 1, 4, 3, 2, 2, 1, 4]
def baseStart_6478407 : Nat := 118140960795 + 6478407 * 2 ^ 59
def prefixEnd_6478407 : Nat := 4983230072969 + 3 ^ 40 * 6478407 * 2
def baseEnd_6478407 : Nat := 1108845555484046645506285

theorem tailTrace_6478407 : CollatzResearch.WordTrace tailWord_6478407 prefixEnd_6478407 1108845555484046645506285 := by
  unfold tailWord_6478407
  simp only [CollatzResearch.WordTrace]
  refine ⟨236286915040845337673809475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157524610027230225115872983 236286915040845337673809475)
  ·
    refine ⟨354430372561268006510714213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236286915040845337673809475 354430372561268006510714213)
    ·
      refine ⟨66455694855237751220758915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354430372561268006510714213 66455694855237751220758915)
      ·
        refine ⟨99683542282856626831138373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66455694855237751220758915 99683542282856626831138373)
        ·
          refine ⟨18690664178035617530838445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99683542282856626831138373 18690664178035617530838445)
          ·
            refine ⟨7008999066763356574064417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18690664178035617530838445 7008999066763356574064417)
            ·
              refine ⟨5256749300072517430548313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7008999066763356574064417 5256749300072517430548313)
              ·
                refine ⟨3942561975054388072911235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5256749300072517430548313 3942561975054388072911235)
                ·
                  refine ⟨5913842962581582109366853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3942561975054388072911235 5913842962581582109366853)
                  ·
                    refine ⟨1108845555484046645506285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5913842962581582109366853 1108845555484046645506285)
                    ·
                      rfl

theorem cell23_6478407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_6478407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478407 prefixEnd_6478407 := by exact prefixLift 6478407
  have htrace : WordTrace (prefixWord ++ tailWord_6478407) baseStart_6478407 baseEnd_6478407 := by
    simpa [prefixWord, tailWord_6478407, baseEnd_6478407] using wordTrace_append hprefix tailTrace_6478407
  have hstable : (prefixWord ++ tailWord_6478407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478407).length < 2 ^ (prefixWord ++ tailWord_6478407).sum := by decide
  have hdescent : baseEnd_6478407 < baseStart_6478407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478434 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6478434 : Nat := 118140960795 + 6478434 * 2 ^ 59
def prefixEnd_6478434 : Nat := 4983230072969 + 3 ^ 40 * 6478434 * 2
def baseEnd_6478434 : Nat := 3326550530429811330881231

theorem tailTrace_6478434 : CollatzResearch.WordTrace tailWord_6478434 prefixEnd_6478434 3326550530429811330881231 := by
  unfold tailWord_6478434
  simp only [CollatzResearch.WordTrace]
  refine ⟨59071974952936880321260589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157525266541165014190028237 59071974952936880321260589)
  ·
    refine ⟨22151990607351330120472721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59071974952936880321260589 22151990607351330120472721)
    ·
      refine ⟨16613992955513497590354541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22151990607351330120472721 16613992955513497590354541)
      ·
        refine ⟨6230247358317561596382953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16613992955513497590354541 6230247358317561596382953)
        ·
          refine ⟨4672685518738171197287215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6230247358317561596382953 4672685518738171197287215)
          ·
            refine ⟨7009028278107256795930823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4672685518738171197287215 7009028278107256795930823)
            ·
              refine ⟨10513542417160885193896235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7009028278107256795930823 10513542417160885193896235)
              ·
                refine ⟨15770313625741327790844353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10513542417160885193896235 15770313625741327790844353)
                ·
                  refine ⟨11827735219305995843133265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15770313625741327790844353 11827735219305995843133265)
                  ·
                    refine ⟨8870801414479496882349949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11827735219305995843133265 8870801414479496882349949)
                    ·
                      refine ⟨3326550530429811330881231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8870801414479496882349949 3326550530429811330881231)
                      ·
                        rfl

theorem cell23_6478434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6478434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478434 prefixEnd_6478434 := by exact prefixLift 6478434
  have htrace : WordTrace (prefixWord ++ tailWord_6478434) baseStart_6478434 baseEnd_6478434 := by
    simpa [prefixWord, tailWord_6478434, baseEnd_6478434] using wordTrace_append hprefix tailTrace_6478434
  have hstable : (prefixWord ++ tailWord_6478434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478434).length < 2 ^ (prefixWord ++ tailWord_6478434).sum := by decide
  have hdescent : baseEnd_6478434 < baseStart_6478434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478436 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_6478436 : Nat := 118140960795 + 6478436 * 2 ^ 59
def prefixEnd_6478436 : Nat := 4983230072969 + 3 ^ 40 * 6478436 * 2
def baseEnd_6478436 : Nat := 3326551557391120323056221

theorem tailTrace_6478436 : CollatzResearch.WordTrace tailWord_6478436 prefixEnd_6478436 3326551557391120323056221 := by
  unfold tailWord_6478436
  simp only [CollatzResearch.WordTrace]
  refine ⟨118143986378870137813307581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157525315171826850417743441 118143986378870137813307581)
  ·
    refine ⟨44303994892076301679990343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118143986378870137813307581 44303994892076301679990343)
    ·
      refine ⟨66455992338114452519985515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44303994892076301679990343 66455992338114452519985515)
      ·
        refine ⟨99683988507171678779978273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66455992338114452519985515 99683988507171678779978273)
        ·
          refine ⟨74762991380378759084983705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99683988507171678779978273 74762991380378759084983705)
          ·
            refine ⟨56072243535284069313737779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74762991380378759084983705 56072243535284069313737779)
            ·
              refine ⟨84108365302926103970606669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56072243535284069313737779 84108365302926103970606669)
              ·
                refine ⟨31540636988597288988977501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84108365302926103970606669 31540636988597288988977501)
                ·
                  refine ⟨11827738870723983370866563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31540636988597288988977501 11827738870723983370866563)
                  ·
                    refine ⟨17741608306085975056299845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11827738870723983370866563 17741608306085975056299845)
                    ·
                      refine ⟨3326551557391120323056221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17741608306085975056299845 3326551557391120323056221)
                      ·
                        rfl

theorem cell23_6478436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_6478436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478436 prefixEnd_6478436 := by exact prefixLift 6478436
  have htrace : WordTrace (prefixWord ++ tailWord_6478436) baseStart_6478436 baseEnd_6478436 := by
    simpa [prefixWord, tailWord_6478436, baseEnd_6478436] using wordTrace_append hprefix tailTrace_6478436
  have hstable : (prefixWord ++ tailWord_6478436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478436).length < 2 ^ (prefixWord ++ tailWord_6478436).sum := by decide
  have hdescent : baseEnd_6478436 < baseStart_6478436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478440 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_6478440 : Nat := 118140960795 + 6478440 * 2 ^ 59
def prefixEnd_6478440 : Nat := 4983230072969 + 3 ^ 40 * 6478440 * 2
def baseEnd_6478440 : Nat := 3326553611313738307406203

theorem tailTrace_6478440 : CollatzResearch.WordTrace tailWord_6478440 prefixEnd_6478440 3326553611313738307406203 := by
  unfold tailWord_6478440
  simp only [CollatzResearch.WordTrace]
  refine ⟨118144059324862892154880387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157525412433150522873173849 118144059324862892154880387)
  ·
    refine ⟨177216088987294338232320581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118144059324862892154880387 177216088987294338232320581)
    ·
      refine ⟨33228016685117688418560109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177216088987294338232320581 33228016685117688418560109)
      ·
        refine ⟨12460506256919133156960041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33228016685117688418560109 12460506256919133156960041)
        ·
          refine ⟨9345379692689349867720031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12460506256919133156960041 9345379692689349867720031)
          ·
            refine ⟨14018069539034024801580047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9345379692689349867720031 14018069539034024801580047)
            ·
              refine ⟨21027104308551037202370071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14018069539034024801580047 21027104308551037202370071)
              ·
                refine ⟨31540656462826555803555107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21027104308551037202370071 31540656462826555803555107)
                ·
                  refine ⟨47310984694239833705332661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31540656462826555803555107 47310984694239833705332661)
                  ·
                    refine ⟨4435404815084984409874937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47310984694239833705332661 4435404815084984409874937)
                    ·
                      refine ⟨3326553611313738307406203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4435404815084984409874937 3326553611313738307406203)
                      ·
                        rfl

theorem cell23_6478440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_6478440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478440 prefixEnd_6478440 := by exact prefixLift 6478440
  have htrace : WordTrace (prefixWord ++ tailWord_6478440) baseStart_6478440 baseEnd_6478440 := by
    simpa [prefixWord, tailWord_6478440, baseEnd_6478440] using wordTrace_append hprefix tailTrace_6478440
  have hstable : (prefixWord ++ tailWord_6478440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478440).length < 2 ^ (prefixWord ++ tailWord_6478440).sum := by decide
  have hdescent : baseEnd_6478440 < baseStart_6478440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478449 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_6478449 : Nat := 118140960795 + 6478449 * 2 ^ 59
def prefixEnd_6478449 : Nat := 4983230072969 + 3 ^ 40 * 6478449 * 2
def baseEnd_6478449 : Nat := 3326558232639628772193661

theorem tailTrace_6478449 : CollatzResearch.WordTrace tailWord_6478449 prefixEnd_6478449 3326558232639628772193661 := by
  unfold tailWord_6478449
  simp only [CollatzResearch.WordTrace]
  refine ⟨236288446906693178846838401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157525631271128785897892267 236288446906693178846838401)
  ·
    refine ⟨177216335180019884135128801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236288446906693178846838401 177216335180019884135128801)
    ·
      refine ⟨132912251385014913101346601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177216335180019884135128801 132912251385014913101346601)
      ·
        refine ⟨99684188538761184826009951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132912251385014913101346601 99684188538761184826009951)
        ·
          refine ⟨149526282808141777239014927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99684188538761184826009951 149526282808141777239014927)
          ·
            refine ⟨224289424212212665858522391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149526282808141777239014927 224289424212212665858522391)
            ·
              refine ⟨336434136318318998787783587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224289424212212665858522391 336434136318318998787783587)
              ·
                refine ⟨504651204477478498181675381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336434136318318998787783587 504651204477478498181675381)
                ·
                  refine ⟨47311050419763609204532067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 504651204477478498181675381 47311050419763609204532067)
                  ·
                    refine ⟨70966575629645413806798101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47311050419763609204532067 70966575629645413806798101)
                    ·
                      refine ⟨3326558232639628772193661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70966575629645413806798101 3326558232639628772193661)
                      ·
                        rfl

theorem cell23_6478449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_6478449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478449 prefixEnd_6478449 := by exact prefixLift 6478449
  have htrace : WordTrace (prefixWord ++ tailWord_6478449) baseStart_6478449 baseEnd_6478449 := by
    simpa [prefixWord, tailWord_6478449, baseEnd_6478449] using wordTrace_append hprefix tailTrace_6478449
  have hstable : (prefixWord ++ tailWord_6478449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478449).length < 2 ^ (prefixWord ++ tailWord_6478449).sum := by decide
  have hdescent : baseEnd_6478449 < baseStart_6478449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478479 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 6]
def baseStart_6478479 : Nat := 118140960795 + 6478479 * 2 ^ 59
def prefixEnd_6478479 : Nat := 4983230072969 + 3 ^ 40 * 6478479 * 2
def baseEnd_6478479 : Nat := 3326573637059263654818523

theorem tailTrace_6478479 : CollatzResearch.WordTrace tailWord_6478479 prefixEnd_6478479 3326573637059263654818523 := by
  unfold tailWord_6478479
  simp only [CollatzResearch.WordTrace]
  refine ⟨236289541096584493970430491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157526360731056329313620327 236289541096584493970430491)
  ·
    refine ⟨354434311644876740955645737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236289541096584493970430491 354434311644876740955645737)
    ·
      refine ⟨265825733733657555716734303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354434311644876740955645737 265825733733657555716734303)
      ·
        refine ⟨398738600600486333575101455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265825733733657555716734303 398738600600486333575101455)
        ·
          refine ⟨598107900900729500362652183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398738600600486333575101455 598107900900729500362652183)
          ·
            refine ⟨897161851351094250543978275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598107900900729500362652183 897161851351094250543978275)
            ·
              refine ⟨1345742777026641375815967413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897161851351094250543978275 1345742777026641375815967413)
              ·
                refine ⟨126163385346247628982746945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1345742777026641375815967413 126163385346247628982746945)
                ·
                  refine ⟨94622539009685721737060209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126163385346247628982746945 94622539009685721737060209)
                  ·
                    refine ⟨70966904257264291302795157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94622539009685721737060209 70966904257264291302795157)
                    ·
                      refine ⟨3326573637059263654818523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70966904257264291302795157 3326573637059263654818523)
                      ·
                        rfl

theorem cell23_6478479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_6478479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478479 prefixEnd_6478479 := by exact prefixLift 6478479
  have htrace : WordTrace (prefixWord ++ tailWord_6478479) baseStart_6478479 baseEnd_6478479 := by
    simpa [prefixWord, tailWord_6478479, baseEnd_6478479] using wordTrace_append hprefix tailTrace_6478479
  have hstable : (prefixWord ++ tailWord_6478479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478479).length < 2 ^ (prefixWord ++ tailWord_6478479).sum := by decide
  have hdescent : baseEnd_6478479 < baseStart_6478479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478541 : List Nat := [1, 6, 2, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_6478541 : Nat := 118140960795 + 6478541 * 2 ^ 59
def prefixEnd_6478541 : Nat := 4983230072969 + 3 ^ 40 * 6478541 * 2
def baseEnd_6478541 : Nat := 3326605472859842412243239

theorem tailTrace_6478541 : CollatzResearch.WordTrace tailWord_6478541 prefixEnd_6478541 3326605472859842412243239 := by
  unfold tailWord_6478541
  simp only [CollatzResearch.WordTrace]
  refine ⟨236291802422359878559187477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157527868281573252372791651 236291802422359878559187477)
  ·
    refine ⟨11076178238548119307461913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 236291802422359878559187477 11076178238548119307461913)
    ·
      refine ⟨8307133678911089480596435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11076178238548119307461913 8307133678911089480596435)
      ·
        refine ⟨12460700518366634220894653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8307133678911089480596435 12460700518366634220894653)
        ·
          refine ⟨4672762694387487832835495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12460700518366634220894653 4672762694387487832835495)
          ·
            refine ⟨7009144041581231749253243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4672762694387487832835495 7009144041581231749253243)
            ·
              refine ⟨10513716062371847623879865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7009144041581231749253243 10513716062371847623879865)
              ·
                refine ⟨7885287046778885717909899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10513716062371847623879865 7885287046778885717909899)
                ·
                  refine ⟨11827930570168328576864849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7885287046778885717909899 11827930570168328576864849)
                  ·
                    refine ⟨8870947927626246432648637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11827930570168328576864849 8870947927626246432648637)
                    ·
                      refine ⟨3326605472859842412243239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8870947927626246432648637 3326605472859842412243239)
                      ·
                        rfl

theorem cell23_6478541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_6478541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478541 prefixEnd_6478541 := by exact prefixLift 6478541
  have htrace : WordTrace (prefixWord ++ tailWord_6478541) baseStart_6478541 baseEnd_6478541 := by
    simpa [prefixWord, tailWord_6478541, baseEnd_6478541] using wordTrace_append hprefix tailTrace_6478541
  have hstable : (prefixWord ++ tailWord_6478541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478541).length < 2 ^ (prefixWord ++ tailWord_6478541).sum := by decide
  have hdescent : baseEnd_6478541 < baseStart_6478541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478563 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 5]
def baseStart_6478563 : Nat := 118140960795 + 6478563 * 2 ^ 59
def prefixEnd_6478563 : Nat := 4983230072969 + 3 ^ 40 * 6478563 * 2
def baseEnd_6478563 : Nat := 3326616769434241326168137

theorem tailTrace_6478563 : CollatzResearch.WordTrace tailWord_6478563 prefixEnd_6478563 3326616769434241326168137 := by
  unfold tailWord_6478563
  simp only [CollatzResearch.WordTrace]
  refine ⟨236292604828280176316488343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157528403218853450877658895 236292604828280176316488343)
  ·
    refine ⟨354438907242420264474732515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236292604828280176316488343 354438907242420264474732515)
    ·
      refine ⟨531658360863630396712098773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354438907242420264474732515 531658360863630396712098773)
      ·
        refine ⟨12460742832741337422939815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 531658360863630396712098773 12460742832741337422939815)
        ·
          refine ⟨18691114249112006134409723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12460742832741337422939815 18691114249112006134409723)
          ·
            refine ⟨28036671373668009201614585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18691114249112006134409723 28036671373668009201614585)
            ·
              refine ⟨21027503530251006901210939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28036671373668009201614585 21027503530251006901210939)
              ·
                refine ⟨31541255295376510351816409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21027503530251006901210939 31541255295376510351816409)
                ·
                  refine ⟨23655941471532382763862307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31541255295376510351816409 23655941471532382763862307)
                  ·
                    refine ⟨35483912207298574145793461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23655941471532382763862307 35483912207298574145793461)
                    ·
                      refine ⟨3326616769434241326168137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35483912207298574145793461 3326616769434241326168137)
                      ·
                        rfl

theorem cell23_6478563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_6478563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478563 prefixEnd_6478563 := by exact prefixLift 6478563
  have htrace : WordTrace (prefixWord ++ tailWord_6478563) baseStart_6478563 baseEnd_6478563 := by
    simpa [prefixWord, tailWord_6478563, baseEnd_6478563] using wordTrace_append hprefix tailTrace_6478563
  have hstable : (prefixWord ++ tailWord_6478563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478563).length < 2 ^ (prefixWord ++ tailWord_6478563).sum := by decide
  have hdescent : baseEnd_6478563 < baseStart_6478563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478573 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_6478573 : Nat := 118140960795 + 6478573 * 2 ^ 59
def prefixEnd_6478573 : Nat := 4983230072969 + 3 ^ 40 * 6478573 * 2
def baseEnd_6478573 : Nat := 3326621904240786287043091

theorem tailTrace_6478573 : CollatzResearch.WordTrace tailWord_6478573 prefixEnd_6478573 3326621904240786287043091 := by
  unfold tailWord_6478573
  simp only [CollatzResearch.WordTrace]
  refine ⟨236292969558243948024352373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157528646372162632016234915 236292969558243948024352373)
  ·
    refine ⟨22152465896085370127283035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236292969558243948024352373 22152465896085370127283035)
    ·
      refine ⟨33228698844128055190924553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22152465896085370127283035 33228698844128055190924553)
      ·
        refine ⟨24921524133096041393193415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33228698844128055190924553 24921524133096041393193415)
        ·
          refine ⟨37382286199644062089790123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24921524133096041393193415 37382286199644062089790123)
          ·
            refine ⟨56073429299466093134685185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37382286199644062089790123 56073429299466093134685185)
            ·
              refine ⟨42055071974599569851013889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56073429299466093134685185 42055071974599569851013889)
              ·
                refine ⟨31541303980949677388260417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42055071974599569851013889 31541303980949677388260417)
                ·
                  refine ⟨23655977985712258041195313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31541303980949677388260417 23655977985712258041195313)
                  ·
                    refine ⟨17741983489284193530896485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23655977985712258041195313 17741983489284193530896485)
                    ·
                      refine ⟨3326621904240786287043091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17741983489284193530896485 3326621904240786287043091)
                      ·
                        rfl

theorem cell23_6478573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_6478573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478573 prefixEnd_6478573 := by exact prefixLift 6478573
  have htrace : WordTrace (prefixWord ++ tailWord_6478573) baseStart_6478573 baseEnd_6478573 := by
    simpa [prefixWord, tailWord_6478573, baseEnd_6478573] using wordTrace_append hprefix tailTrace_6478573
  have hstable : (prefixWord ++ tailWord_6478573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478573).length < 2 ^ (prefixWord ++ tailWord_6478573).sum := by decide
  have hdescent : baseEnd_6478573 < baseStart_6478573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478577 : List Nat := [1, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2]
def baseStart_6478577 : Nat := 118140960795 + 6478577 * 2 ^ 59
def prefixEnd_6478577 : Nat := 4983230072969 + 3 ^ 40 * 6478577 * 2
def baseEnd_6478577 : Nat := 3326623958163404271393073

theorem tailTrace_6478577 : CollatzResearch.WordTrace tailWord_6478577 prefixEnd_6478577 3326623958163404271393073 := by
  unfold tailWord_6478577
  simp only [CollatzResearch.WordTrace]
  refine ⟨236293115450229456707497985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157528743633486304471665323 236293115450229456707497985)
  ·
    refine ⟨177219836587672092530623489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236293115450229456707497985 177219836587672092530623489)
    ·
      refine ⟨132914877440754069397967617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177219836587672092530623489 132914877440754069397967617)
      ·
        refine ⟨99686158080565552048475713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132914877440754069397967617 99686158080565552048475713)
        ·
          refine ⟨74764618560424164036356785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99686158080565552048475713 74764618560424164036356785)
          ·
            refine ⟨56073463920318123027267589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74764618560424164036356785 56073463920318123027267589)
            ·
              refine ⟨10513774485059648067612673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56073463920318123027267589 10513774485059648067612673)
              ·
                refine ⟨7885330863794736050709505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10513774485059648067612673 7885330863794736050709505)
                ·
                  refine ⟨5913998147846052038032129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7885330863794736050709505 5913998147846052038032129)
                  ·
                    refine ⟨4435498610884539028524097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5913998147846052038032129 4435498610884539028524097)
                    ·
                      refine ⟨3326623958163404271393073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4435498610884539028524097 3326623958163404271393073)
                      ·
                        rfl

theorem cell23_6478577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_6478577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478577 prefixEnd_6478577 := by exact prefixLift 6478577
  have htrace : WordTrace (prefixWord ++ tailWord_6478577) baseStart_6478577 baseEnd_6478577 := by
    simpa [prefixWord, tailWord_6478577, baseEnd_6478577] using wordTrace_append hprefix tailTrace_6478577
  have hstable : (prefixWord ++ tailWord_6478577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478577).length < 2 ^ (prefixWord ++ tailWord_6478577).sum := by decide
  have hdescent : baseEnd_6478577 < baseStart_6478577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478590 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_6478590 : Nat := 118140960795 + 6478590 * 2 ^ 59
def prefixEnd_6478590 : Nat := 4983230072969 + 3 ^ 40 * 6478590 * 2
def baseEnd_6478590 : Nat := 3326630633411912720530513

theorem tailTrace_6478590 : CollatzResearch.WordTrace tailWord_6478590 prefixEnd_6478590 3326630633411912720530513 := by
  unfold tailWord_6478590
  simp only [CollatzResearch.WordTrace]
  refine ⟨29536698699897794990965153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157529059732788239951814149 29536698699897794990965153)
  ·
    refine ⟨22152524024923346243223865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29536698699897794990965153 22152524024923346243223865)
    ·
      refine ⟨16614393018692509682417899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22152524024923346243223865 16614393018692509682417899)
      ·
        refine ⟨24921589528038764523626849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16614393018692509682417899 24921589528038764523626849)
        ·
          refine ⟨18691192146029073392720137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24921589528038764523626849 18691192146029073392720137)
          ·
            refine ⟨14018394109521805044540103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18691192146029073392720137 14018394109521805044540103)
            ·
              refine ⟨21027591164282707566810155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14018394109521805044540103 21027591164282707566810155)
              ·
                refine ⟨31541386746424061350215233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21027591164282707566810155 31541386746424061350215233)
                ·
                  refine ⟨23656040059818046012661425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31541386746424061350215233 23656040059818046012661425)
                  ·
                    refine ⟨17742030044863534509496069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23656040059818046012661425 17742030044863534509496069)
                    ·
                      refine ⟨3326630633411912720530513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17742030044863534509496069 3326630633411912720530513)
                      ·
                        rfl

theorem cell23_6478590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_6478590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478590 prefixEnd_6478590 := by exact prefixLift 6478590
  have htrace : WordTrace (prefixWord ++ tailWord_6478590) baseStart_6478590 baseEnd_6478590 := by
    simpa [prefixWord, tailWord_6478590, baseEnd_6478590] using wordTrace_append hprefix tailTrace_6478590
  have hstable : (prefixWord ++ tailWord_6478590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478590).length < 2 ^ (prefixWord ++ tailWord_6478590).sum := by decide
  have hdescent : baseEnd_6478590 < baseStart_6478590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478594 : List Nat := [3, 4, 1, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_6478594 : Nat := 118140960795 + 6478594 * 2 ^ 59
def prefixEnd_6478594 : Nat := 4983230072969 + 3 ^ 40 * 6478594 * 2
def baseEnd_6478594 : Nat := 3326632687334530704880495

theorem tailTrace_6478594 : CollatzResearch.WordTrace tailWord_6478594 prefixEnd_6478594 3326632687334530704880495 := by
  unfold tailWord_6478594
  simp only [CollatzResearch.WordTrace]
  refine ⟨59073433872791967152716709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157529156994111912407244557 59073433872791967152716709)
  ·
    refine ⟨11076268851148493841134383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59073433872791967152716709 11076268851148493841134383)
    ·
      refine ⟨16614403276722740761701575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11076268851148493841134383 16614403276722740761701575)
      ·
        refine ⟨24921604915084111142552363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16614403276722740761701575 24921604915084111142552363)
        ·
          refine ⟨37382407372626166713828545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24921604915084111142552363 37382407372626166713828545)
          ·
            refine ⟨28036805529469625035371409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37382407372626166713828545 28036805529469625035371409)
            ·
              refine ⟨21027604147102218776528557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28036805529469625035371409 21027604147102218776528557)
              ·
                refine ⟨7885351555163332041198209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21027604147102218776528557 7885351555163332041198209)
                ·
                  refine ⟨5914013666372499030898657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7885351555163332041198209 5914013666372499030898657)
                  ·
                    refine ⟨4435510249779374273173993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5914013666372499030898657 4435510249779374273173993)
                    ·
                      refine ⟨3326632687334530704880495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4435510249779374273173993 3326632687334530704880495)
                      ·
                        rfl

theorem cell23_6478594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_6478594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478594 prefixEnd_6478594 := by exact prefixLift 6478594
  have htrace : WordTrace (prefixWord ++ tailWord_6478594) baseStart_6478594 baseEnd_6478594 := by
    simpa [prefixWord, tailWord_6478594, baseEnd_6478594] using wordTrace_append hprefix tailTrace_6478594
  have hstable : (prefixWord ++ tailWord_6478594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478594).length < 2 ^ (prefixWord ++ tailWord_6478594).sum := by decide
  have hdescent : baseEnd_6478594 < baseStart_6478594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478603 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 4, 5, 2]
def baseStart_6478603 : Nat := 118140960795 + 6478603 * 2 ^ 59
def prefixEnd_6478603 : Nat := 4983230072969 + 3 ^ 40 * 6478603 * 2
def baseEnd_6478603 : Nat := 3326637308660421169667953

theorem tailTrace_6478603 : CollatzResearch.WordTrace tailWord_6478603 prefixEnd_6478603 3326637308660421169667953 := by
  unfold tailWord_6478603
  simp only [CollatzResearch.WordTrace]
  refine ⟨236294063748135263147944463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157529375832090175431962975 236294063748135263147944463)
  ·
    refine ⟨354441095622202894721916695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236294063748135263147944463 354441095622202894721916695)
    ·
      refine ⟨531661643433304342082875043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354441095622202894721916695 531661643433304342082875043)
      ·
        refine ⟨797492465149956513124312565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531661643433304342082875043 797492465149956513124312565)
        ·
          refine ⟨74764918607808423105404303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 797492465149956513124312565 74764918607808423105404303)
          ·
            refine ⟨112147377911712634658106455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74764918607808423105404303 112147377911712634658106455)
            ·
              refine ⟨168221066867568951987159683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112147377911712634658106455 168221066867568951987159683)
              ·
                refine ⟨252331600301353427980739525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168221066867568951987159683 252331600301353427980739525)
                ·
                  refine ⟨47312175056503767746388661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252331600301353427980739525 47312175056503767746388661)
                  ·
                    refine ⟨4435516411547228226223937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47312175056503767746388661 4435516411547228226223937)
                    ·
                      refine ⟨3326637308660421169667953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4435516411547228226223937 3326637308660421169667953)
                      ·
                        rfl

theorem cell23_6478603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 5, 2].length) (baseStart_6478603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478603 prefixEnd_6478603 := by exact prefixLift 6478603
  have htrace : WordTrace (prefixWord ++ tailWord_6478603) baseStart_6478603 baseEnd_6478603 := by
    simpa [prefixWord, tailWord_6478603, baseEnd_6478603] using wordTrace_append hprefix tailTrace_6478603
  have hstable : (prefixWord ++ tailWord_6478603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478603).length < 2 ^ (prefixWord ++ tailWord_6478603).sum := by decide
  have hdescent : baseEnd_6478603 < baseStart_6478603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478633 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 3, 6, 2]
def baseStart_6478633 : Nat := 118140960795 + 6478633 * 2 ^ 59
def prefixEnd_6478633 : Nat := 4983230072969 + 3 ^ 40 * 6478633 * 2
def baseEnd_6478633 : Nat := 3326652713080056052292815

theorem tailTrace_6478633 : CollatzResearch.WordTrace tailWord_6478633 prefixEnd_6478633 3326652713080056052292815 := by
  unfold tailWord_6478633
  simp only [CollatzResearch.WordTrace]
  refine ⟨236295157938026578271536553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157530105292017718847691035 236295157938026578271536553)
  ·
    refine ⟨177221368453519933703652415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236295157938026578271536553 177221368453519933703652415)
    ·
      refine ⟨265832052680279900555478623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177221368453519933703652415 265832052680279900555478623)
      ·
        refine ⟨398748079020419850833217935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265832052680279900555478623 398748079020419850833217935)
        ·
          refine ⟨598122118530629776249826903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398748079020419850833217935 598122118530629776249826903)
          ·
            refine ⟨897183177795944664374740355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598122118530629776249826903 897183177795944664374740355)
            ·
              refine ⟨1345774766693916996562110533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897183177795944664374740355 1345774766693916996562110533)
              ·
                refine ⟨252332768755109436855395725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1345774766693916996562110533 252332768755109436855395725)
                ·
                  refine ⟨94624788283166038820773397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252332768755109436855395725 94624788283166038820773397)
                  ·
                    refine ⟨4435536950773408069723753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94624788283166038820773397 4435536950773408069723753)
                    ·
                      refine ⟨3326652713080056052292815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4435536950773408069723753 3326652713080056052292815)
                      ·
                        rfl

theorem cell23_6478633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 6, 2].length) (baseStart_6478633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478633 prefixEnd_6478633 := by exact prefixLift 6478633
  have htrace : WordTrace (prefixWord ++ tailWord_6478633) baseStart_6478633 baseEnd_6478633 := by
    simpa [prefixWord, tailWord_6478633, baseEnd_6478633] using wordTrace_append hprefix tailTrace_6478633
  have hstable : (prefixWord ++ tailWord_6478633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478633).length < 2 ^ (prefixWord ++ tailWord_6478633).sum := by decide
  have hdescent : baseEnd_6478633 < baseStart_6478633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478727 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 2, 3, 2]
def baseStart_6478727 : Nat := 118140960795 + 6478727 * 2 ^ 59
def prefixEnd_6478727 : Nat := 4983230072969 + 3 ^ 40 * 6478727 * 2
def baseEnd_6478727 : Nat := 3326700980261578684517383

theorem tailTrace_6478727 : CollatzResearch.WordTrace tailWord_6478727 prefixEnd_6478727 3326700980261578684517383 := by
  unfold tailWord_6478727
  simp only [CollatzResearch.WordTrace]
  refine ⟨236298586399686032325458435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157532390933124021550305623 236298586399686032325458435)
  ·
    refine ⟨354447879599529048488187653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236298586399686032325458435 354447879599529048488187653)
    ·
      refine ⟨66458977424911696591535185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354447879599529048488187653 66458977424911696591535185)
      ·
        refine ⟨49844233068683772443651389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66458977424911696591535185 49844233068683772443651389)
        ·
          refine ⟨18691587400756414666369271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49844233068683772443651389 18691587400756414666369271)
          ·
            refine ⟨28037381101134621999553907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18691587400756414666369271 28037381101134621999553907)
            ·
              refine ⟨42056071651701932999330861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28037381101134621999553907 42056071651701932999330861)
              ·
                refine ⟨15771026869388224874749073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42056071651701932999330861 15771026869388224874749073)
                ·
                  refine ⟨11828270152041168656061805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15771026869388224874749073 11828270152041168656061805)
                  ·
                    refine ⟨4435601307015438246023177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11828270152041168656061805 4435601307015438246023177)
                    ·
                      refine ⟨3326700980261578684517383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4435601307015438246023177 3326700980261578684517383)
                      ·
                        rfl

theorem cell23_6478727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_6478727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478727 prefixEnd_6478727 := by exact prefixLift 6478727
  have htrace : WordTrace (prefixWord ++ tailWord_6478727) baseStart_6478727 baseEnd_6478727 := by
    simpa [prefixWord, tailWord_6478727, baseEnd_6478727] using wordTrace_append hprefix tailTrace_6478727
  have hstable : (prefixWord ++ tailWord_6478727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478727).length < 2 ^ (prefixWord ++ tailWord_6478727).sum := by decide
  have hdescent : baseEnd_6478727 < baseStart_6478727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478751 : List Nat := [1, 1, 2, 5, 2, 1, 4, 2, 1, 1, 3]
def baseStart_6478751 : Nat := 118140960795 + 6478751 * 2 ^ 59
def prefixEnd_6478751 : Nat := 4983230072969 + 3 ^ 40 * 6478751 * 2
def baseEnd_6478751 : Nat := 3326713303797286590617273

theorem tailTrace_6478751 : CollatzResearch.WordTrace tailWord_6478751 prefixEnd_6478751 3326713303797286590617273 := by
  unfold tailWord_6478751
  simp only [CollatzResearch.WordTrace]
  refine ⟨236299461751599084424332107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157532974501066056282888071 236299461751599084424332107)
  ·
    refine ⟨354449192627398626636498161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236299461751599084424332107 354449192627398626636498161)
    ·
      refine ⟨265836894470548969977373621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354449192627398626636498161 265836894470548969977373621)
      ·
        refine ⟨24922208856613965935378777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 265836894470548969977373621 24922208856613965935378777)
        ·
          refine ⟨18691656642460474451534083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24922208856613965935378777 18691656642460474451534083)
          ·
            refine ⟨28037484963690711677301125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18691656642460474451534083 28037484963690711677301125)
            ·
              refine ⟨5257028430692008439493961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28037484963690711677301125 5257028430692008439493961)
              ·
                refine ⟨3942771323019006329620471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5257028430692008439493961 3942771323019006329620471)
                ·
                  refine ⟨5914156984528509494430707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3942771323019006329620471 5914156984528509494430707)
                  ·
                    refine ⟨8871235476792764241646061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5914156984528509494430707 8871235476792764241646061)
                    ·
                      refine ⟨3326713303797286590617273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8871235476792764241646061 3326713303797286590617273)
                      ·
                        rfl

theorem cell23_6478751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_6478751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478751 prefixEnd_6478751 := by exact prefixLift 6478751
  have htrace : WordTrace (prefixWord ++ tailWord_6478751) baseStart_6478751 baseEnd_6478751 := by
    simpa [prefixWord, tailWord_6478751, baseEnd_6478751] using wordTrace_append hprefix tailTrace_6478751
  have hstable : (prefixWord ++ tailWord_6478751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478751).length < 2 ^ (prefixWord ++ tailWord_6478751).sum := by decide
  have hdescent : baseEnd_6478751 < baseStart_6478751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478788 : List Nat := [2, 3, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_6478788 : Nat := 118140960795 + 6478788 * 2 ^ 59
def prefixEnd_6478788 : Nat := 4983230072969 + 3 ^ 40 * 6478788 * 2
def baseEnd_6478788 : Nat := 1108910767527167648618201

theorem tailTrace_6478788 : CollatzResearch.WordTrace tailWord_6478788 prefixEnd_6478788 1108910767527167648618201 := by
  unfold tailWord_6478788
  simp only [CollatzResearch.WordTrace]
  refine ⟨118150405626232519871714509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157533874168310026495619345 118150405626232519871714509)
  ·
    refine ⟨44306402109837194951892941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118150405626232519871714509 44306402109837194951892941)
    ·
      refine ⟨16614900791188948106959853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44306402109837194951892941 16614900791188948106959853)
      ·
        refine ⟨6230587796695855540109945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16614900791188948106959853 6230587796695855540109945)
        ·
          refine ⟨4672940847521891655082459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6230587796695855540109945 4672940847521891655082459)
          ·
            refine ⟨7009411271282837482623689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4672940847521891655082459 7009411271282837482623689)
            ·
              refine ⟨5257058453462128111967767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7009411271282837482623689 5257058453462128111967767)
              ·
                refine ⟨7885587680193192167951651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5257058453462128111967767 7885587680193192167951651)
                ·
                  refine ⟨11828381520289788251927477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7885587680193192167951651 11828381520289788251927477)
                  ·
                    refine ⟨1108910767527167648618201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11828381520289788251927477 1108910767527167648618201)
                    ·
                      rfl

theorem cell23_6478788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_6478788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478788 prefixEnd_6478788 := by exact prefixLift 6478788
  have htrace : WordTrace (prefixWord ++ tailWord_6478788) baseStart_6478788 baseEnd_6478788 := by
    simpa [prefixWord, tailWord_6478788, baseEnd_6478788] using wordTrace_append hprefix tailTrace_6478788
  have hstable : (prefixWord ++ tailWord_6478788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478788).length < 2 ^ (prefixWord ++ tailWord_6478788).sum := by decide
  have hdescent : baseEnd_6478788 < baseStart_6478788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478807 : List Nat := [1, 1, 3, 2, 1, 1, 2, 6, 2, 1, 3]
def baseStart_6478807 : Nat := 118140960795 + 6478807 * 2 ^ 59
def prefixEnd_6478807 : Nat := 4983230072969 + 3 ^ 40 * 6478807 * 2
def baseEnd_6478807 : Nat := 3326742058713938371517015

theorem tailTrace_6478807 : CollatzResearch.WordTrace tailWord_6478807 prefixEnd_6478807 3326742058713938371517015 := by
  unfold tailWord_6478807
  simp only [CollatzResearch.WordTrace]
  refine ⟨236301504239396205988370675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157534336159597470658913783 236301504239396205988370675)
  ·
    refine ⟨354452256359094308982556013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236301504239396205988370675 354452256359094308982556013)
    ·
      refine ⟨132919596134660365868458505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354452256359094308982556013 132919596134660365868458505)
      ·
        refine ⟨99689697100995274401343879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132919596134660365868458505 99689697100995274401343879)
        ·
          refine ⟨149534545651492911602015819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99689697100995274401343879 149534545651492911602015819)
          ·
            refine ⟨224301818477239367403023729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149534545651492911602015819 224301818477239367403023729)
            ·
              refine ⟨168226363857929525552267797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224301818477239367403023729 168226363857929525552267797)
              ·
                refine ⟨7885610805840446510262553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 168226363857929525552267797 7885610805840446510262553)
                ·
                  refine ⟨5914208104380334882696915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7885610805840446510262553 5914208104380334882696915)
                  ·
                    refine ⟨8871312156570502324045373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5914208104380334882696915 8871312156570502324045373)
                    ·
                      refine ⟨3326742058713938371517015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8871312156570502324045373 3326742058713938371517015)
                      ·
                        rfl

theorem cell23_6478807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_6478807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478807 prefixEnd_6478807 := by exact prefixLift 6478807
  have htrace : WordTrace (prefixWord ++ tailWord_6478807) baseStart_6478807 baseEnd_6478807 := by
    simpa [prefixWord, tailWord_6478807, baseEnd_6478807] using wordTrace_append hprefix tailTrace_6478807
  have hstable : (prefixWord ++ tailWord_6478807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478807).length < 2 ^ (prefixWord ++ tailWord_6478807).sum := by decide
  have hdescent : baseEnd_6478807 < baseStart_6478807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478821 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 1, 2, 4]
def baseStart_6478821 : Nat := 118140960795 + 6478821 * 2 ^ 59
def prefixEnd_6478821 : Nat := 4983230072969 + 3 ^ 40 * 6478821 * 2
def baseEnd_6478821 : Nat := 3326749247443101316741951

theorem tailTrace_6478821 : CollatzResearch.WordTrace tailWord_6478821 prefixEnd_6478821 3326749247443101316741951 := by
  unfold tailWord_6478821
  simp only [CollatzResearch.WordTrace]
  refine ⟨236302014861345486379380317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157534676574230324252920211 236302014861345486379380317)
  ·
    refine ⟨88613255573004557392267619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236302014861345486379380317 88613255573004557392267619)
    ·
      refine ⟨132919883359506836088401429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88613255573004557392267619 132919883359506836088401429)
      ·
        refine ⟨6230619532476882941643817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132919883359506836088401429 6230619532476882941643817)
        ·
          refine ⟨4672964649357662206232863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6230619532476882941643817 4672964649357662206232863)
          ·
            refine ⟨7009446974036493309349295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4672964649357662206232863 7009446974036493309349295)
            ·
              refine ⟨10514170461054739964023943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7009446974036493309349295 10514170461054739964023943)
              ·
                refine ⟨15771255691582109946035915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10514170461054739964023943 15771255691582109946035915)
                ·
                  refine ⟨23656883537373164919053873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15771255691582109946035915 23656883537373164919053873)
                  ·
                    refine ⟨17742662653029873689290405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23656883537373164919053873 17742662653029873689290405)
                    ·
                      refine ⟨3326749247443101316741951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17742662653029873689290405 3326749247443101316741951)
                      ·
                        rfl

theorem cell23_6478821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_6478821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478821 prefixEnd_6478821 := by exact prefixLift 6478821
  have htrace : WordTrace (prefixWord ++ tailWord_6478821) baseStart_6478821 baseEnd_6478821 := by
    simpa [prefixWord, tailWord_6478821, baseEnd_6478821] using wordTrace_append hprefix tailTrace_6478821
  have hstable : (prefixWord ++ tailWord_6478821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478821).length < 2 ^ (prefixWord ++ tailWord_6478821).sum := by decide
  have hdescent : baseEnd_6478821 < baseStart_6478821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478881 : List Nat := [1, 2, 3, 2, 3, 2, 1, 3, 2, 2, 2]
def baseStart_6478881 : Nat := 118140960795 + 6478881 * 2 ^ 59
def prefixEnd_6478881 : Nat := 4983230072969 + 3 ^ 40 * 6478881 * 2
def baseEnd_6478881 : Nat := 3326780056282371081991675

theorem tailTrace_6478881 : CollatzResearch.WordTrace tailWord_6478881 prefixEnd_6478881 3326780056282371081991675 := by
  unfold tailWord_6478881
  simp only [CollatzResearch.WordTrace]
  refine ⟨236304203241128116626564497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157536135494085411084376331 236304203241128116626564497)
  ·
    refine ⟨177228152430846087469923373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236304203241128116626564497 177228152430846087469923373)
    ·
      refine ⟨66460557161567282801221265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177228152430846087469923373 66460557161567282801221265)
      ·
        refine ⟨49845417871175462100915949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66460557161567282801221265 49845417871175462100915949)
        ·
          refine ⟨18692031701690798287843481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49845417871175462100915949 18692031701690798287843481)
          ·
            refine ⟨14019023776268098715882611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18692031701690798287843481 14019023776268098715882611)
            ·
              refine ⟨21028535664402148073823917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14019023776268098715882611 21028535664402148073823917)
              ·
                refine ⟨7885700874150805527683969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21028535664402148073823917 7885700874150805527683969)
                ·
                  refine ⟨5914275655613104145762977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7885700874150805527683969 5914275655613104145762977)
                  ·
                    refine ⟨4435706741709828109322233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5914275655613104145762977 4435706741709828109322233)
                    ·
                      refine ⟨3326780056282371081991675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4435706741709828109322233 3326780056282371081991675)
                      ·
                        rfl

theorem cell23_6478881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_6478881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478881 prefixEnd_6478881 := by exact prefixLift 6478881
  have htrace : WordTrace (prefixWord ++ tailWord_6478881) baseStart_6478881 baseEnd_6478881 := by
    simpa [prefixWord, tailWord_6478881, baseEnd_6478881] using wordTrace_append hprefix tailTrace_6478881
  have hstable : (prefixWord ++ tailWord_6478881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478881).length < 2 ^ (prefixWord ++ tailWord_6478881).sum := by decide
  have hdescent : baseEnd_6478881 < baseStart_6478881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478954 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_6478954 : Nat := 118140960795 + 6478954 * 2 ^ 59
def prefixEnd_6478954 : Nat := 4983230072969 + 3 ^ 40 * 6478954 * 2
def baseEnd_6478954 : Nat := 3326817540370149296378839

theorem tailTrace_6478954 : CollatzResearch.WordTrace tailWord_6478954 prefixEnd_6478954 3326817540370149296378839 := by
  unfold tailWord_6478954
  simp only [CollatzResearch.WordTrace]
  refine ⟨59076716442465912523492979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157537910513242433395981277 59076716442465912523492979)
  ·
    refine ⟨88615074663698868785239469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59076716442465912523492979 88615074663698868785239469)
    ·
      refine ⟨33230652998887075794464801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88615074663698868785239469 33230652998887075794464801)
      ·
        refine ⟨24922989749165306845848601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33230652998887075794464801 24922989749165306845848601)
        ·
          refine ⟨18692242311873980134386451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24922989749165306845848601 18692242311873980134386451)
          ·
            refine ⟨28038363467810970201579677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18692242311873980134386451 28038363467810970201579677)
            ·
              refine ⟨10514386300429113825592379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28038363467810970201579677 10514386300429113825592379)
              ·
                refine ⟨15771579450643670738388569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10514386300429113825592379 15771579450643670738388569)
                ·
                  refine ⟨11828684587982753053791427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15771579450643670738388569 11828684587982753053791427)
                  ·
                    refine ⟨17743026881974129580687141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11828684587982753053791427 17743026881974129580687141)
                    ·
                      refine ⟨3326817540370149296378839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17743026881974129580687141 3326817540370149296378839)
                      ·
                        rfl

theorem cell23_6478954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_6478954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478954 prefixEnd_6478954 := by exact prefixLift 6478954
  have htrace : WordTrace (prefixWord ++ tailWord_6478954) baseStart_6478954 baseEnd_6478954 := by
    simpa [prefixWord, tailWord_6478954, baseEnd_6478954] using wordTrace_append hprefix tailTrace_6478954
  have hstable : (prefixWord ++ tailWord_6478954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478954).length < 2 ^ (prefixWord ++ tailWord_6478954).sum := by decide
  have hdescent : baseEnd_6478954 < baseStart_6478954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478960 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 8]
def baseStart_6478960 : Nat := 118140960795 + 6478960 * 2 ^ 59
def prefixEnd_6478960 : Nat := 4983230072969 + 3 ^ 40 * 6478960 * 2
def baseEnd_6478960 : Nat := 369646735694897363655979

theorem tailTrace_6478960 : CollatzResearch.WordTrace tailWord_6478960 prefixEnd_6478960 369646735694897363655979 := by
  unfold tailWord_6478960
  simp only [CollatzResearch.WordTrace]
  refine ⟨118153542303920956559345167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157538056405227942079126889 118153542303920956559345167)
  ·
    refine ⟨177230313455881434839017751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118153542303920956559345167 177230313455881434839017751)
    ·
      refine ⟨265845470183822152258526627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177230313455881434839017751 265845470183822152258526627)
      ·
        refine ⟨398768205275733228387789941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265845470183822152258526627 398768205275733228387789941)
        ·
          refine ⟨37384519244599990161355307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 398768205275733228387789941 37384519244599990161355307)
          ·
            refine ⟨56076778866899985242032961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37384519244599990161355307 56076778866899985242032961)
            ·
              refine ⟨42057584150174988931524721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56076778866899985242032961 42057584150174988931524721)
              ·
                refine ⟨31543188112631241698643541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42057584150174988931524721 31543188112631241698643541)
                ·
                  refine ⟨369646735694897363655979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31543188112631241698643541 369646735694897363655979)
                  ·
                    rfl

theorem cell23_6478960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 8].length) (baseStart_6478960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478960 prefixEnd_6478960 := by exact prefixLift 6478960
  have htrace : WordTrace (prefixWord ++ tailWord_6478960) baseStart_6478960 baseEnd_6478960 := by
    simpa [prefixWord, tailWord_6478960, baseEnd_6478960] using wordTrace_append hprefix tailTrace_6478960
  have hstable : (prefixWord ++ tailWord_6478960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478960).length < 2 ^ (prefixWord ++ tailWord_6478960).sum := by decide
  have hdescent : baseEnd_6478960 < baseStart_6478960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6478977 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 8]
def baseStart_6478977 : Nat := 118140960795 + 6478977 * 2 ^ 59
def prefixEnd_6478977 : Nat := 4983230072969 + 3 ^ 40 * 6478977 * 2
def baseEnd_6478977 : Nat := 369647705602800300710137

theorem tailTrace_6478977 : CollatzResearch.WordTrace tailWord_6478977 prefixEnd_6478977 369647705602800300710137 := by
  unfold tailWord_6478977
  simp only [CollatzResearch.WordTrace]
  refine ⟨236307704648780325022059185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157538469765853550014706123 236307704648780325022059185)
  ·
    refine ⟨177230778486585243766544389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236307704648780325022059185 177230778486585243766544389)
    ·
      refine ⟨33230770966234733206227073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177230778486585243766544389 33230770966234733206227073)
      ·
        refine ⟨24923078224676049904670305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33230770966234733206227073 24923078224676049904670305)
        ·
          refine ⟨18692308668507037428502729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24923078224676049904670305 18692308668507037428502729)
          ·
            refine ⟨14019231501380278071377047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18692308668507037428502729 14019231501380278071377047)
            ·
              refine ⟨21028847252070417107065571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14019231501380278071377047 21028847252070417107065571)
              ·
                refine ⟨31543270878105625660598357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21028847252070417107065571 31543270878105625660598357)
                ·
                  refine ⟨369647705602800300710137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31543270878105625660598357 369647705602800300710137)
                  ·
                    rfl

theorem cell23_6478977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 8].length) (baseStart_6478977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6478977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6478977 prefixEnd_6478977 := by exact prefixLift 6478977
  have htrace : WordTrace (prefixWord ++ tailWord_6478977) baseStart_6478977 baseEnd_6478977 := by
    simpa [prefixWord, tailWord_6478977, baseEnd_6478977] using wordTrace_append hprefix tailTrace_6478977
  have hstable : (prefixWord ++ tailWord_6478977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6478977).length < 2 ^ (prefixWord ++ tailWord_6478977).sum := by decide
  have hdescent : baseEnd_6478977 < baseStart_6478977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6478977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479038 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_6479038 : Nat := 118140960795 + 6479038 * 2 ^ 59
def prefixEnd_6479038 : Nat := 4983230072969 + 3 ^ 40 * 6479038 * 2
def baseEnd_6479038 : Nat := 3326860672745126967728453

theorem tailTrace_6479038 : CollatzResearch.WordTrace tailWord_6479038 prefixEnd_6479038 3326860672745126967728453 := by
  unfold tailWord_6479038
  simp only [CollatzResearch.WordTrace]
  refine ⟨29538741187694916555003721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157539953001039554960019845 29538741187694916555003721)
  ·
    refine ⟨22154055890771187416252791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29538741187694916555003721 22154055890771187416252791)
    ·
      refine ⟨33231083836156781124379187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22154055890771187416252791 33231083836156781124379187)
      ·
        refine ⟨49846625754235171686568781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33231083836156781124379187 49846625754235171686568781)
        ·
          refine ⟨18692484657838189382463293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49846625754235171686568781 18692484657838189382463293)
          ·
            refine ⟨7009681746689321018423735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18692484657838189382463293 7009681746689321018423735)
            ·
              refine ⟨10514522620033981527635603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7009681746689321018423735 10514522620033981527635603)
              ·
                refine ⟨15771783930050972291453405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10514522620033981527635603 15771783930050972291453405)
                ·
                  refine ⟨5914418973769114609295027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15771783930050972291453405 5914418973769114609295027)
                  ·
                    refine ⟨8871628460653671913942541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5914418973769114609295027 8871628460653671913942541)
                    ·
                      refine ⟨3326860672745126967728453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8871628460653671913942541 3326860672745126967728453)
                      ·
                        rfl

theorem cell23_6479038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_6479038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479038 prefixEnd_6479038 := by exact prefixLift 6479038
  have htrace : WordTrace (prefixWord ++ tailWord_6479038) baseStart_6479038 baseEnd_6479038 := by
    simpa [prefixWord, tailWord_6479038, baseEnd_6479038] using wordTrace_append hprefix tailTrace_6479038
  have hstable : (prefixWord ++ tailWord_6479038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479038).length < 2 ^ (prefixWord ++ tailWord_6479038).sum := by decide
  have hdescent : baseEnd_6479038 < baseStart_6479038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479057 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_6479057 : Nat := 118140960795 + 6479057 * 2 ^ 59
def prefixEnd_6479057 : Nat := 4983230072969 + 3 ^ 40 * 6479057 * 2
def baseEnd_6479057 : Nat := 3326870428877562393390865

theorem tailTrace_6479057 : CollatzResearch.WordTrace tailWord_6479057 prefixEnd_6479057 3326870428877562393390865 := by
  unfold tailWord_6479057
  simp only [CollatzResearch.WordTrace]
  refine ⟨236310622488490498684971425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157540414992326999123314283 236310622488490498684971425)
  ·
    refine ⟨177232966866367874013728569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236310622488490498684971425 177232966866367874013728569)
    ·
      refine ⟨132924725149775905510296427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177232966866367874013728569 132924725149775905510296427)
      ·
        refine ⟨199387087724663858265444641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132924725149775905510296427 199387087724663858265444641)
        ·
          refine ⟨149540315793497893699083481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199387087724663858265444641 149540315793497893699083481)
          ·
            refine ⟨112155236845123420274312611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149540315793497893699083481 112155236845123420274312611)
            ·
              refine ⟨168232855267685130411468917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112155236845123420274312611 168232855267685130411468917)
              ·
                refine ⟨15771830181345480976075211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168232855267685130411468917 15771830181345480976075211)
                ·
                  refine ⟨23657745272018221464112817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15771830181345480976075211 23657745272018221464112817)
                  ·
                    refine ⟨17743308954013666098084613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23657745272018221464112817 17743308954013666098084613)
                    ·
                      refine ⟨3326870428877562393390865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17743308954013666098084613 3326870428877562393390865)
                      ·
                        rfl

theorem cell23_6479057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_6479057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479057 prefixEnd_6479057 := by exact prefixLift 6479057
  have htrace : WordTrace (prefixWord ++ tailWord_6479057) baseStart_6479057 baseEnd_6479057 := by
    simpa [prefixWord, tailWord_6479057, baseEnd_6479057] using wordTrace_append hprefix tailTrace_6479057
  have hstable : (prefixWord ++ tailWord_6479057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479057).length < 2 ^ (prefixWord ++ tailWord_6479057).sum := by decide
  have hdescent : baseEnd_6479057 < baseStart_6479057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479061 : List Nat := [1, 3, 2, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_6479061 : Nat := 118140960795 + 6479061 * 2 ^ 59
def prefixEnd_6479061 : Nat := 4983230072969 + 3 ^ 40 * 6479061 * 2
def baseEnd_6479061 : Nat := 3326872482800180377740847

theorem tailTrace_6479061 : CollatzResearch.WordTrace tailWord_6479061 prefixEnd_6479061 3326872482800180377740847 := by
  unfold tailWord_6479061
  simp only [CollatzResearch.WordTrace]
  refine ⟨236310768380476007368117037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157540512253650671578744691 236310768380476007368117037)
  ·
    refine ⟨88616538142678502763043889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236310768380476007368117037 88616538142678502763043889)
    ·
      refine ⟨66462403607008877072282917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88616538142678502763043889 66462403607008877072282917)
      ·
        refine ⟨12461700676314164451053047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66462403607008877072282917 12461700676314164451053047)
        ·
          refine ⟨18692551014471246676579571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12461700676314164451053047 18692551014471246676579571)
          ·
            refine ⟨28038826521706870014869357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18692551014471246676579571 28038826521706870014869357)
            ·
              refine ⟨10514559945640076255576009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28038826521706870014869357 10514559945640076255576009)
              ·
                refine ⟨7885919959230057191682007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10514559945640076255576009 7885919959230057191682007)
                ·
                  refine ⟨11828879938845085787523011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7885919959230057191682007 11828879938845085787523011)
                  ·
                    refine ⟨17743319908267628681284517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11828879938845085787523011 17743319908267628681284517)
                    ·
                      refine ⟨3326872482800180377740847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17743319908267628681284517 3326872482800180377740847)
                      ·
                        rfl

theorem cell23_6479061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_6479061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479061 prefixEnd_6479061 := by exact prefixLift 6479061
  have htrace : WordTrace (prefixWord ++ tailWord_6479061) baseStart_6479061 baseEnd_6479061 := by
    simpa [prefixWord, tailWord_6479061, baseEnd_6479061] using wordTrace_append hprefix tailTrace_6479061
  have hstable : (prefixWord ++ tailWord_6479061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479061).length < 2 ^ (prefixWord ++ tailWord_6479061).sum := by decide
  have hdescent : baseEnd_6479061 < baseStart_6479061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479094 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_6479094 : Nat := 118140960795 + 6479094 * 2 ^ 59
def prefixEnd_6479094 : Nat := 4983230072969 + 3 ^ 40 * 6479094 * 2
def baseEnd_6479094 : Nat := 3326889427661778748628195

theorem tailTrace_6479094 : CollatzResearch.WordTrace tailWord_6479094 prefixEnd_6479094 3326889427661778748628195 := by
  unfold tailWord_6479094
  simp only [CollatzResearch.WordTrace]
  refine ⟨14769498249334778375254271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157541314659570969336045557 14769498249334778375254271)
  ·
    refine ⟨22154247374002167562881407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14769498249334778375254271 22154247374002167562881407)
    ·
      refine ⟨33231371061003251344322111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22154247374002167562881407 33231371061003251344322111)
      ·
        refine ⟨49847056591504877016483167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33231371061003251344322111 49847056591504877016483167)
        ·
          refine ⟨74770584887257315524724751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49847056591504877016483167 74770584887257315524724751)
          ·
            refine ⟨112155877330885973287087127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74770584887257315524724751 112155877330885973287087127)
            ·
              refine ⟨168233815996328959930630691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112155877330885973287087127 168233815996328959930630691)
              ·
                refine ⟨252350723994493439895946037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168233815996328959930630691 252350723994493439895946037)
                ·
                  refine ⟨23657880374483759990244941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252350723994493439895946037 23657880374483759990244941)
                  ·
                    refine ⟨8871705140431409996341853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23657880374483759990244941 8871705140431409996341853)
                    ·
                      refine ⟨3326889427661778748628195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8871705140431409996341853 3326889427661778748628195)
                      ·
                        rfl

theorem cell23_6479094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_6479094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479094 prefixEnd_6479094 := by exact prefixLift 6479094
  have htrace : WordTrace (prefixWord ++ tailWord_6479094) baseStart_6479094 baseEnd_6479094 := by
    simpa [prefixWord, tailWord_6479094, baseEnd_6479094] using wordTrace_append hprefix tailTrace_6479094
  have hstable : (prefixWord ++ tailWord_6479094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479094).length < 2 ^ (prefixWord ++ tailWord_6479094).sum := by decide
  have hdescent : baseEnd_6479094 < baseStart_6479094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479121 : List Nat := [1, 2, 2, 1, 1, 4, 2, 4, 1, 3, 2]
def baseStart_6479121 : Nat := 118140960795 + 6479121 * 2 ^ 59
def prefixEnd_6479121 : Nat := 4983230072969 + 3 ^ 40 * 6479121 * 2
def baseEnd_6479121 : Nat := 3326903291639450142990571

theorem tailTrace_6479121 : CollatzResearch.WordTrace tailWord_6479121 prefixEnd_6479121 3326903291639450142990571 := by
  unfold tailWord_6479121
  simp only [CollatzResearch.WordTrace]
  refine ⟨236312956760258637615301217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157541971173505758410200811 236312956760258637615301217)
  ·
    refine ⟨177234717570193978211475913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236312956760258637615301217 177234717570193978211475913)
    ·
      refine ⟨132926038177645483658606935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177234717570193978211475913 132926038177645483658606935)
      ·
        refine ⟨199389057266468225487910403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132926038177645483658606935 199389057266468225487910403)
        ·
          refine ⟨299083585899702338231865605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199389057266468225487910403 299083585899702338231865605)
          ·
            refine ⟨56078172356194188418474801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299083585899702338231865605 56078172356194188418474801)
            ·
              refine ⟨42058629267145641313856101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56078172356194188418474801 42058629267145641313856101)
              ·
                refine ⟨7885992987589807746348019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42058629267145641313856101 7885992987589807746348019)
                ·
                  refine ⟨11828989481384711619522029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7885992987589807746348019 11828989481384711619522029)
                  ·
                    refine ⟨4435871055519266857320761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11828989481384711619522029 4435871055519266857320761)
                    ·
                      refine ⟨3326903291639450142990571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4435871055519266857320761 3326903291639450142990571)
                      ·
                        rfl

theorem cell23_6479121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 3, 2].length) (baseStart_6479121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479121 prefixEnd_6479121 := by exact prefixLift 6479121
  have htrace : WordTrace (prefixWord ++ tailWord_6479121) baseStart_6479121 baseEnd_6479121 := by
    simpa [prefixWord, tailWord_6479121, baseEnd_6479121] using wordTrace_append hprefix tailTrace_6479121
  have hstable : (prefixWord ++ tailWord_6479121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479121).length < 2 ^ (prefixWord ++ tailWord_6479121).sum := by decide
  have hdescent : baseEnd_6479121 < baseStart_6479121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479127 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 1, 8]
def baseStart_6479127 : Nat := 118140960795 + 6479127 * 2 ^ 59
def prefixEnd_6479127 : Nat := 4983230072969 + 3 ^ 40 * 6479127 * 2
def baseEnd_6479127 : Nat := 1108968790841125706505181

theorem tailTrace_6479127 : CollatzResearch.WordTrace tailWord_6479127 prefixEnd_6479127 1108968790841125706505181 := by
  unfold tailWord_6479127
  simp only [CollatzResearch.WordTrace]
  refine ⟨236313175598236900640019635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157542117065491267093346423 236313175598236900640019635)
  ·
    refine ⟨354469763397355350960029453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236313175598236900640019635 354469763397355350960029453)
    ·
      refine ⟨132926161274008256610011045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354469763397355350960029453 132926161274008256610011045)
      ·
        refine ⟨24923655238876548114377071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132926161274008256610011045 24923655238876548114377071)
        ·
          refine ⟨37385482858314822171565607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24923655238876548114377071 37385482858314822171565607)
          ·
            refine ⟨56078224287472233257348411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37385482858314822171565607 56078224287472233257348411)
            ·
              refine ⟨84117336431208349886022617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56078224287472233257348411 84117336431208349886022617)
              ·
                refine ⟨63088002323406262414516963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84117336431208349886022617 63088002323406262414516963)
                ·
                  refine ⟨94632003485109393621775445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63088002323406262414516963 94632003485109393621775445)
                  ·
                    refine ⟨1108968790841125706505181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94632003485109393621775445 1108968790841125706505181)
                    ·
                      rfl

theorem cell23_6479127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_6479127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479127 prefixEnd_6479127 := by exact prefixLift 6479127
  have htrace : WordTrace (prefixWord ++ tailWord_6479127) baseStart_6479127 baseEnd_6479127 := by
    simpa [prefixWord, tailWord_6479127, baseEnd_6479127] using wordTrace_append hprefix tailTrace_6479127
  have hstable : (prefixWord ++ tailWord_6479127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479127).length < 2 ^ (prefixWord ++ tailWord_6479127).sum := by decide
  have hdescent : baseEnd_6479127 < baseStart_6479127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479137 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_6479137 : Nat := 118140960795 + 6479137 * 2 ^ 59
def prefixEnd_6479137 : Nat := 4983230072969 + 3 ^ 40 * 6479137 * 2
def baseEnd_6479137 : Nat := 3326911507329922080390497

theorem tailTrace_6479137 : CollatzResearch.WordTrace tailWord_6479137 prefixEnd_6479137 3326911507329922080390497 := by
  unfold tailWord_6479137
  simp only [CollatzResearch.WordTrace]
  refine ⟨236313540328200672347883665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157542360218800448231922443 236313540328200672347883665)
  ·
    refine ⟨177235155246150504260912749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236313540328200672347883665 177235155246150504260912749)
    ·
      refine ⟨66463183217306439097842281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177235155246150504260912749 66463183217306439097842281)
      ·
        refine ⟨49847387412979829323381711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66463183217306439097842281 49847387412979829323381711)
        ·
          refine ⟨74771081119469743985072567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49847387412979829323381711 74771081119469743985072567)
          ·
            refine ⟨112156621679204615977608851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74771081119469743985072567 112156621679204615977608851)
            ·
              refine ⟨168234932518806923966413277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112156621679204615977608851 168234932518806923966413277)
              ·
                refine ⟨63088099694552596487404979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168234932518806923966413277 63088099694552596487404979)
                ·
                  refine ⟨94632149541828894731107469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63088099694552596487404979 94632149541828894731107469)
                  ·
                    refine ⟨35487056078185835524165301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94632149541828894731107469 35487056078185835524165301)
                    ·
                      refine ⟨3326911507329922080390497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35487056078185835524165301 3326911507329922080390497)
                      ·
                        rfl

theorem cell23_6479137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_6479137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479137 prefixEnd_6479137 := by exact prefixLift 6479137
  have htrace : WordTrace (prefixWord ++ tailWord_6479137) baseStart_6479137 baseEnd_6479137 := by
    simpa [prefixWord, tailWord_6479137, baseEnd_6479137] using wordTrace_append hprefix tailTrace_6479137
  have hstable : (prefixWord ++ tailWord_6479137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479137).length < 2 ^ (prefixWord ++ tailWord_6479137).sum := by decide
  have hdescent : baseEnd_6479137 < baseStart_6479137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479144 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 2, 6]
def baseStart_6479144 : Nat := 118140960795 + 6479144 * 2 ^ 59
def prefixEnd_6479144 : Nat := 4983230072969 + 3 ^ 40 * 6479144 * 2
def baseEnd_6479144 : Nat := 1108971700564834517667655

theorem tailTrace_6479144 : CollatzResearch.WordTrace tailWord_6479144 prefixEnd_6479144 1108971700564834517667655 := by
  unfold tailWord_6479144
  simp only [CollatzResearch.WordTrace]
  refine ⟨118156897819587656271694243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157542530426116875028925657 118156897819587656271694243)
  ·
    refine ⟨177235346729381484407541365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118156897819587656271694243 177235346729381484407541365)
    ·
      refine ⟨16615813755879514163207003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177235346729381484407541365 16615813755879514163207003)
      ·
        refine ⟨24923720633819271244810505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16615813755879514163207003 24923720633819271244810505)
        ·
          refine ⟨18692790475364453433607879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24923720633819271244810505 18692790475364453433607879)
          ·
            refine ⟨28039185713046680150411819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18692790475364453433607879 28039185713046680150411819)
            ·
              refine ⟨42058778569570020225617729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28039185713046680150411819 42058778569570020225617729)
              ·
                refine ⟨31544083927177515169213297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42058778569570020225617729 31544083927177515169213297)
                ·
                  refine ⟨23658062945383136376909973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31544083927177515169213297 23658062945383136376909973)
                  ·
                    refine ⟨1108971700564834517667655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23658062945383136376909973 1108971700564834517667655)
                    ·
                      rfl

theorem cell23_6479144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_6479144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479144 prefixEnd_6479144 := by exact prefixLift 6479144
  have htrace : WordTrace (prefixWord ++ tailWord_6479144) baseStart_6479144 baseEnd_6479144 := by
    simpa [prefixWord, tailWord_6479144, baseEnd_6479144] using wordTrace_append hprefix tailTrace_6479144
  have hstable : (prefixWord ++ tailWord_6479144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479144).length < 2 ^ (prefixWord ++ tailWord_6479144).sum := by decide
  have hdescent : baseEnd_6479144 < baseStart_6479144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479164 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_6479164 : Nat := 118140960795 + 6479164 * 2 ^ 59
def prefixEnd_6479164 : Nat := 4983230072969 + 3 ^ 40 * 6479164 * 2
def baseEnd_6479164 : Nat := 3326925371307593474752873

theorem tailTrace_6479164 : CollatzResearch.WordTrace tailWord_6479164 prefixEnd_6479164 3326925371307593474752873 := by
  unfold tailWord_6479164
  simp only [CollatzResearch.WordTrace]
  refine ⟨118157262549551427979558273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157543016732735237306077697 118157262549551427979558273)
  ·
    refine ⟨88617946912163570984668705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118157262549551427979558273 88617946912163570984668705)
    ·
      refine ⟨66463460184122678238501529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88617946912163570984668705 66463460184122678238501529)
      ·
        refine ⟨49847595138092008678876147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66463460184122678238501529 49847595138092008678876147)
        ·
          refine ⟨74771392707138013018314221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49847595138092008678876147 74771392707138013018314221)
          ·
            refine ⟨28039272265176754881867833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74771392707138013018314221 28039272265176754881867833)
            ·
              refine ⟨21029454198882566161400875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28039272265176754881867833 21029454198882566161400875)
              ·
                refine ⟨31544181298323849242101313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21029454198882566161400875 31544181298323849242101313)
                ·
                  refine ⟨23658135973742886931575985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31544181298323849242101313 23658135973742886931575985)
                  ·
                    refine ⟨17743601980307165198681989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23658135973742886931575985 17743601980307165198681989)
                    ·
                      refine ⟨3326925371307593474752873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17743601980307165198681989 3326925371307593474752873)
                      ·
                        rfl

theorem cell23_6479164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_6479164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479164 prefixEnd_6479164 := by exact prefixLift 6479164
  have htrace : WordTrace (prefixWord ++ tailWord_6479164) baseStart_6479164 baseEnd_6479164 := by
    simpa [prefixWord, tailWord_6479164, baseEnd_6479164] using wordTrace_append hprefix tailTrace_6479164
  have hstable : (prefixWord ++ tailWord_6479164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479164).length < 2 ^ (prefixWord ++ tailWord_6479164).sum := by decide
  have hdescent : baseEnd_6479164 < baseStart_6479164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479187 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 1, 7]
def baseStart_6479187 : Nat := 118140960795 + 6479187 * 2 ^ 59
def prefixEnd_6479187 : Nat := 4983230072969 + 3 ^ 40 * 6479187 * 2
def baseEnd_6479187 : Nat := 1108979060454215628255089

theorem tailTrace_6479187 : CollatzResearch.WordTrace tailWord_6479187 prefixEnd_6479187 1108979060454215628255089 := by
  unfold tailWord_6479187
  simp only [CollatzResearch.WordTrace]
  refine ⟨236315363978019530887203815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157543575985346353924802543 236315363978019530887203815)
  ·
    refine ⟨354473045967029296330805723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236315363978019530887203815 354473045967029296330805723)
    ·
      refine ⟨531709568950543944496208585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354473045967029296330805723 531709568950543944496208585)
      ·
        refine ⟨398782176712907958372156439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531709568950543944496208585 398782176712907958372156439)
        ·
          refine ⟨598173265069361937558234659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398782176712907958372156439 598173265069361937558234659)
          ·
            refine ⟨897259897604042906337351989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598173265069361937558234659 897259897604042906337351989)
            ·
              refine ⟨84118115400379022469126749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 897259897604042906337351989 84118115400379022469126749)
              ·
                refine ⟨31544293275142133425922531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84118115400379022469126749 31544293275142133425922531)
                ·
                  refine ⟨47316439912713200138883797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31544293275142133425922531 47316439912713200138883797)
                  ·
                    refine ⟨1108979060454215628255089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47316439912713200138883797 1108979060454215628255089)
                    ·
                      rfl

theorem cell23_6479187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 7].length) (baseStart_6479187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479187 prefixEnd_6479187 := by exact prefixLift 6479187
  have htrace : WordTrace (prefixWord ++ tailWord_6479187) baseStart_6479187 baseEnd_6479187 := by
    simpa [prefixWord, tailWord_6479187, baseEnd_6479187] using wordTrace_append hprefix tailTrace_6479187
  have hstable : (prefixWord ++ tailWord_6479187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479187).length < 2 ^ (prefixWord ++ tailWord_6479187).sum := by decide
  have hdescent : baseEnd_6479187 < baseStart_6479187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479191 : List Nat := [1, 1, 3, 2, 3, 2, 3, 3, 5]
def baseStart_6479191 : Nat := 118140960795 + 6479191 * 2 ^ 59
def prefixEnd_6479191 : Nat := 4983230072969 + 3 ^ 40 * 6479191 * 2
def baseEnd_6479191 : Nat := 369659915031696096568361

theorem tailTrace_6479191 : CollatzResearch.WordTrace tailWord_6479191 prefixEnd_6479191 369659915031696096568361 := by
  unfold tailWord_6479191
  simp only [CollatzResearch.WordTrace]
  refine ⟨236315509870005039570349427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157543673246670026380232951 236315509870005039570349427)
  ·
    refine ⟨354473264805007559355524141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236315509870005039570349427 354473264805007559355524141)
    ·
      refine ⟨132927474301877834758321553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354473264805007559355524141 132927474301877834758321553)
      ·
        refine ⟨99695605726408376068741165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132927474301877834758321553 99695605726408376068741165)
        ·
          refine ⟨37385852147403141025777937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99695605726408376068741165 37385852147403141025777937)
          ·
            refine ⟨28039389110552355769333453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37385852147403141025777937 28039389110552355769333453)
            ·
              refine ⟨10514770916457133413500045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28039389110552355769333453 10514770916457133413500045)
              ·
                refine ⟨3943039093671425030062517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10514770916457133413500045 3943039093671425030062517)
                ·
                  refine ⟨369659915031696096568361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3943039093671425030062517 369659915031696096568361)
                  ·
                    rfl

theorem cell23_6479191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 5].length) (baseStart_6479191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479191 prefixEnd_6479191 := by exact prefixLift 6479191
  have htrace : WordTrace (prefixWord ++ tailWord_6479191) baseStart_6479191 baseEnd_6479191 := by
    simpa [prefixWord, tailWord_6479191, baseEnd_6479191] using wordTrace_append hprefix tailTrace_6479191
  have hstable : (prefixWord ++ tailWord_6479191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479191).length < 2 ^ (prefixWord ++ tailWord_6479191).sum := by decide
  have hdescent : baseEnd_6479191 < baseStart_6479191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479204 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_6479204 : Nat := 118140960795 + 6479204 * 2 ^ 59
def prefixEnd_6479204 : Nat := 4983230072969 + 3 ^ 40 * 6479204 * 2
def baseEnd_6479204 : Nat := 1108981970177924439417563

theorem tailTrace_6479204 : CollatzResearch.WordTrace tailWord_6479204 prefixEnd_6479204 1108981970177924439417563 := by
  unfold tailWord_6479204
  simp only [CollatzResearch.WordTrace]
  refine ⟨118157992009478971395286333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157543989345971961860381777 118157992009478971395286333)
  ·
    refine ⟨44309247003554614273232375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118157992009478971395286333 44309247003554614273232375)
    ·
      refine ⟨66463870505331921409848563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44309247003554614273232375 66463870505331921409848563)
      ·
        refine ⟨99695805757997882114772845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66463870505331921409848563 99695805757997882114772845)
        ·
          refine ⟨37385927159249205793039817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99695805757997882114772845 37385927159249205793039817)
          ·
            refine ⟨28039445369436904344779863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37385927159249205793039817 28039445369436904344779863)
            ·
              refine ⟨42059168054155356517169795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28039445369436904344779863 42059168054155356517169795)
              ·
                refine ⟨63088752081233034775754693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42059168054155356517169795 63088752081233034775754693)
                ·
                  refine ⟨11829141015231194020454005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63088752081233034775754693 11829141015231194020454005)
                  ·
                    refine ⟨1108981970177924439417563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11829141015231194020454005 1108981970177924439417563)
                    ·
                      rfl

theorem cell23_6479204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_6479204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479204 prefixEnd_6479204 := by exact prefixLift 6479204
  have htrace : WordTrace (prefixWord ++ tailWord_6479204) baseStart_6479204 baseEnd_6479204 := by
    simpa [prefixWord, tailWord_6479204, baseEnd_6479204] using wordTrace_append hprefix tailTrace_6479204
  have hstable : (prefixWord ++ tailWord_6479204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479204).length < 2 ^ (prefixWord ++ tailWord_6479204).sum := by decide
  have hdescent : baseEnd_6479204 < baseStart_6479204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479208 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 7]
def baseStart_6479208 : Nat := 118140960795 + 6479208 * 2 ^ 59
def prefixEnd_6479208 : Nat := 4983230072969 + 3 ^ 40 * 6479208 * 2
def baseEnd_6479208 : Nat := 369660884939599033622519

theorem tailTrace_6479208 : CollatzResearch.WordTrace tailWord_6479208 prefixEnd_6479208 369660884939599033622519 := by
  unfold tailWord_6479208
  simp only [CollatzResearch.WordTrace]
  refine ⟨118158064955471725736859139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157544086607295634315812185 118158064955471725736859139)
  ·
    refine ⟨177237097433207588605288709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118158064955471725736859139 177237097433207588605288709)
    ·
      refine ⟨33231955768726422863491633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177237097433207588605288709 33231955768726422863491633)
      ·
        refine ⟨24923966826544817147618725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33231955768726422863491633 24923966826544817147618725)
        ·
          refine ⟨4673243779977153215178511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24923966826544817147618725 4673243779977153215178511)
          ·
            refine ⟨7009865669965729822767767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4673243779977153215178511 7009865669965729822767767)
            ·
              refine ⟨10514798504948594734151651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7009865669965729822767767 10514798504948594734151651)
              ·
                refine ⟨15772197757422892101227477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10514798504948594734151651 15772197757422892101227477)
                ·
                  refine ⟨369660884939599033622519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15772197757422892101227477 369660884939599033622519)
                  ·
                    rfl

theorem cell23_6479208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 7].length) (baseStart_6479208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479208 prefixEnd_6479208 := by exact prefixLift 6479208
  have htrace : WordTrace (prefixWord ++ tailWord_6479208) baseStart_6479208 baseEnd_6479208 := by
    simpa [prefixWord, tailWord_6479208, baseEnd_6479208] using wordTrace_append hprefix tailTrace_6479208
  have hstable : (prefixWord ++ tailWord_6479208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479208).length < 2 ^ (prefixWord ++ tailWord_6479208).sum := by decide
  have hdescent : baseEnd_6479208 < baseStart_6479208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479325 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_6479325 : Nat := 118140960795 + 6479325 * 2 ^ 59
def prefixEnd_6479325 : Nat := 4983230072969 + 3 ^ 40 * 6479325 * 2
def baseEnd_6479325 : Nat := 3327008041692967344839633

theorem tailTrace_6479325 : CollatzResearch.WordTrace tailWord_6479325 prefixEnd_6479325 3327008041692967344839633 := by
  unfold tailWord_6479325
  simp only [CollatzResearch.WordTrace]
  refine ⟨236320397251519580455727429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157546931501013053637151619 236320397251519580455727429)
  ·
    refine ⟨44310074484659921335448893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236320397251519580455727429 44310074484659921335448893)
    ·
      refine ⟨16616277931747470500793335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44310074484659921335448893 16616277931747470500793335)
      ·
        refine ⟨24924416897621205751190003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16616277931747470500793335 24924416897621205751190003)
        ·
          refine ⟨37386625346431808626785005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24924416897621205751190003 37386625346431808626785005)
          ·
            refine ⟨14019984504911928235044377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37386625346431808626785005 14019984504911928235044377)
            ·
              refine ⟨10514988378683946176283283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14019984504911928235044377 10514988378683946176283283)
              ·
                refine ⟨15772482568025919264424925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10514988378683946176283283 15772482568025919264424925)
                ·
                  refine ⟨5914680963009719724159347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15772482568025919264424925 5914680963009719724159347)
                  ·
                    refine ⟨8872021444514579586239021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5914680963009719724159347 8872021444514579586239021)
                    ·
                      refine ⟨3327008041692967344839633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8872021444514579586239021 3327008041692967344839633)
                      ·
                        rfl

theorem cell23_6479325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_6479325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479325 prefixEnd_6479325 := by exact prefixLift 6479325
  have htrace : WordTrace (prefixWord ++ tailWord_6479325) baseStart_6479325 baseEnd_6479325 := by
    simpa [prefixWord, tailWord_6479325, baseEnd_6479325] using wordTrace_append hprefix tailTrace_6479325
  have hstable : (prefixWord ++ tailWord_6479325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479325).length < 2 ^ (prefixWord ++ tailWord_6479325).sum := by decide
  have hdescent : baseEnd_6479325 < baseStart_6479325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479354 : List Nat := [3, 1, 1, 1, 1, 2, 5, 9]
def baseStart_6479354 : Nat := 118140960795 + 6479354 * 2 ^ 59
def prefixEnd_6479354 : Nat := 4983230072969 + 3 ^ 40 * 6479354 * 2
def baseEnd_6479354 : Nat := 123223071578961027088037

theorem tailTrace_6479354 : CollatzResearch.WordTrace tailWord_6479354 prefixEnd_6479354 123223071578961027088037 := by
  unfold tailWord_6479354
  simp only [CollatzResearch.WordTrace]
  refine ⟨59080363742103629602133279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157547636645609678939022077 59080363742103629602133279)
  ·
    refine ⟨88620545613155444403199919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59080363742103629602133279 88620545613155444403199919)
    ·
      refine ⟨132930818419733166604799879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88620545613155444403199919 132930818419733166604799879)
      ·
        refine ⟨199396227629599749907199819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132930818419733166604799879 199396227629599749907199819)
        ·
          refine ⟨299094341444399624860799729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199396227629599749907199819 299094341444399624860799729)
          ·
            refine ⟨224320756083299718645599797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299094341444399624860799729 224320756083299718645599797)
            ·
              refine ⟨21030070882809348623024981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224320756083299718645599797 21030070882809348623024981)
              ·
                refine ⟨123223071578961027088037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21030070882809348623024981 123223071578961027088037)
                ·
                  rfl

theorem cell23_6479354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 9].length) (baseStart_6479354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479354 prefixEnd_6479354 := by exact prefixLift 6479354
  have htrace : WordTrace (prefixWord ++ tailWord_6479354) baseStart_6479354 baseEnd_6479354 := by
    simpa [prefixWord, tailWord_6479354, baseEnd_6479354] using wordTrace_append hprefix tailTrace_6479354
  have hstable : (prefixWord ++ tailWord_6479354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479354).length < 2 ^ (prefixWord ++ tailWord_6479354).sum := by decide
  have hdescent : baseEnd_6479354 < baseStart_6479354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479368 : List Nat := [2, 1, 3, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_6479368 : Nat := 118140960795 + 6479368 * 2 ^ 59
def prefixEnd_6479368 : Nat := 4983230072969 + 3 ^ 40 * 6479368 * 2
def baseEnd_6479368 : Nat := 3327030121361110676601935

theorem tailTrace_6479368 : CollatzResearch.WordTrace tailWord_6479368 prefixEnd_6479368 3327030121361110676601935 := by
  unfold tailWord_6479368
  simp only [CollatzResearch.WordTrace]
  refine ⟨118160982795181899399771379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157547977060242532533028505 118160982795181899399771379)
  ·
    refine ⟨177241474192772849099657069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118160982795181899399771379 177241474192772849099657069)
    ·
      refine ⟨66465552822289818412371401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177241474192772849099657069 66465552822289818412371401)
      ·
        refine ⟨49849164616717363809278551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66465552822289818412371401 49849164616717363809278551)
        ·
          refine ⟨74773746925076045713917827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49849164616717363809278551 74773746925076045713917827)
          ·
            refine ⟨112160620387614068570876741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74773746925076045713917827 112160620387614068570876741)
            ·
              refine ⟨21030116322677637857039389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112160620387614068570876741 21030116322677637857039389)
              ·
                refine ⟨7886293621004114196389771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21030116322677637857039389 7886293621004114196389771)
                ·
                  refine ⟨11829440431506171294584657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7886293621004114196389771 11829440431506171294584657)
                  ·
                    refine ⟨8872080323629628470938493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11829440431506171294584657 8872080323629628470938493)
                    ·
                      refine ⟨3327030121361110676601935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8872080323629628470938493 3327030121361110676601935)
                      ·
                        rfl

theorem cell23_6479368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_6479368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479368 prefixEnd_6479368 := by exact prefixLift 6479368
  have htrace : WordTrace (prefixWord ++ tailWord_6479368) baseStart_6479368 baseEnd_6479368 := by
    simpa [prefixWord, tailWord_6479368, baseEnd_6479368] using wordTrace_append hprefix tailTrace_6479368
  have hstable : (prefixWord ++ tailWord_6479368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479368).length < 2 ^ (prefixWord ++ tailWord_6479368).sum := by decide
  have hdescent : baseEnd_6479368 < baseStart_6479368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479371 : List Nat := [1, 1, 1, 1, 8, 2, 9]
def baseStart_6479371 : Nat := 118140960795 + 6479371 * 2 ^ 59
def prefixEnd_6479371 : Nat := 4983230072969 + 3 ^ 40 * 6479371 * 2
def baseEnd_6479371 : Nat := 41074464960531779813141

theorem tailTrace_6479371 : CollatzResearch.WordTrace tailWord_6479371 prefixEnd_6479371 41074464960531779813141 := by
  unfold tailWord_6479371
  simp only [CollatzResearch.WordTrace]
  refine ⟨236322075009352930311901967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157548050006235286874601311 236322075009352930311901967)
  ·
    refine ⟨354483112514029395467852951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236322075009352930311901967 354483112514029395467852951)
    ·
      refine ⟨531724668771044093201779427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354483112514029395467852951 531724668771044093201779427)
      ·
        refine ⟨797587003156566139802669141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531724668771044093201779427 797587003156566139802669141)
        ·
          refine ⟨9346722693241009450812529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 797587003156566139802669141 9346722693241009450812529)
          ·
            refine ⟨7010042019930757088109397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9346722693241009450812529 7010042019930757088109397)
            ·
              refine ⟨41074464960531779813141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7010042019930757088109397 41074464960531779813141)
              ·
                rfl

theorem cell23_6479371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 9].length) (baseStart_6479371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479371 prefixEnd_6479371 := by exact prefixLift 6479371
  have htrace : WordTrace (prefixWord ++ tailWord_6479371) baseStart_6479371 baseEnd_6479371 := by
    simpa [prefixWord, tailWord_6479371, baseEnd_6479371] using wordTrace_append hprefix tailTrace_6479371
  have hstable : (prefixWord ++ tailWord_6479371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479371).length < 2 ^ (prefixWord ++ tailWord_6479371).sum := by decide
  have hdescent : baseEnd_6479371 < baseStart_6479371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479392 : List Nat := [2, 1, 1, 6, 1, 3, 2, 1, 2, 4]
def baseStart_6479392 : Nat := 118140960795 + 6479392 * 2 ^ 59
def prefixEnd_6479392 : Nat := 4983230072969 + 3 ^ 40 * 6479392 * 2
def baseEnd_6479392 : Nat := 1109014148298939527567275

theorem tailTrace_6479392 : CollatzResearch.WordTrace tailWord_6479392 prefixEnd_6479392 1109014148298939527567275 := by
  unfold tailWord_6479392
  simp only [CollatzResearch.WordTrace]
  refine ⟨118161420471138425449208215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157548560628184567265610953 118161420471138425449208215)
  ·
    refine ⟨177242130706707638173812323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118161420471138425449208215 177242130706707638173812323)
    ·
      refine ⟨265863196060061457260718485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177242130706707638173812323 265863196060061457260718485)
      ·
        refine ⟨12462337315315380809096179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 265863196060061457260718485 12462337315315380809096179)
        ·
          refine ⟨18693505972973071213644269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12462337315315380809096179 18693505972973071213644269)
          ·
            refine ⟨7010064739864901705116601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18693505972973071213644269 7010064739864901705116601)
            ·
              refine ⟨5257548554898676278837451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7010064739864901705116601 5257548554898676278837451)
              ·
                refine ⟨7886322832348014418256177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5257548554898676278837451 7886322832348014418256177)
                ·
                  refine ⟨5914742124261010813692133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7886322832348014418256177 5914742124261010813692133)
                  ·
                    refine ⟨1109014148298939527567275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5914742124261010813692133 1109014148298939527567275)
                    ·
                      rfl

theorem cell23_6479392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 2, 4].length) (baseStart_6479392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479392 prefixEnd_6479392 := by exact prefixLift 6479392
  have htrace : WordTrace (prefixWord ++ tailWord_6479392) baseStart_6479392 baseEnd_6479392 := by
    simpa [prefixWord, tailWord_6479392, baseEnd_6479392] using wordTrace_append hprefix tailTrace_6479392
  have hstable : (prefixWord ++ tailWord_6479392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479392).length < 2 ^ (prefixWord ++ tailWord_6479392).sum := by decide
  have hdescent : baseEnd_6479392 < baseStart_6479392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479404 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_6479404 : Nat := 118140960795 + 6479404 * 2 ^ 59
def prefixEnd_6479404 : Nat := 4983230072969 + 3 ^ 40 * 6479404 * 2
def baseEnd_6479404 : Nat := 3327048606664672535751769

theorem tailTrace_6479404 : CollatzResearch.WordTrace tailWord_6479404 prefixEnd_6479404 3327048606664672535751769 := by
  unfold tailWord_6479404
  simp only [CollatzResearch.WordTrace]
  refine ⟨118161639309116688473926633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157548852412155584631902177 118161639309116688473926633)
  ·
    refine ⟨88621229481837516355444975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118161639309116688473926633 88621229481837516355444975)
    ·
      refine ⟨132931844222756274533167463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88621229481837516355444975 132931844222756274533167463)
      ·
        refine ⟨199397766334134411799751195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132931844222756274533167463 199397766334134411799751195)
        ·
          refine ⟨299096649501201617699626793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199397766334134411799751195 299096649501201617699626793)
          ·
            refine ⟨224322487125901213274720095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299096649501201617699626793 224322487125901213274720095)
            ·
              refine ⟨336483730688851819912080143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224322487125901213274720095 336483730688851819912080143)
              ·
                refine ⟨504725596033277729868120215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336483730688851819912080143 504725596033277729868120215)
                ·
                  refine ⟨757088394049916594802180323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504725596033277729868120215 757088394049916594802180323)
                  ·
                    refine ⟨1135632591074874892203270485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 757088394049916594802180323 1135632591074874892203270485)
                    ·
                      refine ⟨3327048606664672535751769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1135632591074874892203270485 3327048606664672535751769)
                      ·
                        rfl

theorem cell23_6479404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_6479404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479404 prefixEnd_6479404 := by exact prefixLift 6479404
  have htrace : WordTrace (prefixWord ++ tailWord_6479404) baseStart_6479404 baseEnd_6479404 := by
    simpa [prefixWord, tailWord_6479404, baseEnd_6479404] using wordTrace_append hprefix tailTrace_6479404
  have hstable : (prefixWord ++ tailWord_6479404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479404).length < 2 ^ (prefixWord ++ tailWord_6479404).sum := by decide
  have hdescent : baseEnd_6479404 < baseStart_6479404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479438 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2]
def baseStart_6479438 : Nat := 118140960795 + 6479438 * 2 ^ 59
def prefixEnd_6479438 : Nat := 4983230072969 + 3 ^ 40 * 6479438 * 2
def baseEnd_6479438 : Nat := 3327066065006925402726613

theorem tailTrace_6479438 : CollatzResearch.WordTrace tailWord_6479438 prefixEnd_6479438 3327066065006925402726613 := by
  unfold tailWord_6479438
  simp only [CollatzResearch.WordTrace]
  refine ⟨29540564837513775094323871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157549679133406800503060645 29540564837513775094323871)
  ·
    refine ⟨44310847256270662641485807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29540564837513775094323871 44310847256270662641485807)
    ·
      refine ⟨66466270884405993962228711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44310847256270662641485807 66466270884405993962228711)
      ·
        refine ⟨99699406326608990943343067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66466270884405993962228711 99699406326608990943343067)
        ·
          refine ⟨149549109489913486415014601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99699406326608990943343067 149549109489913486415014601)
          ·
            refine ⟨112161832117435114811260951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149549109489913486415014601 112161832117435114811260951)
            ·
              refine ⟨168242748176152672216891427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112161832117435114811260951 168242748176152672216891427)
              ·
                refine ⟨252364122264229008325337141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168242748176152672216891427 252364122264229008325337141)
                ·
                  refine ⟨23659136462271469530500357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252364122264229008325337141 23659136462271469530500357)
                  ·
                    refine ⟨4436088086675900536968817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23659136462271469530500357 4436088086675900536968817)
                    ·
                      refine ⟨3327066065006925402726613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4436088086675900536968817 3327066065006925402726613)
                      ·
                        rfl

theorem cell23_6479438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_6479438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479438 prefixEnd_6479438 := by exact prefixLift 6479438
  have htrace : WordTrace (prefixWord ++ tailWord_6479438) baseStart_6479438 baseEnd_6479438 := by
    simpa [prefixWord, tailWord_6479438, baseEnd_6479438] using wordTrace_append hprefix tailTrace_6479438
  have hstable : (prefixWord ++ tailWord_6479438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479438).length < 2 ^ (prefixWord ++ tailWord_6479438).sum := by decide
  have hdescent : baseEnd_6479438 < baseStart_6479438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479441 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 1, 6, 3]
def baseStart_6479441 : Nat := 118140960795 + 6479441 * 2 ^ 59
def prefixEnd_6479441 : Nat := 4983230072969 + 3 ^ 40 * 6479441 * 2
def baseEnd_6479441 : Nat := 3327067605448888890989099

theorem tailTrace_6479441 : CollatzResearch.WordTrace tailWord_6479441 prefixEnd_6479441 3327067605448888890989099 := by
  unfold tailWord_6479441
  simp only [CollatzResearch.WordTrace]
  refine ⟨236324628119099332266950177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157549752079399554844633451 236324628119099332266950177)
  ·
    refine ⟨177243471089324499200212633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236324628119099332266950177 177243471089324499200212633)
    ·
      refine ⟨132932603316993374400159475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177243471089324499200212633 132932603316993374400159475)
      ·
        refine ⟨199398904975490061600239213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132932603316993374400159475 199398904975490061600239213)
        ·
          refine ⟨74774589365808773100089705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199398904975490061600239213 74774589365808773100089705)
          ·
            refine ⟨56080942024356579825067279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74774589365808773100089705 56080942024356579825067279)
            ·
              refine ⟨84121413036534869737600919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56080942024356579825067279 84121413036534869737600919)
              ·
                refine ⟨126182119554802304606401379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84121413036534869737600919 126182119554802304606401379)
                ·
                  refine ⟨189273179332203456909602069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126182119554802304606401379 189273179332203456909602069)
                  ·
                    refine ⟨8872180281197037042637597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 189273179332203456909602069 8872180281197037042637597)
                    ·
                      refine ⟨3327067605448888890989099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8872180281197037042637597 3327067605448888890989099)
                      ·
                        rfl

theorem cell23_6479441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_6479441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479441 prefixEnd_6479441 := by exact prefixLift 6479441
  have htrace : WordTrace (prefixWord ++ tailWord_6479441) baseStart_6479441 baseEnd_6479441 := by
    simpa [prefixWord, tailWord_6479441, baseEnd_6479441] using wordTrace_append hprefix tailTrace_6479441
  have hstable : (prefixWord ++ tailWord_6479441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479441).length < 2 ^ (prefixWord ++ tailWord_6479441).sum := by decide
  have hdescent : baseEnd_6479441 < baseStart_6479441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479461 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 9]
def baseStart_6479461 : Nat := 118140960795 + 6479461 * 2 ^ 59
def prefixEnd_6479461 : Nat := 4983230072969 + 3 ^ 40 * 6479461 * 2
def baseEnd_6479461 : Nat := 369675319451330979193223

theorem tailTrace_6479461 : CollatzResearch.WordTrace tailWord_6479461 prefixEnd_6479461 369675319451330979193223 := by
  unfold tailWord_6479461
  simp only [CollatzResearch.WordTrace]
  refine ⟨236325357579026875682678237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157550238386017917121785491 236325357579026875682678237)
  ·
    refine ⟨88622009092135078381004339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236325357579026875682678237 88622009092135078381004339)
    ·
      refine ⟨132933013638202617571506509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88622009092135078381004339 132933013638202617571506509)
      ·
        refine ⟨49849880114325981589314941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132933013638202617571506509 49849880114325981589314941)
        ·
          refine ⟨18693705042872243095993103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49849880114325981589314941 18693705042872243095993103)
          ·
            refine ⟨28040557564308364643989655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18693705042872243095993103 28040557564308364643989655)
            ·
              refine ⟨42060836346462546965984483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28040557564308364643989655 42060836346462546965984483)
              ·
                refine ⟨63091254519693820448976725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42060836346462546965984483 63091254519693820448976725)
                ·
                  refine ⟨369675319451330979193223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63091254519693820448976725 369675319451330979193223)
                  ·
                    rfl

theorem cell23_6479461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_6479461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479461 prefixEnd_6479461 := by exact prefixLift 6479461
  have htrace : WordTrace (prefixWord ++ tailWord_6479461) baseStart_6479461 baseEnd_6479461 := by
    simpa [prefixWord, tailWord_6479461, baseEnd_6479461] using wordTrace_append hprefix tailTrace_6479461
  have hstable : (prefixWord ++ tailWord_6479461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479461).length < 2 ^ (prefixWord ++ tailWord_6479461).sum := by decide
  have hdescent : baseEnd_6479461 < baseStart_6479461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479471 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 3]
def baseStart_6479471 : Nat := 118140960795 + 6479471 * 2 ^ 59
def prefixEnd_6479471 : Nat := 4983230072969 + 3 ^ 40 * 6479471 * 2
def baseEnd_6479471 : Nat := 3327083009868523773613961

theorem tailTrace_6479471 : CollatzResearch.WordTrace tailWord_6479471 prefixEnd_6479471 3327083009868523773613961 := by
  unfold tailWord_6479471
  simp only [CollatzResearch.WordTrace]
  refine ⟨236325722308990647390542267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157550481539327098260361511 236325722308990647390542267)
  ·
    refine ⟨354488583463485971085813401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236325722308990647390542267 354488583463485971085813401)
    ·
      refine ⟨265866437597614478314360051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354488583463485971085813401 265866437597614478314360051)
      ·
        refine ⟨398799656396421717471540077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265866437597614478314360051 398799656396421717471540077)
        ·
          refine ⟨149549871148658144051827529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398799656396421717471540077 149549871148658144051827529)
          ·
            refine ⟨112162403361493608038870647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149549871148658144051827529 112162403361493608038870647)
            ·
              refine ⟨168243605042240412058305971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112162403361493608038870647 168243605042240412058305971)
              ·
                refine ⟨252365407563360618087458957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168243605042240412058305971 252365407563360618087458957)
                ·
                  refine ⟨94637027836260231782797109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252365407563360618087458957 94637027836260231782797109)
                  ·
                    refine ⟨8872221359649396729637229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94637027836260231782797109 8872221359649396729637229)
                    ·
                      refine ⟨3327083009868523773613961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8872221359649396729637229 3327083009868523773613961)
                      ·
                        rfl

theorem cell23_6479471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 3].length) (baseStart_6479471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479471 prefixEnd_6479471 := by exact prefixLift 6479471
  have htrace : WordTrace (prefixWord ++ tailWord_6479471) baseStart_6479471 baseEnd_6479471 := by
    simpa [prefixWord, tailWord_6479471, baseEnd_6479471] using wordTrace_append hprefix tailTrace_6479471
  have hstable : (prefixWord ++ tailWord_6479471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479471).length < 2 ^ (prefixWord ++ tailWord_6479471).sum := by decide
  have hdescent : baseEnd_6479471 < baseStart_6479471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479489 : List Nat := [1, 2, 4, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_6479489 : Nat := 118140960795 + 6479489 * 2 ^ 59
def prefixEnd_6479489 : Nat := 4983230072969 + 3 ^ 40 * 6479489 * 2
def baseEnd_6479489 : Nat := 3327092252520304703188879

theorem tailTrace_6479489 : CollatzResearch.WordTrace tailWord_6479489 prefixEnd_6479489 3327092252520304703188879 := by
  unfold tailWord_6479489
  simp only [CollatzResearch.WordTrace]
  refine ⟨236326378822925436464697521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157550919215283624309798347 236326378822925436464697521)
  ·
    refine ⟨177244784117194077348523141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236326378822925436464697521 177244784117194077348523141)
    ·
      refine ⟨33233397021973889502848089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177244784117194077348523141 33233397021973889502848089)
      ·
        refine ⟨24925047766480417127136067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33233397021973889502848089 24925047766480417127136067)
        ·
          refine ⟨37387571649720625690704101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24925047766480417127136067 37387571649720625690704101)
          ·
            refine ⟨7010169684322617317007019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37387571649720625690704101 7010169684322617317007019)
            ·
              refine ⟨10515254526483925975510529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7010169684322617317007019 10515254526483925975510529)
              ·
                refine ⟨7886440894862944481632897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10515254526483925975510529 7886440894862944481632897)
                ·
                  refine ⟨5914830671147208361224673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7886440894862944481632897 5914830671147208361224673)
                  ·
                    refine ⟨4436123003360406270918505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5914830671147208361224673 4436123003360406270918505)
                    ·
                      refine ⟨3327092252520304703188879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4436123003360406270918505 3327092252520304703188879)
                      ·
                        rfl

theorem cell23_6479489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_6479489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479489 prefixEnd_6479489 := by exact prefixLift 6479489
  have htrace : WordTrace (prefixWord ++ tailWord_6479489) baseStart_6479489 baseEnd_6479489 := by
    simpa [prefixWord, tailWord_6479489, baseEnd_6479489] using wordTrace_append hprefix tailTrace_6479489
  have hstable : (prefixWord ++ tailWord_6479489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479489).length < 2 ^ (prefixWord ++ tailWord_6479489).sum := by decide
  have hdescent : baseEnd_6479489 < baseStart_6479489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479491 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 4, 5]
def baseStart_6479491 : Nat := 118140960795 + 6479491 * 2 ^ 59
def prefixEnd_6479491 : Nat := 4983230072969 + 3 ^ 40 * 6479491 * 2
def baseEnd_6479491 : Nat := 1109031093160537898454623

theorem tailTrace_6479491 : CollatzResearch.WordTrace tailWord_6479491 prefixEnd_6479491 1109031093160537898454623 := by
  unfold tailWord_6479491
  simp only [CollatzResearch.WordTrace]
  refine ⟨236326451768918190806270327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157550967845945460537513551 236326451768918190806270327)
  ·
    refine ⟨354489677653377286209405491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236326451768918190806270327 354489677653377286209405491)
    ·
      refine ⟨531734516480065929314108237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354489677653377286209405491 531734516480065929314108237)
      ·
        refine ⟨199400443680024723492790589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 531734516480065929314108237 199400443680024723492790589)
        ·
          refine ⟨74775166380009271309796471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199400443680024723492790589 74775166380009271309796471)
          ·
            refine ⟨112162749570013906964694707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74775166380009271309796471 112162749570013906964694707)
            ·
              refine ⟨168244124355020860447042061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112162749570013906964694707 168244124355020860447042061)
              ·
                refine ⟨63091546633132822667640773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168244124355020860447042061 63091546633132822667640773)
                ·
                  refine ⟨11829664993712404250182645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63091546633132822667640773 11829664993712404250182645)
                  ·
                    refine ⟨1109031093160537898454623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11829664993712404250182645 1109031093160537898454623)
                    ·
                      rfl

theorem cell23_6479491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 5].length) (baseStart_6479491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479491 prefixEnd_6479491 := by exact prefixLift 6479491
  have htrace : WordTrace (prefixWord ++ tailWord_6479491) baseStart_6479491 baseEnd_6479491 := by
    simpa [prefixWord, tailWord_6479491, baseEnd_6479491] using wordTrace_append hprefix tailTrace_6479491
  have hstable : (prefixWord ++ tailWord_6479491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479491).length < 2 ^ (prefixWord ++ tailWord_6479491).sum := by decide
  have hdescent : baseEnd_6479491 < baseStart_6479491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479506 : List Nat := [3, 2, 3, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_6479506 : Nat := 118140960795 + 6479506 * 2 ^ 59
def prefixEnd_6479506 : Nat := 4983230072969 + 3 ^ 40 * 6479506 * 2
def baseEnd_6479506 : Nat := 3327100981691431136676301

theorem tailTrace_6479506 : CollatzResearch.WordTrace tailWord_6479506 prefixEnd_6479506 3327100981691431136676301 := by
  unfold tailWord_6479506
  simp only [CollatzResearch.WordTrace]
  refine ⟨59081749715965962092016593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157551332575909232245377581 59081749715965962092016593)
  ·
    refine ⟨44311312286974471569012445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59081749715965962092016593 44311312286974471569012445)
    ·
      refine ⟨16616742107615426838379667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44311312286974471569012445 16616742107615426838379667)
      ·
        refine ⟨24925113161423140257569501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16616742107615426838379667 24925113161423140257569501)
        ·
          refine ⟨9346917435533677596588563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24925113161423140257569501 9346917435533677596588563)
          ·
            refine ⟨14020376153300516394882845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9346917435533677596588563 14020376153300516394882845)
            ·
              refine ⟨5257641057487693648081067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14020376153300516394882845 5257641057487693648081067)
              ·
                refine ⟨7886461586231540472121601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5257641057487693648081067 7886461586231540472121601)
                ·
                  refine ⟨5914846189673655354091201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7886461586231540472121601 5914846189673655354091201)
                  ·
                    refine ⟨4436134642255241515568401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5914846189673655354091201 4436134642255241515568401)
                    ·
                      refine ⟨3327100981691431136676301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4436134642255241515568401 3327100981691431136676301)
                      ·
                        rfl

theorem cell23_6479506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_6479506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479506 prefixEnd_6479506 := by exact prefixLift 6479506
  have htrace : WordTrace (prefixWord ++ tailWord_6479506) baseStart_6479506 baseEnd_6479506 := by
    simpa [prefixWord, tailWord_6479506, baseEnd_6479506] using wordTrace_append hprefix tailTrace_6479506
  have hstable : (prefixWord ++ tailWord_6479506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479506).length < 2 ^ (prefixWord ++ tailWord_6479506).sum := by decide
  have hdescent : baseEnd_6479506 < baseStart_6479506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479538 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_6479538 : Nat := 118140960795 + 6479538 * 2 ^ 59
def prefixEnd_6479538 : Nat := 4983230072969 + 3 ^ 40 * 6479538 * 2
def baseEnd_6479538 : Nat := 1109039137690791670492051

theorem tailTrace_6479538 : CollatzResearch.WordTrace tailWord_6479538 prefixEnd_6479538 1109039137690791670492051 := by
  unfold tailWord_6479538
  simp only [CollatzResearch.WordTrace]
  refine ⟨59082041499936979458307817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157552110666498611888820845 59082041499936979458307817)
  ·
    refine ⟨44311531124952734593730863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59082041499936979458307817 44311531124952734593730863)
    ·
      refine ⟨66467296687429101890596295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44311531124952734593730863 66467296687429101890596295)
      ·
        refine ⟨99700945031143652835894443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66467296687429101890596295 99700945031143652835894443)
        ·
          refine ⟨149551417546715479253841665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99700945031143652835894443 149551417546715479253841665)
          ·
            refine ⟨112163563160036609440381249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149551417546715479253841665 112163563160036609440381249)
            ·
              refine ⟨84122672370027457080285937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112163563160036609440381249 84122672370027457080285937)
              ·
                refine ⟨63092004277520592810214453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84122672370027457080285937 63092004277520592810214453)
                ·
                  refine ⟨5914875401017555575957605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63092004277520592810214453 5914875401017555575957605)
                  ·
                    refine ⟨1109039137690791670492051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5914875401017555575957605 1109039137690791670492051)
                    ·
                      rfl

theorem cell23_6479538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_6479538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479538 prefixEnd_6479538 := by exact prefixLift 6479538
  have htrace : WordTrace (prefixWord ++ tailWord_6479538) baseStart_6479538 baseEnd_6479538 := by
    simpa [prefixWord, tailWord_6479538, baseEnd_6479538] using wordTrace_append hprefix tailTrace_6479538
  have hstable : (prefixWord ++ tailWord_6479538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479538).length < 2 ^ (prefixWord ++ tailWord_6479538).sum := by decide
  have hdescent : baseEnd_6479538 < baseStart_6479538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479542 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_6479542 : Nat := 118140960795 + 6479542 * 2 ^ 59
def prefixEnd_6479542 : Nat := 4983230072969 + 3 ^ 40 * 6479542 * 2
def baseEnd_6479542 : Nat := 1109039822331664331942045

theorem tailTrace_6479542 : CollatzResearch.WordTrace tailWord_6479542 prefixEnd_6479542 1109039822331664331942045 := by
  unfold tailWord_6479542
  simp only [CollatzResearch.WordTrace]
  refine ⟨14770519493233339157273555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157552207927822284344251253 14770519493233339157273555)
  ·
    refine ⟨22155779239850008735910333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14770519493233339157273555 22155779239850008735910333)
    ·
      refine ⟨8308417214943753275966375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22155779239850008735910333 8308417214943753275966375)
      ·
        refine ⟨12462625822415629913949563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8308417214943753275966375 12462625822415629913949563)
        ·
          refine ⟨18693938733623444870924345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12462625822415629913949563 18693938733623444870924345)
          ·
            refine ⟨14020454050217583653193259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18693938733623444870924345 14020454050217583653193259)
            ·
              refine ⟨21030681075326375479789889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14020454050217583653193259 21030681075326375479789889)
              ·
                refine ⟨15773010806494781609842417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21030681075326375479789889 15773010806494781609842417)
                ·
                  refine ⟨11829758104871086207381813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15773010806494781609842417 11829758104871086207381813)
                  ·
                    refine ⟨1109039822331664331942045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11829758104871086207381813 1109039822331664331942045)
                    ·
                      rfl

theorem cell23_6479542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_6479542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479542 prefixEnd_6479542 := by exact prefixLift 6479542
  have htrace : WordTrace (prefixWord ++ tailWord_6479542) baseStart_6479542 baseEnd_6479542 := by
    simpa [prefixWord, tailWord_6479542, baseEnd_6479542] using wordTrace_append hprefix tailTrace_6479542
  have hstable : (prefixWord ++ tailWord_6479542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479542).length < 2 ^ (prefixWord ++ tailWord_6479542).sum := by decide
  have hdescent : baseEnd_6479542 < baseStart_6479542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479551 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 8]
def baseStart_6479551 : Nat := 118140960795 + 6479551 * 2 ^ 59
def prefixEnd_6479551 : Nat := 4983230072969 + 3 ^ 40 * 6479551 * 2
def baseEnd_6479551 : Nat := 369680454257875940068177

theorem tailTrace_6479551 : CollatzResearch.WordTrace tailWord_6479551 prefixEnd_6479551 369680454257875940068177 := by
  unfold tailWord_6479551
  simp only [CollatzResearch.WordTrace]
  refine ⟨236328640148700821053454507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157552426765800547368969671 236328640148700821053454507)
  ·
    refine ⟨354492960223051231580181761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236328640148700821053454507 354492960223051231580181761)
    ·
      refine ⟨265869720167288423685136321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354492960223051231580181761 265869720167288423685136321)
      ·
        refine ⟨199402290125466317763852241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265869720167288423685136321 199402290125466317763852241)
        ·
          refine ⟨149551717594099738322889181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199402290125466317763852241 149551717594099738322889181)
          ·
            refine ⟨56081894097787401871083443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149551717594099738322889181 56081894097787401871083443)
            ·
              refine ⟨84122841146681102806625165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56081894097787401871083443 84122841146681102806625165)
              ·
                refine ⟨31546065430005413552484437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84122841146681102806625165 31546065430005413552484437)
                ·
                  refine ⟨369680454257875940068177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31546065430005413552484437 369680454257875940068177)
                  ·
                    rfl

theorem cell23_6479551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 8].length) (baseStart_6479551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479551 prefixEnd_6479551 := by exact prefixLift 6479551
  have htrace : WordTrace (prefixWord ++ tailWord_6479551) baseStart_6479551 baseEnd_6479551 := by
    simpa [prefixWord, tailWord_6479551, baseEnd_6479551] using wordTrace_append hprefix tailTrace_6479551
  have hstable : (prefixWord ++ tailWord_6479551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479551).length < 2 ^ (prefixWord ++ tailWord_6479551).sum := by decide
  have hdescent : baseEnd_6479551 < baseStart_6479551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479606 : List Nat := [5, 1, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_6479606 : Nat := 118140960795 + 6479606 * 2 ^ 59
def prefixEnd_6479606 : Nat := 4983230072969 + 3 ^ 40 * 6479606 * 2
def baseEnd_6479606 : Nat := 1109050776585626915141947

theorem tailTrace_6479606 : CollatzResearch.WordTrace tailWord_6479606 prefixEnd_6479606 1109050776585626915141947 := by
  unfold tailWord_6479606
  simp only [CollatzResearch.WordTrace]
  refine ⟨14770665385218847840419167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157553764109001043631137781 14770665385218847840419167)
  ·
    refine ⟨22155998077828271760628751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14770665385218847840419167 22155998077828271760628751)
    ·
      refine ⟨33233997116742407640943127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22155998077828271760628751 33233997116742407640943127)
      ·
        refine ⟨49850995675113611461414691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33233997116742407640943127 49850995675113611461414691)
        ·
          refine ⟨74776493512670417192122037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49850995675113611461414691 74776493512670417192122037)
          ·
            refine ⟨7010296266812851611761441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74776493512670417192122037 7010296266812851611761441)
            ·
              refine ⟨5257722200109638708821081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7010296266812851611761441 5257722200109638708821081)
              ·
                refine ⟨3943291650082229031615811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5257722200109638708821081 3943291650082229031615811)
                ·
                  refine ⟨5914937475123343547423717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943291650082229031615811 5914937475123343547423717)
                  ·
                    refine ⟨1109050776585626915141947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5914937475123343547423717 1109050776585626915141947)
                    ·
                      rfl

theorem cell23_6479606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_6479606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479606 prefixEnd_6479606 := by exact prefixLift 6479606
  have htrace : WordTrace (prefixWord ++ tailWord_6479606) baseStart_6479606 baseEnd_6479606 := by
    simpa [prefixWord, tailWord_6479606, baseEnd_6479606] using wordTrace_append hprefix tailTrace_6479606
  have hstable : (prefixWord ++ tailWord_6479606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479606).length < 2 ^ (prefixWord ++ tailWord_6479606).sum := by decide
  have hdescent : baseEnd_6479606 < baseStart_6479606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479628 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 1, 6]
def baseStart_6479628 : Nat := 118140960795 + 6479628 * 2 ^ 59
def prefixEnd_6479628 : Nat := 4983230072969 + 3 ^ 40 * 6479628 * 2
def baseEnd_6479628 : Nat := 1109054542110426553116913

theorem tailTrace_6479628 : CollatzResearch.WordTrace tailWord_6479628 prefixEnd_6479628 1109054542110426553116913 := by
  unfold tailWord_6479628
  simp only [CollatzResearch.WordTrace]
  refine ⟨118165724284710931602003769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157554299046281242136005025 118165724284710931602003769)
  ·
    refine ⟨88624293213533198701502827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118165724284710931602003769 88624293213533198701502827)
    ·
      refine ⟨132936439820299798052254241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88624293213533198701502827 132936439820299798052254241)
      ·
        refine ⟨99702329865224848539190681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132936439820299798052254241 99702329865224848539190681)
        ·
          refine ⟨74776747398918636404393011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99702329865224848539190681 74776747398918636404393011)
          ·
            refine ⟨112165121098377954606589517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74776747398918636404393011 112165121098377954606589517)
            ·
              refine ⟨42061920411891732977471069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112165121098377954606589517 42061920411891732977471069)
              ·
                refine ⟨15773220154459399866551651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42061920411891732977471069 15773220154459399866551651)
                ·
                  refine ⟨23659830231689099799827477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15773220154459399866551651 23659830231689099799827477)
                  ·
                    refine ⟨1109054542110426553116913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23659830231689099799827477 1109054542110426553116913)
                    ·
                      rfl

theorem cell23_6479628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_6479628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479628 prefixEnd_6479628 := by exact prefixLift 6479628
  have htrace : WordTrace (prefixWord ++ tailWord_6479628) baseStart_6479628 baseEnd_6479628 := by
    simpa [prefixWord, tailWord_6479628, baseEnd_6479628] using wordTrace_append hprefix tailTrace_6479628
  have hstable : (prefixWord ++ tailWord_6479628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479628).length < 2 ^ (prefixWord ++ tailWord_6479628).sum := by decide
  have hdescent : baseEnd_6479628 < baseStart_6479628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479639 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 2, 3, 2]
def baseStart_6479639 : Nat := 118140960795 + 6479639 * 2 ^ 59
def prefixEnd_6479639 : Nat := 4983230072969 + 3 ^ 40 * 6479639 * 2
def baseEnd_6479639 : Nat := 3327169274618479116313189

theorem tailTrace_6479639 : CollatzResearch.WordTrace tailWord_6479639 prefixEnd_6479639 3327169274618479116313189 := by
  unfold tailWord_6479639
  simp only [CollatzResearch.WordTrace]
  refine ⟨236331849772382012082657971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157554566514921341388438647 236331849772382012082657971)
  ·
    refine ⟨354497774658573018123986957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236331849772382012082657971 354497774658573018123986957)
    ·
      refine ⟨132936665496964881796495109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354497774658573018123986957 132936665496964881796495109)
      ·
        refine ⟨24925624780680915336842833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132936665496964881796495109 24925624780680915336842833)
        ·
          refine ⟨18694218585510686502632125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24925624780680915336842833 18694218585510686502632125)
          ·
            refine ⟨7010331969566507438487047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18694218585510686502632125 7010331969566507438487047)
            ·
              refine ⟨10515497954349761157730571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7010331969566507438487047 10515497954349761157730571)
              ·
                refine ⟨15773246931524641736595857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10515497954349761157730571 15773246931524641736595857)
                ·
                  refine ⟨11829935198643481302446893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15773246931524641736595857 11829935198643481302446893)
                  ·
                    refine ⟨4436225699491305488417585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11829935198643481302446893 4436225699491305488417585)
                    ·
                      refine ⟨3327169274618479116313189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4436225699491305488417585 3327169274618479116313189)
                      ·
                        rfl

theorem cell23_6479639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_6479639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479639 prefixEnd_6479639 := by exact prefixLift 6479639
  have htrace : WordTrace (prefixWord ++ tailWord_6479639) baseStart_6479639 baseEnd_6479639 := by
    simpa [prefixWord, tailWord_6479639, baseEnd_6479639] using wordTrace_append hprefix tailTrace_6479639
  have hstable : (prefixWord ++ tailWord_6479639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479639).length < 2 ^ (prefixWord ++ tailWord_6479639).sum := by decide
  have hdescent : baseEnd_6479639 < baseStart_6479639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479652 : List Nat := [2, 3, 1, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_6479652 : Nat := 118140960795 + 6479652 * 2 ^ 59
def prefixEnd_6479652 : Nat := 4983230072969 + 3 ^ 40 * 6479652 * 2
def baseEnd_6479652 : Nat := 3327175949866987565450629

theorem tailTrace_6479652 : CollatzResearch.WordTrace tailWord_6479652 prefixEnd_6479652 3327175949866987565450629 := by
  unfold tailWord_6479652
  simp only [CollatzResearch.WordTrace]
  refine ⟨118166161960667457651440605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157554882614223276868587473 118166161960667457651440605)
  ·
    refine ⟨44312310735250296619290227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118166161960667457651440605 44312310735250296619290227)
    ·
      refine ⟨66468466102875444928935341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44312310735250296619290227 66468466102875444928935341)
      ·
        refine ⟨24925674788578291848350753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66468466102875444928935341 24925674788578291848350753)
        ·
          refine ⟨18694256091433718886263065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24925674788578291848350753 18694256091433718886263065)
          ·
            refine ⟨14020692068575289164697299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18694256091433718886263065 14020692068575289164697299)
            ·
              refine ⟨21031038102862933747045949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14020692068575289164697299 21031038102862933747045949)
              ·
                refine ⟨7886639288573600155142231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21031038102862933747045949 7886639288573600155142231)
                ·
                  refine ⟨11829958932860400232713347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7886639288573600155142231 11829958932860400232713347)
                  ·
                    refine ⟨17744938399290600349070021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11829958932860400232713347 17744938399290600349070021)
                    ·
                      refine ⟨3327175949866987565450629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17744938399290600349070021 3327175949866987565450629)
                      ·
                        rfl

theorem cell23_6479652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_6479652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479652 prefixEnd_6479652 := by exact prefixLift 6479652
  have htrace : WordTrace (prefixWord ++ tailWord_6479652) baseStart_6479652 baseEnd_6479652 := by
    simpa [prefixWord, tailWord_6479652, baseEnd_6479652] using wordTrace_append hprefix tailTrace_6479652
  have hstable : (prefixWord ++ tailWord_6479652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479652).length < 2 ^ (prefixWord ++ tailWord_6479652).sum := by decide
  have hdescent : baseEnd_6479652 < baseStart_6479652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479679 : List Nat := [1, 1, 2, 2, 6, 1, 3, 1, 2, 4]
def baseStart_6479679 : Nat := 118140960795 + 6479679 * 2 ^ 59
def prefixEnd_6479679 : Nat := 4983230072969 + 3 ^ 40 * 6479679 * 2
def baseEnd_6479679 : Nat := 1109063271281552986604335

theorem tailTrace_6479679 : CollatzResearch.WordTrace tailWord_6479679 prefixEnd_6479679 1109063271281552986604335 := by
  unfold tailWord_6479679
  simp only [CollatzResearch.WordTrace]
  refine ⟨236333308692237098914114091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157555539128158065942742727 236333308692237098914114091)
  ·
    refine ⟨354499963038355648371171137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236333308692237098914114091 354499963038355648371171137)
    ·
      refine ⟨265874972278766736278378353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354499963038355648371171137 265874972278766736278378353)
      ·
        refine ⟨199406229209075052208783765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265874972278766736278378353 199406229209075052208783765)
        ·
          refine ⟨9347166994175393072286739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 199406229209075052208783765 9347166994175393072286739)
          ·
            refine ⟨14020750491263089608430109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9347166994175393072286739 14020750491263089608430109)
            ·
              refine ⟨5257781434223658603161291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14020750491263089608430109 5257781434223658603161291)
              ·
                refine ⟨7886672151335487904741937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5257781434223658603161291 7886672151335487904741937)
                ·
                  refine ⟨5915004113501615928556453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7886672151335487904741937 5915004113501615928556453)
                  ·
                    refine ⟨1109063271281552986604335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5915004113501615928556453 1109063271281552986604335)
                    ·
                      rfl

theorem cell23_6479679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 2, 4].length) (baseStart_6479679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479679 prefixEnd_6479679 := by exact prefixLift 6479679
  have htrace : WordTrace (prefixWord ++ tailWord_6479679) baseStart_6479679 baseEnd_6479679 := by
    simpa [prefixWord, tailWord_6479679, baseEnd_6479679] using wordTrace_append hprefix tailTrace_6479679
  have hstable : (prefixWord ++ tailWord_6479679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479679).length < 2 ^ (prefixWord ++ tailWord_6479679).sum := by decide
  have hdescent : baseEnd_6479679 < baseStart_6479679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479686 : List Nat := [6, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_6479686 : Nat := 118140960795 + 6479686 * 2 ^ 59
def prefixEnd_6479686 : Nat := 4983230072969 + 3 ^ 40 * 6479686 * 2
def baseEnd_6479686 : Nat := 3327193408209240432425473

theorem tailTrace_6479686 : CollatzResearch.WordTrace tailWord_6479686 prefixEnd_6479686 3327193408209240432425473 := by
  unfold tailWord_6479686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7385423875100366847175591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157555709335474492739745941 7385423875100366847175591)
  ·
    refine ⟨11078135812650550270763387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7385423875100366847175591 11078135812650550270763387)
    ·
      refine ⟨16617203718975825406145081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11078135812650550270763387 16617203718975825406145081)
      ·
        refine ⟨12462902789231869054608811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16617203718975825406145081 12462902789231869054608811)
        ·
          refine ⟨18694354183847803581913217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12462902789231869054608811 18694354183847803581913217)
          ·
            refine ⟨14020765637885852686434913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18694354183847803581913217 14020765637885852686434913)
            ·
              refine ⟨10515574228414389514826185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14020765637885852686434913 10515574228414389514826185)
              ·
                refine ⟨7886680671310792136119639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10515574228414389514826185 7886680671310792136119639)
                ·
                  refine ⟨11830021006966188204179459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7886680671310792136119639 11830021006966188204179459)
                  ·
                    refine ⟨17745031510449282306269189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11830021006966188204179459 17745031510449282306269189)
                    ·
                      refine ⟨3327193408209240432425473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17745031510449282306269189 3327193408209240432425473)
                      ·
                        rfl

theorem cell23_6479686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_6479686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479686 prefixEnd_6479686 := by exact prefixLift 6479686
  have htrace : WordTrace (prefixWord ++ tailWord_6479686) baseStart_6479686 baseEnd_6479686 := by
    simpa [prefixWord, tailWord_6479686, baseEnd_6479686] using wordTrace_append hprefix tailTrace_6479686
  have hstable : (prefixWord ++ tailWord_6479686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479686).length < 2 ^ (prefixWord ++ tailWord_6479686).sum := by decide
  have hdescent : baseEnd_6479686 < baseStart_6479686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479692 : List Nat := [2, 2, 1, 3, 4, 2, 2, 7]
def baseStart_6479692 : Nat := 118140960795 + 6479692 * 2 ^ 59
def prefixEnd_6479692 : Nat := 4983230072969 + 3 ^ 40 * 6479692 * 2
def baseEnd_6479692 : Nat := 123229499596043237368535

theorem tailTrace_6479692 : CollatzResearch.WordTrace tailWord_6479692 prefixEnd_6479692 123229499596043237368535 := by
  unfold tailWord_6479692
  simp only [CollatzResearch.WordTrace]
  refine ⟨118166891420595001067168665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157555855227460001422891553 118166891420595001067168665)
  ·
    refine ⟨88625168565446250800376499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118166891420595001067168665 88625168565446250800376499)
    ·
      refine ⟨132937752848169376200564749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88625168565446250800376499 132937752848169376200564749)
      ·
        refine ⟨49851657318063516075211781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132937752848169376200564749 49851657318063516075211781)
        ·
          refine ⟨9347185747136909264102209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49851657318063516075211781 9347185747136909264102209)
          ·
            refine ⟨7010389310352681948076657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9347185747136909264102209 7010389310352681948076657)
            ·
              refine ⟨5257791982764511461057493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7010389310352681948076657 5257791982764511461057493)
              ·
                refine ⟨123229499596043237368535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5257791982764511461057493 123229499596043237368535)
                ·
                  rfl

theorem cell23_6479692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 7].length) (baseStart_6479692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479692 prefixEnd_6479692 := by exact prefixLift 6479692
  have htrace : WordTrace (prefixWord ++ tailWord_6479692) baseStart_6479692 baseEnd_6479692 := by
    simpa [prefixWord, tailWord_6479692, baseEnd_6479692] using wordTrace_append hprefix tailTrace_6479692
  have hstable : (prefixWord ++ tailWord_6479692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479692).length < 2 ^ (prefixWord ++ tailWord_6479692).sum := by decide
  have hdescent : baseEnd_6479692 < baseStart_6479692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479703 : List Nat := [1, 1, 3, 2, 5, 2, 1, 3, 1, 2, 2]
def baseStart_6479703 : Nat := 118140960795 + 6479703 * 2 ^ 59
def prefixEnd_6479703 : Nat := 4983230072969 + 3 ^ 40 * 6479703 * 2
def baseEnd_6479703 : Nat := 3327202137380366865912895

theorem tailTrace_6479703 : CollatzResearch.WordTrace tailWord_6479703 prefixEnd_6479703 3327202137380366865912895 := by
  unfold tailWord_6479703
  simp only [CollatzResearch.WordTrace]
  refine ⟨236334184044150151012987763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157556122696100100675325175 236334184044150151012987763)
  ·
    refine ⟨354501276066225226519481645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236334184044150151012987763 354501276066225226519481645)
    ·
      refine ⟨132937978524834459944805617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354501276066225226519481645 132937978524834459944805617)
      ·
        refine ⟨99703483893625844958604213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132937978524834459944805617 99703483893625844958604213)
        ·
          refine ⟨9347201615027422964869145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99703483893625844958604213 9347201615027422964869145)
          ·
            refine ⟨7010401211270567223651859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9347201615027422964869145 7010401211270567223651859)
            ·
              refine ⟨10515601816905850835477789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7010401211270567223651859 10515601816905850835477789)
              ·
                refine ⟨3943350681339694063304171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10515601816905850835477789 3943350681339694063304171)
                ·
                  refine ⟨5915026022009541094956257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943350681339694063304171 5915026022009541094956257)
                  ·
                    refine ⟨4436269516507155821217193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5915026022009541094956257 4436269516507155821217193)
                    ·
                      refine ⟨3327202137380366865912895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4436269516507155821217193 3327202137380366865912895)
                      ·
                        rfl

theorem cell23_6479703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_6479703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479703 prefixEnd_6479703 := by exact prefixLift 6479703
  have htrace : WordTrace (prefixWord ++ tailWord_6479703) baseStart_6479703 baseEnd_6479703 := by
    simpa [prefixWord, tailWord_6479703, baseEnd_6479703] using wordTrace_append hprefix tailTrace_6479703
  have hstable : (prefixWord ++ tailWord_6479703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479703).length < 2 ^ (prefixWord ++ tailWord_6479703).sum := by decide
  have hdescent : baseEnd_6479703 < baseStart_6479703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479728 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 5]
def baseStart_6479728 : Nat := 118140960795 + 6479728 * 2 ^ 59
def prefixEnd_6479728 : Nat := 4983230072969 + 3 ^ 40 * 6479728 * 2
def baseEnd_6479728 : Nat := 3327214974396729268100279

theorem tailTrace_6479728 : CollatzResearch.WordTrace tailWord_6479728 prefixEnd_6479728 3327214974396729268100279 := by
  unfold tailWord_6479728
  simp only [CollatzResearch.WordTrace]
  refine ⟨118167547934529790141323919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157556730579373053521765225 118167547934529790141323919)
  ·
    refine ⟨177251321901794685211985879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118167547934529790141323919 177251321901794685211985879)
    ·
      refine ⟨265876982852692027817978819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177251321901794685211985879 265876982852692027817978819)
      ·
        refine ⟨398815474279038041726968229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265876982852692027817978819 398815474279038041726968229)
        ·
          refine ⟨74777901427319632823806543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 398815474279038041726968229 74777901427319632823806543)
          ·
            refine ⟨112166852140979449235709815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74777901427319632823806543 112166852140979449235709815)
            ·
              refine ⟨168250278211469173853564723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112166852140979449235709815 168250278211469173853564723)
              ·
                refine ⟨252375417317203760780347085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168250278211469173853564723 252375417317203760780347085)
                ·
                  refine ⟨94640781493951410292630157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252375417317203760780347085 94640781493951410292630157)
                  ·
                    refine ⟨35490293060231778859736309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94640781493951410292630157 35490293060231778859736309)
                    ·
                      refine ⟨3327214974396729268100279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35490293060231778859736309 3327214974396729268100279)
                      ·
                        rfl

theorem cell23_6479728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_6479728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479728 prefixEnd_6479728 := by exact prefixLift 6479728
  have htrace : WordTrace (prefixWord ++ tailWord_6479728) baseStart_6479728 baseEnd_6479728 := by
    simpa [prefixWord, tailWord_6479728, baseEnd_6479728] using wordTrace_append hprefix tailTrace_6479728
  have hstable : (prefixWord ++ tailWord_6479728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479728).length < 2 ^ (prefixWord ++ tailWord_6479728).sum := by decide
  have hdescent : baseEnd_6479728 < baseStart_6479728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479762 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_6479762 : Nat := 118140960795 + 6479762 * 2 ^ 59
def prefixEnd_6479762 : Nat := 4983230072969 + 3 ^ 40 * 6479762 * 2
def baseEnd_6479762 : Nat := 3327232432738982135075123

theorem tailTrace_6479762 : CollatzResearch.WordTrace tailWord_6479762 prefixEnd_6479762 3327232432738982135075123 := by
  unfold tailWord_6479762
  simp only [CollatzResearch.WordTrace]
  refine ⟨59084083987734101022346385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157557557300624269392923693 59084083987734101022346385)
  ·
    refine ⟨44313062990800575766759789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59084083987734101022346385 44313062990800575766759789)
    ·
      refine ⟨16617398621550215912534921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44313062990800575766759789 16617398621550215912534921)
      ·
        refine ⟨12463048966162661934401191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16617398621550215912534921 12463048966162661934401191)
        ·
          refine ⟨18694573449243992901601787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12463048966162661934401191 18694573449243992901601787)
          ·
            refine ⟨28041860173865989352402681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18694573449243992901601787 28041860173865989352402681)
            ·
              refine ⟨21031395130399492014302011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28041860173865989352402681 21031395130399492014302011)
              ·
                refine ⟨31547092695599238021453017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21031395130399492014302011 31547092695599238021453017)
                ·
                  refine ⟨23660319521699428516089763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31547092695599238021453017 23660319521699428516089763)
                  ·
                    refine ⟨35490479282549142774134645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23660319521699428516089763 35490479282549142774134645)
                    ·
                      refine ⟨3327232432738982135075123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35490479282549142774134645 3327232432738982135075123)
                      ·
                        rfl

theorem cell23_6479762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_6479762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479762 prefixEnd_6479762 := by exact prefixLift 6479762
  have htrace : WordTrace (prefixWord ++ tailWord_6479762) baseStart_6479762 baseEnd_6479762 := by
    simpa [prefixWord, tailWord_6479762, baseEnd_6479762] using wordTrace_append hprefix tailTrace_6479762
  have hstable : (prefixWord ++ tailWord_6479762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479762).length < 2 ^ (prefixWord ++ tailWord_6479762).sum := by decide
  have hdescent : baseEnd_6479762 < baseStart_6479762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479832 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 4, 4, 2]
def baseStart_6479832 : Nat := 118140960795 + 6479832 * 2 ^ 59
def prefixEnd_6479832 : Nat := 4983230072969 + 3 ^ 40 * 6479832 * 2
def baseEnd_6479832 : Nat := 3327268376384796861199801

theorem tailTrace_6479832 : CollatzResearch.WordTrace tailWord_6479832 prefixEnd_6479832 3327268376384796861199801 := by
  unfold tailWord_6479832
  simp only [CollatzResearch.WordTrace]
  refine ⟨118169444530341403022216875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157559259373788537362955833 118169444530341403022216875)
  ·
    refine ⟨177254166795512104533325313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118169444530341403022216875 177254166795512104533325313)
    ·
      refine ⟨132940625096634078399993985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177254166795512104533325313 132940625096634078399993985)
      ·
        refine ⟨99705468822475558799995489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132940625096634078399993985 99705468822475558799995489)
        ·
          refine ⟨74779101616856669099996617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99705468822475558799995489 74779101616856669099996617)
          ·
            refine ⟨56084326212642501824997463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74779101616856669099996617 56084326212642501824997463)
            ·
              refine ⟨84126489318963752737496195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56084326212642501824997463 84126489318963752737496195)
              ·
                refine ⟨126189733978445629106244293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84126489318963752737496195 126189733978445629106244293)
                ·
                  refine ⟨23660575120958555457420805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126189733978445629106244293 23660575120958555457420805)
                  ·
                    refine ⟨4436357835179729148266401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23660575120958555457420805 4436357835179729148266401)
                    ·
                      refine ⟨3327268376384796861199801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4436357835179729148266401 3327268376384796861199801)
                      ·
                        rfl

theorem cell23_6479832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_6479832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479832 prefixEnd_6479832 := by exact prefixLift 6479832
  have htrace : WordTrace (prefixWord ++ tailWord_6479832) baseStart_6479832 baseEnd_6479832 := by
    simpa [prefixWord, tailWord_6479832, baseEnd_6479832] using wordTrace_append hprefix tailTrace_6479832
  have hstable : (prefixWord ++ tailWord_6479832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479832).length < 2 ^ (prefixWord ++ tailWord_6479832).sum := by decide
  have hdescent : baseEnd_6479832 < baseStart_6479832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479893 : List Nat := [1, 3, 2, 1, 5, 1, 3, 2, 1, 4]
def baseStart_6479893 : Nat := 118140960795 + 6479893 * 2 ^ 59
def prefixEnd_6479893 : Nat := 4983230072969 + 3 ^ 40 * 6479893 * 2
def baseEnd_6479893 : Nat := 1109099899568240374179007

theorem tailTrace_6479893 : CollatzResearch.WordTrace tailWord_6479893 prefixEnd_6479893 1109099899568240374179007 := by
  unfold tailWord_6479893
  simp only [CollatzResearch.WordTrace]
  refine ⟨236341113913461813462404333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157560742608974542308269555 236341113913461813462404333)
  ·
    refine ⟨88627917717548180048401625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236341113913461813462404333 88627917717548180048401625)
    ·
      refine ⟨66470938288161135036301219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88627917717548180048401625 66470938288161135036301219)
      ·
        refine ⟨99706407432241702554451829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66470938288161135036301219 99706407432241702554451829)
        ·
          refine ⟨9347475696772659614479859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99706407432241702554451829 9347475696772659614479859)
          ·
            refine ⟨14021213545158989421719789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9347475696772659614479859 14021213545158989421719789)
            ·
              refine ⟨5257955079434621033144921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14021213545158989421719789 5257955079434621033144921)
              ·
                refine ⟨3943466309575965774858691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5257955079434621033144921 3943466309575965774858691)
                ·
                  refine ⟨5915199464363948662288037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943466309575965774858691 5915199464363948662288037)
                  ·
                    refine ⟨1109099899568240374179007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5915199464363948662288037 1109099899568240374179007)
                    ·
                      rfl

theorem cell23_6479893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_6479893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479893 prefixEnd_6479893 := by exact prefixLift 6479893
  have htrace : WordTrace (prefixWord ++ tailWord_6479893) baseStart_6479893 baseEnd_6479893 := by
    simpa [prefixWord, tailWord_6479893, baseEnd_6479893] using wordTrace_append hprefix tailTrace_6479893
  have hstable : (prefixWord ++ tailWord_6479893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479893).length < 2 ^ (prefixWord ++ tailWord_6479893).sum := by decide
  have hdescent : baseEnd_6479893 < baseStart_6479893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479932 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 1, 6]
def baseStart_6479932 : Nat := 118140960795 + 6479932 * 2 ^ 59
def prefixEnd_6479932 : Nat := 4983230072969 + 3 ^ 40 * 6479932 * 2
def baseEnd_6479932 : Nat := 1109106574816748823316447

theorem tailTrace_6479932 : CollatzResearch.WordTrace tailWord_6479932 prefixEnd_6479932 1109106574816748823316447 := by
  unfold tailWord_6479932
  simp only [CollatzResearch.WordTrace]
  refine ⟨118171268180160261561537025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157561690906880348748716033 118171268180160261561537025)
  ·
    refine ⟨88628451135120196171152769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118171268180160261561537025 88628451135120196171152769)
    ·
      refine ⟨66471338351340147128364577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88628451135120196171152769 66471338351340147128364577)
      ·
        refine ⟨49853503763505110346273433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66471338351340147128364577 49853503763505110346273433)
        ·
          refine ⟨37390127822628832759705075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49853503763505110346273433 37390127822628832759705075)
          ·
            refine ⟨56085191733943249139557613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37390127822628832759705075 56085191733943249139557613)
            ·
              refine ⟨21031946900228718427334105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56085191733943249139557613 21031946900228718427334105)
              ·
                refine ⟨15773960175171538820500579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21031946900228718427334105 15773960175171538820500579)
                ·
                  refine ⟨23660940262757308230750869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15773960175171538820500579 23660940262757308230750869)
                  ·
                    refine ⟨1109106574816748823316447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23660940262757308230750869 1109106574816748823316447)
                    ·
                      rfl

theorem cell23_6479932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_6479932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479932 prefixEnd_6479932 := by exact prefixLift 6479932
  have htrace : WordTrace (prefixWord ++ tailWord_6479932) baseStart_6479932 baseEnd_6479932 := by
    simpa [prefixWord, tailWord_6479932, baseEnd_6479932] using wordTrace_append hprefix tailTrace_6479932
  have hstable : (prefixWord ++ tailWord_6479932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479932).length < 2 ^ (prefixWord ++ tailWord_6479932).sum := by decide
  have hdescent : baseEnd_6479932 < baseStart_6479932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479939 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 7, 2, 2]
def baseStart_6479939 : Nat := 118140960795 + 6479939 * 2 ^ 59
def prefixEnd_6479939 : Nat := 4983230072969 + 3 ^ 40 * 6479939 * 2
def baseEnd_6479939 : Nat := 3327323318814827942561809

theorem tailTrace_6479939 : CollatzResearch.WordTrace tailWord_6479939 prefixEnd_6479939 3327323318814827942561809 := by
  unfold tailWord_6479939
  simp only [CollatzResearch.WordTrace]
  refine ⟨236342791671295163318578871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157561861114196775545719247 236342791671295163318578871)
  ·
    refine ⟨354514187506942744977868307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236342791671295163318578871 354514187506942744977868307)
    ·
      refine ⟨531771281260414117466802461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354514187506942744977868307 531771281260414117466802461)
      ·
        refine ⟨199414230472655294050050923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 531771281260414117466802461 199414230472655294050050923)
        ·
          refine ⟨299121345708982941075076385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199414230472655294050050923 299121345708982941075076385)
          ·
            refine ⟨224341009281737205806307289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299121345708982941075076385 224341009281737205806307289)
            ·
              refine ⟨168255756961302904354730467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224341009281737205806307289 168255756961302904354730467)
              ·
                refine ⟨252383635441954356532095701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168255756961302904354730467 252383635441954356532095701)
                ·
                  refine ⟨5915241455670805231220993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 252383635441954356532095701 5915241455670805231220993)
                  ·
                    refine ⟨4436431091753103923415745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5915241455670805231220993 4436431091753103923415745)
                    ·
                      refine ⟨3327323318814827942561809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4436431091753103923415745 3327323318814827942561809)
                      ·
                        rfl

theorem cell23_6479939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 2, 2].length) (baseStart_6479939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479939 prefixEnd_6479939 := by exact prefixLift 6479939
  have htrace : WordTrace (prefixWord ++ tailWord_6479939) baseStart_6479939 baseEnd_6479939 := by
    simpa [prefixWord, tailWord_6479939, baseEnd_6479939] using wordTrace_append hprefix tailTrace_6479939
  have hstable : (prefixWord ++ tailWord_6479939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479939).length < 2 ^ (prefixWord ++ tailWord_6479939).sum := by decide
  have hdescent : baseEnd_6479939 < baseStart_6479939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479950 : List Nat := [4, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3]
def baseStart_6479950 : Nat := 118140960795 + 6479950 * 2 ^ 59
def prefixEnd_6479950 : Nat := 4983230072969 + 3 ^ 40 * 6479950 * 2
def baseEnd_6479950 : Nat := 3327328967102027399524259

theorem tailTrace_6479950 : CollatzResearch.WordTrace tailWord_6479950 prefixEnd_6479950 3327328967102027399524259 := by
  unfold tailWord_6479950
  simp only [CollatzResearch.WordTrace]
  refine ⟨29542899109281914024653663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157562128582836874798152869 29542899109281914024653663)
  ·
    refine ⟨44314348663922871036980495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29542899109281914024653663 44314348663922871036980495)
    ·
      refine ⟨66471522995884306555470743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44314348663922871036980495 66471522995884306555470743)
      ·
        refine ⟨99707284493826459833206115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66471522995884306555470743 99707284493826459833206115)
        ·
          refine ⟨149560926740739689749809173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99707284493826459833206115 149560926740739689749809173)
          ·
            refine ⟨7010668440972172957022305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149560926740739689749809173 7010668440972172957022305)
            ·
              refine ⟨5258001330729129717766729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7010668440972172957022305 5258001330729129717766729)
              ·
                refine ⟨3943500998046847288325047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5258001330729129717766729 3943500998046847288325047)
                ·
                  refine ⟨5915251497070270932487571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943500998046847288325047 5915251497070270932487571)
                  ·
                    refine ⟨8872877245605406398731357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5915251497070270932487571 8872877245605406398731357)
                    ·
                      refine ⟨3327328967102027399524259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8872877245605406398731357 3327328967102027399524259)
                      ·
                        rfl

theorem cell23_6479950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_6479950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479950 prefixEnd_6479950 := by exact prefixLift 6479950
  have htrace : WordTrace (prefixWord ++ tailWord_6479950) baseStart_6479950 baseEnd_6479950 := by
    simpa [prefixWord, tailWord_6479950, baseEnd_6479950] using wordTrace_append hprefix tailTrace_6479950
  have hstable : (prefixWord ++ tailWord_6479950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479950).length < 2 ^ (prefixWord ++ tailWord_6479950).sum := by decide
  have hdescent : baseEnd_6479950 < baseStart_6479950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479956 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_6479956 : Nat := 118140960795 + 6479956 * 2 ^ 59
def prefixEnd_6479956 : Nat := 4983230072969 + 3 ^ 40 * 6479956 * 2
def baseEnd_6479956 : Nat := 3327332047985954376049231

theorem tailTrace_6479956 : CollatzResearch.WordTrace tailWord_6479956 prefixEnd_6479956 3327332047985954376049231 := by
  unfold tailWord_6479956
  simp only [CollatzResearch.WordTrace]
  refine ⟨118171705856116787610973861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157562274474822383481298481 118171705856116787610973861)
  ·
    refine ⟨22157194848021897677057599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118171705856116787610973861 22157194848021897677057599)
    ·
      refine ⟨33235792272032846515586399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22157194848021897677057599 33235792272032846515586399)
      ·
        refine ⟨49853688408049269773379599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33235792272032846515586399 49853688408049269773379599)
        ·
          refine ⟨74780532612073904660069399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49853688408049269773379599 74780532612073904660069399)
          ·
            refine ⟨112170798918110856990104099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74780532612073904660069399 112170798918110856990104099)
            ·
              refine ⟨168256198377166285485156149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112170798918110856990104099 168256198377166285485156149)
              ·
                refine ⟨15774018597859339264233389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168256198377166285485156149 15774018597859339264233389)
                ·
                  refine ⟨5915256974197252224087521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15774018597859339264233389 5915256974197252224087521)
                  ·
                    refine ⟨4436442730647939168065641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5915256974197252224087521 4436442730647939168065641)
                    ·
                      refine ⟨3327332047985954376049231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4436442730647939168065641 3327332047985954376049231)
                      ·
                        rfl

theorem cell23_6479956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_6479956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479956 prefixEnd_6479956 := by exact prefixLift 6479956
  have htrace : WordTrace (prefixWord ++ tailWord_6479956) baseStart_6479956 baseEnd_6479956 := by
    simpa [prefixWord, tailWord_6479956, baseEnd_6479956] using wordTrace_append hprefix tailTrace_6479956
  have hstable : (prefixWord ++ tailWord_6479956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479956).length < 2 ^ (prefixWord ++ tailWord_6479956).sum := by decide
  have hdescent : baseEnd_6479956 < baseStart_6479956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479990 : List Nat := [5, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_6479990 : Nat := 118140960795 + 6479990 * 2 ^ 59
def prefixEnd_6479990 : Nat := 4983230072969 + 3 ^ 40 * 6479990 * 2
def baseEnd_6479990 : Nat := 3327349506328207243024075

theorem tailTrace_6479990 : CollatzResearch.WordTrace tailWord_6479990 prefixEnd_6479990 3327349506328207243024075 := by
  unfold tailWord_6479990
  simp only [CollatzResearch.WordTrace]
  refine ⟨14771540737131899939292839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157563101196073599352456949 14771540737131899939292839)
  ·
    refine ⟨22157311105697849908939259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14771540737131899939292839 22157311105697849908939259)
    ·
      refine ⟨33235966658546774863408889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22157311105697849908939259 33235966658546774863408889)
      ·
        refine ⟨24926974993910081147556667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33235966658546774863408889 24926974993910081147556667)
        ·
          refine ⟨37390462490865121721335001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24926974993910081147556667 37390462490865121721335001)
          ·
            refine ⟨28042846868148841291001251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37390462490865121721335001 28042846868148841291001251)
            ·
              refine ⟨42064270302223261936501877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28042846868148841291001251 42064270302223261936501877)
              ·
                refine ⟨3943525340833430806547051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42064270302223261936501877 3943525340833430806547051)
                ·
                  refine ⟨5915288011250146209820577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943525340833430806547051 5915288011250146209820577)
                  ·
                    refine ⟨4436466008437609657365433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5915288011250146209820577 4436466008437609657365433)
                    ·
                      refine ⟨3327349506328207243024075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4436466008437609657365433 3327349506328207243024075)
                      ·
                        rfl

theorem cell23_6479990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_6479990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479990 prefixEnd_6479990 := by exact prefixLift 6479990
  have htrace : WordTrace (prefixWord ++ tailWord_6479990) baseStart_6479990 baseEnd_6479990 := by
    simpa [prefixWord, tailWord_6479990, baseEnd_6479990] using wordTrace_append hprefix tailTrace_6479990
  have hstable : (prefixWord ++ tailWord_6479990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479990).length < 2 ^ (prefixWord ++ tailWord_6479990).sum := by decide
  have hdescent : baseEnd_6479990 < baseStart_6479990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6479993 : List Nat := [1, 2, 1, 3, 4, 3, 2, 1, 1, 2, 3]
def baseStart_6479993 : Nat := 118140960795 + 6479993 * 2 ^ 59
def prefixEnd_6479993 : Nat := 4983230072969 + 3 ^ 40 * 6479993 * 2
def baseEnd_6479993 : Nat := 3327351046770170731286561

theorem tailTrace_6479993 : CollatzResearch.WordTrace tailWord_6479993 prefixEnd_6479993 3327351046770170731286561 := by
  unfold tailWord_6479993
  simp only [CollatzResearch.WordTrace]
  refine ⟨236344761213099530541044633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157563174142066353694029755 236344761213099530541044633)
  ·
    refine ⟨177258570909824647905783475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236344761213099530541044633 177258570909824647905783475)
    ·
      refine ⟨265887856364736971858675213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177258570909824647905783475 265887856364736971858675213)
      ·
        refine ⟨99707946136776364447003205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265887856364736971858675213 99707946136776364447003205)
        ·
          refine ⟨18695239900645568333813101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99707946136776364447003205 18695239900645568333813101)
          ·
            refine ⟨7010714962742088125179913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18695239900645568333813101 7010714962742088125179913)
            ·
              refine ⟨5258036222056566093884935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7010714962742088125179913 5258036222056566093884935)
              ·
                refine ⟨7887054333084849140827403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258036222056566093884935 7887054333084849140827403)
                ·
                  refine ⟨11830581499627273711241105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7887054333084849140827403 11830581499627273711241105)
                  ·
                    refine ⟨8872936124720455283430829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11830581499627273711241105 8872936124720455283430829)
                    ·
                      refine ⟨3327351046770170731286561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8872936124720455283430829 3327351046770170731286561)
                      ·
                        rfl

theorem cell23_6479993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_6479993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6479993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6479993 prefixEnd_6479993 := by exact prefixLift 6479993
  have htrace : WordTrace (prefixWord ++ tailWord_6479993) baseStart_6479993 baseEnd_6479993 := by
    simpa [prefixWord, tailWord_6479993, baseEnd_6479993] using wordTrace_append hprefix tailTrace_6479993
  have hstable : (prefixWord ++ tailWord_6479993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6479993).length < 2 ^ (prefixWord ++ tailWord_6479993).sum := by decide
  have hdescent : baseEnd_6479993 < baseStart_6479993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6479993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480020 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_6480020 : Nat := 118140960795 + 6480020 * 2 ^ 59
def prefixEnd_6480020 : Nat := 4983230072969 + 3 ^ 40 * 6480020 * 2
def baseEnd_6480020 : Nat := 3327364910747842125648937

theorem tailTrace_6480020 : CollatzResearch.WordTrace tailWord_6480020 prefixEnd_6480020 3327364910747842125648937 := by
  unfold tailWord_6480020
  simp only [CollatzResearch.WordTrace]
  refine ⟨118172872992000857076138757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157563830656001142768185009 118172872992000857076138757)
  ·
    refine ⟨22157413686000160701776017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118172872992000857076138757 22157413686000160701776017)
    ·
      refine ⟨16618060264500120526332013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22157413686000160701776017 16618060264500120526332013)
      ·
        refine ⟨6231772599187545197374505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16618060264500120526332013 6231772599187545197374505)
        ·
          refine ⟨4673829449390658898030879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6231772599187545197374505 4673829449390658898030879)
          ·
            refine ⟨7010744174085988347046319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4673829449390658898030879 7010744174085988347046319)
            ·
              refine ⟨10516116261128982520569479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7010744174085988347046319 10516116261128982520569479)
              ·
                refine ⟨15774174391693473780854219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10516116261128982520569479 15774174391693473780854219)
                ·
                  refine ⟨23661261587540210671281329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15774174391693473780854219 23661261587540210671281329)
                  ·
                    refine ⟨17745946190655158003460997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23661261587540210671281329 17745946190655158003460997)
                    ·
                      refine ⟨3327364910747842125648937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17745946190655158003460997 3327364910747842125648937)
                      ·
                        rfl

theorem cell23_6480020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_6480020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480020 prefixEnd_6480020 := by exact prefixLift 6480020
  have htrace : WordTrace (prefixWord ++ tailWord_6480020) baseStart_6480020 baseEnd_6480020 := by
    simpa [prefixWord, tailWord_6480020, baseEnd_6480020] using wordTrace_append hprefix tailTrace_6480020
  have hstable : (prefixWord ++ tailWord_6480020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480020).length < 2 ^ (prefixWord ++ tailWord_6480020).sum := by decide
  have hdescent : baseEnd_6480020 < baseStart_6480020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480023 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 1, 3, 3]
def baseStart_6480023 : Nat := 118140960795 + 6480023 * 2 ^ 59
def prefixEnd_6480023 : Nat := 4983230072969 + 3 ^ 40 * 6480023 * 2
def baseEnd_6480023 : Nat := 3327366451189805613911423

theorem tailTrace_6480023 : CollatzResearch.WordTrace tailWord_6480023 prefixEnd_6480023 3327366451189805613911423 := by
  unfold tailWord_6480023
  simp only [CollatzResearch.WordTrace]
  refine ⟨236345855402990845664636723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157563903601993897109757815 236345855402990845664636723)
  ·
    refine ⟨354518783104486268496955085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236345855402990845664636723 354518783104486268496955085)
    ·
      refine ⟨132944543664182350686358157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354518783104486268496955085 132944543664182350686358157)
      ·
        refine ⟨49854203874068381507384309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132944543664182350686358157 49854203874068381507384309)
        ·
          refine ⟨4673831613193910766317279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49854203874068381507384309 4673831613193910766317279)
          ·
            refine ⟨7010747419790866149475919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4673831613193910766317279 7010747419790866149475919)
            ·
              refine ⟨10516121129686299224213879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7010747419790866149475919 10516121129686299224213879)
              ·
                refine ⟨15774181694529448836320819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10516121129686299224213879 15774181694529448836320819)
                ·
                  refine ⟨23661272541794173254481229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15774181694529448836320819 23661272541794173254481229)
                  ·
                    refine ⟨8872977203172814970430461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23661272541794173254481229 8872977203172814970430461)
                    ·
                      refine ⟨3327366451189805613911423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8872977203172814970430461 3327366451189805613911423)
                      ·
                        rfl

theorem cell23_6480023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_6480023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480023 prefixEnd_6480023 := by exact prefixLift 6480023
  have htrace : WordTrace (prefixWord ++ tailWord_6480023) baseStart_6480023 baseEnd_6480023 := by
    simpa [prefixWord, tailWord_6480023, baseEnd_6480023] using wordTrace_append hprefix tailTrace_6480023
  have hstable : (prefixWord ++ tailWord_6480023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480023).length < 2 ^ (prefixWord ++ tailWord_6480023).sum := by decide
  have hdescent : baseEnd_6480023 < baseStart_6480023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480033 : List Nat := [1, 2, 3, 3, 1, 3, 2, 2, 1, 3, 2]
def baseStart_6480033 : Nat := 118140960795 + 6480033 * 2 ^ 59
def prefixEnd_6480033 : Nat := 4983230072969 + 3 ^ 40 * 6480033 * 2
def baseEnd_6480033 : Nat := 3327371585996350574786377

theorem tailTrace_6480033 : CollatzResearch.WordTrace tailWord_6480033 prefixEnd_6480033 3327371585996350574786377 := by
  unfold tailWord_6480033
  simp only [CollatzResearch.WordTrace]
  refine ⟨236346220132954617372500753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157564146755303078248333835 236346220132954617372500753)
  ·
    refine ⟨177259665099715963029375565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236346220132954617372500753 177259665099715963029375565)
    ·
      refine ⟨66472374412393486136015837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177259665099715963029375565 66472374412393486136015837)
      ·
        refine ⟨24927140404647557301005939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66472374412393486136015837 24927140404647557301005939)
        ·
          refine ⟨37390710606971335951508909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24927140404647557301005939 37390710606971335951508909)
          ·
            refine ⟨14021516477614250981815841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37390710606971335951508909 14021516477614250981815841)
            ·
              refine ⟨10516137358210688236361881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14021516477614250981815841 10516137358210688236361881)
              ·
                refine ⟨7887103018658016177271411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10516137358210688236361881 7887103018658016177271411)
                ·
                  refine ⟨11830654527987024265907117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7887103018658016177271411 11830654527987024265907117)
                  ·
                    refine ⟨4436495447995134099715169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11830654527987024265907117 4436495447995134099715169)
                    ·
                      refine ⟨3327371585996350574786377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4436495447995134099715169 3327371585996350574786377)
                      ·
                        rfl

theorem cell23_6480033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_6480033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480033 prefixEnd_6480033 := by exact prefixLift 6480033
  have htrace : WordTrace (prefixWord ++ tailWord_6480033) baseStart_6480033 baseEnd_6480033 := by
    simpa [prefixWord, tailWord_6480033, baseEnd_6480033] using wordTrace_append hprefix tailTrace_6480033
  have hstable : (prefixWord ++ tailWord_6480033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480033).length < 2 ^ (prefixWord ++ tailWord_6480033).sum := by decide
  have hdescent : baseEnd_6480033 < baseStart_6480033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480069 : List Nat := [1, 3, 1, 1, 1, 1, 4, 6, 5]
def baseStart_6480069 : Nat := 118140960795 + 6480069 * 2 ^ 59
def prefixEnd_6480069 : Nat := 4983230072969 + 3 ^ 40 * 6480069 * 2
def baseEnd_6480069 : Nat := 369710007922212492659579

theorem tailTrace_6480069 : CollatzResearch.WordTrace tailWord_6480069 prefixEnd_6480069 369710007922212492659579 := by
  unfold tailWord_6480069
  simp only [CollatzResearch.WordTrace]
  refine ⟨236347533160824195520811261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157565022107216130347207507 236347533160824195520811261)
  ·
    refine ⟨88630324935309073320304223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236347533160824195520811261 88630324935309073320304223)
    ·
      refine ⟨132945487402963609980456335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88630324935309073320304223 132945487402963609980456335)
      ·
        refine ⟨199418231104445414970684503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132945487402963609980456335 199418231104445414970684503)
        ·
          refine ⟨299127346656668122456026755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199418231104445414970684503 299127346656668122456026755)
          ·
            refine ⟨448691019985002183684040133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299127346656668122456026755 448691019985002183684040133)
            ·
              refine ⟨84129566247187909440757525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 448691019985002183684040133 84129566247187909440757525)
              ·
                refine ⟨3943573417836933255035509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84129566247187909440757525 3943573417836933255035509)
                ·
                  refine ⟨369710007922212492659579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3943573417836933255035509 369710007922212492659579)
                  ·
                    rfl

theorem cell23_6480069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 5].length) (baseStart_6480069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480069 prefixEnd_6480069 := by exact prefixLift 6480069
  have htrace : WordTrace (prefixWord ++ tailWord_6480069) baseStart_6480069 baseEnd_6480069 := by
    simpa [prefixWord, tailWord_6480069, baseEnd_6480069] using wordTrace_append hprefix tailTrace_6480069
  have hstable : (prefixWord ++ tailWord_6480069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480069).length < 2 ^ (prefixWord ++ tailWord_6480069).sum := by decide
  have hdescent : baseEnd_6480069 < baseStart_6480069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480136 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 1, 6, 2]
def baseStart_6480136 : Nat := 118140960795 + 6480136 * 2 ^ 59
def prefixEnd_6480136 : Nat := 4983230072969 + 3 ^ 40 * 6480136 * 2
def baseEnd_6480136 : Nat := 3327424474503763671798403

theorem tailTrace_6480136 : CollatzResearch.WordTrace tailWord_6480136 prefixEnd_6480136 3327424474503763671798403 := by
  unfold tailWord_6480136
  simp only [CollatzResearch.WordTrace]
  refine ⟨118174988425790732981750131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157566651234387643975666841 118174988425790732981750131)
  ·
    refine ⟨177262482638686099472625197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118174988425790732981750131 177262482638686099472625197)
    ·
      refine ⟨66473430989507287302234449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177262482638686099472625197 66473430989507287302234449)
      ·
        refine ⟨49855073242130465476675837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66473430989507287302234449 49855073242130465476675837)
        ·
          refine ⟨18695652465798924553753439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49855073242130465476675837 18695652465798924553753439)
          ·
            refine ⟨28043478698698386830630159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18695652465798924553753439 28043478698698386830630159)
            ·
              refine ⟨42065218048047580245945239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28043478698698386830630159 42065218048047580245945239)
              ·
                refine ⟨63097827072071370368917859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42065218048047580245945239 63097827072071370368917859)
                ·
                  refine ⟨94646740608107055553376789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63097827072071370368917859 94646740608107055553376789)
                  ·
                    refine ⟨4436565966005018229064537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94646740608107055553376789 4436565966005018229064537)
                    ·
                      refine ⟨3327424474503763671798403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4436565966005018229064537 3327424474503763671798403)
                      ·
                        rfl

theorem cell23_6480136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_6480136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480136 prefixEnd_6480136 := by exact prefixLift 6480136
  have htrace : WordTrace (prefixWord ++ tailWord_6480136) baseStart_6480136 baseEnd_6480136 := by
    simpa [prefixWord, tailWord_6480136, baseEnd_6480136] using wordTrace_append hprefix tailTrace_6480136
  have hstable : (prefixWord ++ tailWord_6480136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480136).length < 2 ^ (prefixWord ++ tailWord_6480136).sum := by decide
  have hdescent : baseEnd_6480136 < baseStart_6480136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480139 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 3]
def baseStart_6480139 : Nat := 118140960795 + 6480139 * 2 ^ 59
def prefixEnd_6480139 : Nat := 4983230072969 + 3 ^ 40 * 6480139 * 2
def baseEnd_6480139 : Nat := 3327426014945727160060889

theorem tailTrace_6480139 : CollatzResearch.WordTrace tailWord_6480139 prefixEnd_6480139 3327426014945727160060889 := by
  unfold tailWord_6480139
  simp only [CollatzResearch.WordTrace]
  refine ⟨236350086270570597475859471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157566724180380398317239647 236350086270570597475859471)
  ·
    refine ⟨354525129405855896213789207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236350086270570597475859471 354525129405855896213789207)
    ·
      refine ⟨531787694108783844320683811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354525129405855896213789207 531787694108783844320683811)
      ·
        refine ⟨797681541163175766481025717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531787694108783844320683811 797681541163175766481025717)
        ·
          refine ⟨74782644484047728107596161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 797681541163175766481025717 74782644484047728107596161)
          ·
            refine ⟨56086983363035796080697121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74782644484047728107596161 56086983363035796080697121)
            ·
              refine ⟨42065237522276847060522841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56086983363035796080697121 42065237522276847060522841)
              ·
                refine ⟨31548928141707635295392131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42065237522276847060522841 31548928141707635295392131)
                ·
                  refine ⟨47323392212561452943088197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31548928141707635295392131 47323392212561452943088197)
                  ·
                    refine ⟨8873136039855272426829037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47323392212561452943088197 8873136039855272426829037)
                    ·
                      refine ⟨3327426014945727160060889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8873136039855272426829037 3327426014945727160060889)
                      ·
                        rfl

theorem cell23_6480139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 3].length) (baseStart_6480139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480139 prefixEnd_6480139 := by exact prefixLift 6480139
  have htrace : WordTrace (prefixWord ++ tailWord_6480139) baseStart_6480139 baseEnd_6480139 := by
    simpa [prefixWord, tailWord_6480139, baseEnd_6480139] using wordTrace_append hprefix tailTrace_6480139
  have hstable : (prefixWord ++ tailWord_6480139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480139).length < 2 ^ (prefixWord ++ tailWord_6480139).sum := by decide
  have hdescent : baseEnd_6480139 < baseStart_6480139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480163 : List Nat := [1, 1, 1, 4, 2, 2, 4, 3, 1, 4]
def baseStart_6480163 : Nat := 118140960795 + 6480163 * 2 ^ 59
def prefixEnd_6480163 : Nat := 4983230072969 + 3 ^ 40 * 6480163 * 2
def baseEnd_6480163 : Nat := 1109146112827145022053593

theorem tailTrace_6480163 : CollatzResearch.WordTrace tailWord_6480163 prefixEnd_6480163 1109146112827145022053593 := by
  unfold tailWord_6480163
  simp only [CollatzResearch.WordTrace]
  refine ⟨236350961622483649574733143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157567307748322433049822095 236350961622483649574733143)
  ·
    refine ⟨354526442433725474362099715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236350961622483649574733143 354526442433725474362099715)
    ·
      refine ⟨531789663650588211543149573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354526442433725474362099715 531789663650588211543149573)
      ·
        refine ⟨99710561934485289664340545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 531789663650588211543149573 99710561934485289664340545)
        ·
          refine ⟨74782921450863967248255409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99710561934485289664340545 74782921450863967248255409)
          ·
            refine ⟨56087191088147975436191557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74782921450863967248255409 56087191088147975436191557)
            ·
              refine ⟨10516348329027745394285917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56087191088147975436191557 10516348329027745394285917)
              ·
                refine ⟨3943630623385404522857219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10516348329027745394285917 3943630623385404522857219)
                ·
                  refine ⟨5915445935078106784285829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943630623385404522857219 5915445935078106784285829)
                  ·
                    refine ⟨1109146112827145022053593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5915445935078106784285829 1109146112827145022053593)
                    ·
                      rfl

theorem cell23_6480163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 1, 4].length) (baseStart_6480163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480163 prefixEnd_6480163 := by exact prefixLift 6480163
  have htrace : WordTrace (prefixWord ++ tailWord_6480163) baseStart_6480163 baseEnd_6480163 := by
    simpa [prefixWord, tailWord_6480163, baseEnd_6480163] using wordTrace_append hprefix tailTrace_6480163
  have hstable : (prefixWord ++ tailWord_6480163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480163).length < 2 ^ (prefixWord ++ tailWord_6480163).sum := by decide
  have hdescent : baseEnd_6480163 < baseStart_6480163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480180 : List Nat := [2, 5, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_6480180 : Nat := 118140960795 + 6480180 * 2 ^ 59
def prefixEnd_6480180 : Nat := 4983230072969 + 3 ^ 40 * 6480180 * 2
def baseEnd_6480180 : Nat := 1109149022550853833216067

theorem tailTrace_6480180 : CollatzResearch.WordTrace tailWord_6480180 prefixEnd_6480180 1109149022550853833216067 := by
  unfold tailWord_6480180
  simp only [CollatzResearch.WordTrace]
  refine ⟨118175790831711030739050997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157567721108948040985401329 118175790831711030739050997)
  ·
    refine ⟨11078980390472909131786031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118175790831711030739050997 11078980390472909131786031)
    ·
      refine ⟨16618470585709363697679047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11078980390472909131786031 16618470585709363697679047)
      ·
        refine ⟨24927705878564045546518571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16618470585709363697679047 24927705878564045546518571)
        ·
          refine ⟨37391558817846068319777857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24927705878564045546518571 37391558817846068319777857)
          ·
            refine ⟨28043669113384551239833393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37391558817846068319777857 28043669113384551239833393)
            ·
              refine ⟨21032751835038413429875045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28043669113384551239833393 21032751835038413429875045)
              ·
                refine ⟨3943640969069702518101571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21032751835038413429875045 3943640969069702518101571)
                ·
                  refine ⟨5915461453604553777152357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943640969069702518101571 5915461453604553777152357)
                  ·
                    refine ⟨1109149022550853833216067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5915461453604553777152357 1109149022550853833216067)
                    ·
                      rfl

theorem cell23_6480180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_6480180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480180 prefixEnd_6480180 := by exact prefixLift 6480180
  have htrace : WordTrace (prefixWord ++ tailWord_6480180) baseStart_6480180 baseEnd_6480180 := by
    simpa [prefixWord, tailWord_6480180, baseEnd_6480180] using wordTrace_append hprefix tailTrace_6480180
  have hstable : (prefixWord ++ tailWord_6480180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480180).length < 2 ^ (prefixWord ++ tailWord_6480180).sum := by decide
  have hdescent : baseEnd_6480180 < baseStart_6480180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480237 : List Nat := [1, 5, 1, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_6480237 : Nat := 118140960795 + 6480237 * 2 ^ 59
def prefixEnd_6480237 : Nat := 4983230072969 + 3 ^ 40 * 6480237 * 2
def baseEnd_6480237 : Nat := 3327476336049867776635439

theorem tailTrace_6480237 : CollatzResearch.WordTrace tailWord_6480237 prefixEnd_6480237 3327476336049867776635439 := by
  unfold tailWord_6480237
  simp only [CollatzResearch.WordTrace]
  refine ⟨236353660624215560212926965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157569107082810373475284643 236353660624215560212926965)
  ·
    refine ⟨22158155683520208769961903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236353660624215560212926965 22158155683520208769961903)
    ·
      refine ⟨33237233525280313154942855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22158155683520208769961903 33237233525280313154942855)
      ·
        refine ⟨49855850287920469732414283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33237233525280313154942855 49855850287920469732414283)
        ·
          refine ⟨74783775431880704598621425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49855850287920469732414283 74783775431880704598621425)
          ·
            refine ⟨56087831573910528448966069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74783775431880704598621425 56087831573910528448966069)
            ·
              refine ⟨5258234210054112042090569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56087831573910528448966069 5258234210054112042090569)
              ·
                refine ⟨3943675657540584031567927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5258234210054112042090569 3943675657540584031567927)
                ·
                  refine ⟨5915513486310876047351891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943675657540584031567927 5915513486310876047351891)
                  ·
                    refine ⟨8873270229466314071027837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5915513486310876047351891 8873270229466314071027837)
                    ·
                      refine ⟨3327476336049867776635439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8873270229466314071027837 3327476336049867776635439)
                      ·
                        rfl

theorem cell23_6480237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_6480237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480237 prefixEnd_6480237 := by exact prefixLift 6480237
  have htrace : WordTrace (prefixWord ++ tailWord_6480237) baseStart_6480237 baseEnd_6480237 := by
    simpa [prefixWord, tailWord_6480237, baseEnd_6480237] using wordTrace_append hprefix tailTrace_6480237
  have hstable : (prefixWord ++ tailWord_6480237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480237).length < 2 ^ (prefixWord ++ tailWord_6480237).sum := by decide
  have hdescent : baseEnd_6480237 < baseStart_6480237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480239 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 4]
def baseStart_6480239 : Nat := 118140960795 + 6480239 * 2 ^ 59
def prefixEnd_6480239 : Nat := 4983230072969 + 3 ^ 40 * 6480239 * 2
def baseEnd_6480239 : Nat := 3327477363011176768810429

theorem tailTrace_6480239 : CollatzResearch.WordTrace tailWord_6480239 prefixEnd_6480239 3327477363011176768810429 := by
  unfold tailWord_6480239
  simp only [CollatzResearch.WordTrace]
  refine ⟨236353733570208314554499771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157569155713472209702999847 236353733570208314554499771)
  ·
    refine ⟨354530600355312471831749657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236353733570208314554499771 354530600355312471831749657)
    ·
      refine ⟨265897950266484353873812243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354530600355312471831749657 265897950266484353873812243)
      ·
        refine ⟨398846925399726530810718365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265897950266484353873812243 398846925399726530810718365)
        ·
          refine ⟨149567597024897449054019387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398846925399726530810718365 149567597024897449054019387)
          ·
            refine ⟨224351395537346173581029081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149567597024897449054019387 224351395537346173581029081)
            ·
              refine ⟨168263546653009630185771811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224351395537346173581029081 168263546653009630185771811)
              ·
                refine ⟨252395319979514445278657717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168263546653009630185771811 252395319979514445278657717)
                ·
                  refine ⟨23662061248079479244874161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252395319979514445278657717 23662061248079479244874161)
                  ·
                    refine ⟨17746545936059609433655621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23662061248079479244874161 17746545936059609433655621)
                    ·
                      refine ⟨3327477363011176768810429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17746545936059609433655621 3327477363011176768810429)
                      ·
                        rfl

theorem cell23_6480239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_6480239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480239 prefixEnd_6480239 := by exact prefixLift 6480239
  have htrace : WordTrace (prefixWord ++ tailWord_6480239) baseStart_6480239 baseEnd_6480239 := by
    simpa [prefixWord, tailWord_6480239, baseEnd_6480239] using wordTrace_append hprefix tailTrace_6480239
  have hstable : (prefixWord ++ tailWord_6480239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480239).length < 2 ^ (prefixWord ++ tailWord_6480239).sum := by decide
  have hdescent : baseEnd_6480239 < baseStart_6480239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480253 : List Nat := [1, 4, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_6480253 : Nat := 118140960795 + 6480253 * 2 ^ 59
def prefixEnd_6480253 : Nat := 4983230072969 + 3 ^ 40 * 6480253 * 2
def baseEnd_6480253 : Nat := 1109161517246779904678455

theorem tailTrace_6480253 : CollatzResearch.WordTrace tailWord_6480253 prefixEnd_6480253 1109161517246779904678455 := by
  unfold tailWord_6480253
  simp only [CollatzResearch.WordTrace]
  refine ⟨236354244192157594945509413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157569496128105063297006275 236354244192157594945509413)
  ·
    refine ⟨44316420786029549052283015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236354244192157594945509413 44316420786029549052283015)
    ·
      refine ⟨66474631179044323578424523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44316420786029549052283015 66474631179044323578424523)
      ·
        refine ⟨99711946768566485367636785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66474631179044323578424523 99711946768566485367636785)
        ·
          refine ⟨74783960076424864025727589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99711946768566485367636785 74783960076424864025727589)
          ·
            refine ⟨14021992514329662004823923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74783960076424864025727589 14021992514329662004823923)
            ·
              refine ⟨21032988771494493007235885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14021992514329662004823923 21032988771494493007235885)
              ·
                refine ⟨7887370789310434877713457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21032988771494493007235885 7887370789310434877713457)
                ·
                  refine ⟨5915528091982826158285093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7887370789310434877713457 5915528091982826158285093)
                  ·
                    refine ⟨1109161517246779904678455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5915528091982826158285093 1109161517246779904678455)
                    ·
                      rfl

theorem cell23_6480253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_6480253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480253 prefixEnd_6480253 := by exact prefixLift 6480253
  have htrace : WordTrace (prefixWord ++ tailWord_6480253) baseStart_6480253 baseEnd_6480253 := by
    simpa [prefixWord, tailWord_6480253, baseEnd_6480253] using wordTrace_append hprefix tailTrace_6480253
  have hstable : (prefixWord ++ tailWord_6480253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480253).length < 2 ^ (prefixWord ++ tailWord_6480253).sum := by decide
  have hdescent : baseEnd_6480253 < baseStart_6480253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480346 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_6480346 : Nat := 118140960795 + 6480346 * 2 ^ 59
def prefixEnd_6480346 : Nat := 4983230072969 + 3 ^ 40 * 6480346 * 2
def baseEnd_6480346 : Nat := 3327532305441207850172437

theorem tailTrace_6480346 : CollatzResearch.WordTrace tailWord_6480346 prefixEnd_6480346 3327532305441207850172437 := by
  unfold tailWord_6480346
  simp only [CollatzResearch.WordTrace]
  refine ⟨59089409045205167957161223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157571757453880447885763261 59089409045205167957161223)
  ·
    refine ⟨88634113567807751935741835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59089409045205167957161223 88634113567807751935741835)
    ·
      refine ⟨132951170351711627903612753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88634113567807751935741835 132951170351711627903612753)
      ·
        refine ⟨99713377763783720927709565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132951170351711627903612753 99713377763783720927709565)
        ·
          refine ⟨37392516661418895347891087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99713377763783720927709565 37392516661418895347891087)
          ·
            refine ⟨56088774992128343021836631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37392516661418895347891087 56088774992128343021836631)
            ·
              refine ⟨84133162488192514532754947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56088774992128343021836631 84133162488192514532754947)
              ·
                refine ⟨126199743732288771799132421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84133162488192514532754947 126199743732288771799132421)
                ·
                  refine ⟨23662451949804144712337329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126199743732288771799132421 23662451949804144712337329)
                  ·
                    refine ⟨17746838962353108534252997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23662451949804144712337329 17746838962353108534252997)
                    ·
                      refine ⟨3327532305441207850172437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17746838962353108534252997 3327532305441207850172437)
                      ·
                        rfl

theorem cell23_6480346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_6480346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480346 prefixEnd_6480346 := by exact prefixLift 6480346
  have htrace : WordTrace (prefixWord ++ tailWord_6480346) baseStart_6480346 baseEnd_6480346 := by
    simpa [prefixWord, tailWord_6480346, baseEnd_6480346] using wordTrace_append hprefix tailTrace_6480346
  have hstable : (prefixWord ++ tailWord_6480346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480346).length < 2 ^ (prefixWord ++ tailWord_6480346).sum := by decide
  have hdescent : baseEnd_6480346 < baseStart_6480346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480407 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 7]
def baseStart_6480407 : Nat := 118140960795 + 6480407 * 2 ^ 59
def prefixEnd_6480407 : Nat := 4983230072969 + 3 ^ 40 * 6480407 * 2
def baseEnd_6480407 : Nat := 369729291973459123501073

theorem tailTrace_6480407 : CollatzResearch.WordTrace tailWord_6480407 prefixEnd_6480407 369729291973459123501073 := by
  unfold tailWord_6480407
  simp only [CollatzResearch.WordTrace]
  refine ⟨236359861033599679246615475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157573240689066452831076983 236359861033599679246615475)
  ·
    refine ⟨354539791550399518869923213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236359861033599679246615475 354539791550399518869923213)
    ·
      refine ⟨132952421831399819576221205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354539791550399518869923213 132952421831399819576221205)
      ·
        refine ⟨6232144773346866542635369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132952421831399819576221205 6232144773346866542635369)
        ·
          refine ⟨4674108580010149906976527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6232144773346866542635369 4674108580010149906976527)
          ·
            refine ⟨7011162870015224860464791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4674108580010149906976527 7011162870015224860464791)
            ·
              refine ⟨10516744305022837290697187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7011162870015224860464791 10516744305022837290697187)
              ·
                refine ⟨15775116457534255936045781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10516744305022837290697187 15775116457534255936045781)
                ·
                  refine ⟨369729291973459123501073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15775116457534255936045781 369729291973459123501073)
                  ·
                    rfl

theorem cell23_6480407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 7].length) (baseStart_6480407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480407 prefixEnd_6480407 := by exact prefixLift 6480407
  have htrace : WordTrace (prefixWord ++ tailWord_6480407) baseStart_6480407 baseEnd_6480407 := by
    simpa [prefixWord, tailWord_6480407, baseEnd_6480407] using wordTrace_append hprefix tailTrace_6480407
  have hstable : (prefixWord ++ tailWord_6480407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480407).length < 2 ^ (prefixWord ++ tailWord_6480407).sum := by decide
  have hdescent : baseEnd_6480407 < baseStart_6480407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480413 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_6480413 : Nat := 118140960795 + 6480413 * 2 ^ 59
def prefixEnd_6480413 : Nat := 4983230072969 + 3 ^ 40 * 6480413 * 2
def baseEnd_6480413 : Nat := 3327566708645059088034629

theorem tailTrace_6480413 : CollatzResearch.WordTrace tailWord_6480413 prefixEnd_6480413 3327566708645059088034629 := by
  unfold tailWord_6480413
  simp only [CollatzResearch.WordTrace]
  refine ⟨236360079871577942271333893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157573386581051961514222595 236360079871577942271333893)
  ·
    refine ⟨44317514975920864175875105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236360079871577942271333893 44317514975920864175875105)
    ·
      refine ⟨33238136231940648131906329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44317514975920864175875105 33238136231940648131906329)
      ·
        refine ⟨24928602173955486098929747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33238136231940648131906329 24928602173955486098929747)
        ·
          refine ⟨37392903260933229148394621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24928602173955486098929747 37392903260933229148394621)
          ·
            refine ⟨14022338722849960930647983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37392903260933229148394621 14022338722849960930647983)
            ·
              refine ⟨21033508084274941395971975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14022338722849960930647983 21033508084274941395971975)
              ·
                refine ⟨31550262126412412093957963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21033508084274941395971975 31550262126412412093957963)
                ·
                  refine ⟨47325393189618618140936945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31550262126412412093957963 47325393189618618140936945)
                  ·
                    refine ⟨35494044892213963605702709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47325393189618618140936945 35494044892213963605702709)
                    ·
                      refine ⟨3327566708645059088034629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35494044892213963605702709 3327566708645059088034629)
                      ·
                        rfl

theorem cell23_6480413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_6480413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480413 prefixEnd_6480413 := by exact prefixLift 6480413
  have htrace : WordTrace (prefixWord ++ tailWord_6480413) baseStart_6480413 baseEnd_6480413 := by
    simpa [prefixWord, tailWord_6480413, baseEnd_6480413] using wordTrace_append hprefix tailTrace_6480413
  have hstable : (prefixWord ++ tailWord_6480413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480413).length < 2 ^ (prefixWord ++ tailWord_6480413).sum := by decide
  have hdescent : baseEnd_6480413 < baseStart_6480413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480433 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 3, 4]
def baseStart_6480433 : Nat := 118140960795 + 6480433 * 2 ^ 59
def prefixEnd_6480433 : Nat := 4983230072969 + 3 ^ 40 * 6480433 * 2
def baseEnd_6480433 : Nat := 1109192326086049669928179

theorem tailTrace_6480433 : CollatzResearch.WordTrace tailWord_6480433 prefixEnd_6480433 1109192326086049669928179 := by
  unfold tailWord_6480433
  simp only [CollatzResearch.WordTrace]
  refine ⟨236360809331505485687061953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157573872887670323791374635 236360809331505485687061953)
  ·
    refine ⟨177270606998629114265296465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236360809331505485687061953 177270606998629114265296465)
    ·
      refine ⟨132952955248971835698972349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177270606998629114265296465 132952955248971835698972349)
      ·
        refine ⟨49857358218364438387114631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132952955248971835698972349 49857358218364438387114631)
        ·
          refine ⟨74786037327546657580671947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49857358218364438387114631 74786037327546657580671947)
          ·
            refine ⟨112179055991319986371007921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74786037327546657580671947 112179055991319986371007921)
            ·
              refine ⟨84134291993489989778255941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112179055991319986371007921 84134291993489989778255941)
              ·
                refine ⟨15775179748779373083422989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84134291993489989778255941 15775179748779373083422989)
                ·
                  refine ⟨5915692405792264906283621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15775179748779373083422989 5915692405792264906283621)
                  ·
                    refine ⟨1109192326086049669928179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5915692405792264906283621 1109192326086049669928179)
                    ·
                      rfl

theorem cell23_6480433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_6480433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480433 prefixEnd_6480433 := by exact prefixLift 6480433
  have htrace : WordTrace (prefixWord ++ tailWord_6480433) baseStart_6480433 baseEnd_6480433 := by
    simpa [prefixWord, tailWord_6480433, baseEnd_6480433] using wordTrace_append hprefix tailTrace_6480433
  have hstable : (prefixWord ++ tailWord_6480433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480433).length < 2 ^ (prefixWord ++ tailWord_6480433).sum := by decide
  have hdescent : baseEnd_6480433 < baseStart_6480433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480506 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 2, 10]
def baseStart_6480506 : Nat := 118140960795 + 6480506 * 2 ^ 59
def prefixEnd_6480506 : Nat := 4983230072969 + 3 ^ 40 * 6480506 * 2
def baseEnd_6480506 : Nat := 1109204820781975741390567

theorem tailTrace_6480506 : CollatzResearch.WordTrace tailWord_6480506 prefixEnd_6480506 1109204820781975741390567 := by
  unfold tailWord_6480506
  simp only [CollatzResearch.WordTrace]
  refine ⟨59090867965060254788617343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157575647906827346102979581 59090867965060254788617343)
  ·
    refine ⟨88636301947590382182926015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59090867965060254788617343 88636301947590382182926015)
    ·
      refine ⟨132954452921385573274389023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88636301947590382182926015 132954452921385573274389023)
      ·
        refine ⟨199431679382078359911583535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132954452921385573274389023 199431679382078359911583535)
        ·
          refine ⟨299147519073117539867375303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199431679382078359911583535 299147519073117539867375303)
          ·
            refine ⟨448721278609676309801062955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299147519073117539867375303 448721278609676309801062955)
            ·
              refine ⟨673081917914514464701594433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448721278609676309801062955 673081917914514464701594433)
              ·
                refine ⟨504811438435885848526195825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673081917914514464701594433 504811438435885848526195825)
                ·
                  refine ⟨378608578826914386394646869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504811438435885848526195825 378608578826914386394646869)
                  ·
                    refine ⟨1109204820781975741390567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 378608578826914386394646869 1109204820781975741390567)
                    ·
                      rfl

theorem cell23_6480506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_6480506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480506 prefixEnd_6480506 := by exact prefixLift 6480506
  have htrace : WordTrace (prefixWord ++ tailWord_6480506) baseStart_6480506 baseEnd_6480506 := by
    simpa [prefixWord, tailWord_6480506, baseEnd_6480506] using wordTrace_append hprefix tailTrace_6480506
  have hstable : (prefixWord ++ tailWord_6480506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480506).length < 2 ^ (prefixWord ++ tailWord_6480506).sum := by decide
  have hdescent : baseEnd_6480506 < baseStart_6480506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480514 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 8]
def baseStart_6480514 : Nat := 118140960795 + 6480514 * 2 ^ 59
def prefixEnd_6480514 : Nat := 4983230072969 + 3 ^ 40 * 6480514 * 2
def baseEnd_6480514 : Nat := 369735396687907021430185

theorem tailTrace_6480514 : CollatzResearch.WordTrace tailWord_6480514 prefixEnd_6480514 369735396687907021430185 := by
  unfold tailWord_6480514
  simp only [CollatzResearch.WordTrace]
  refine ⟨59090940911053009130190149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157575842429474691013840397 59090940911053009130190149)
  ·
    refine ⟨11079551420822439211910653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59090940911053009130190149 11079551420822439211910653)
    ·
      refine ⟨4154831782808414704466495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11079551420822439211910653 4154831782808414704466495)
      ·
        refine ⟨6232247674212622056699743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4154831782808414704466495 6232247674212622056699743)
        ·
          refine ⟨9348371511318933085049615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6232247674212622056699743 9348371511318933085049615)
          ·
            refine ⟨14022557266978399627574423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9348371511318933085049615 14022557266978399627574423)
            ·
              refine ⟨21033835900467599441361635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14022557266978399627574423 21033835900467599441361635)
              ·
                refine ⟨31550753850701399162042453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21033835900467599441361635 31550753850701399162042453)
                ·
                  refine ⟨369735396687907021430185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31550753850701399162042453 369735396687907021430185)
                  ·
                    rfl

theorem cell23_6480514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_6480514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480514 prefixEnd_6480514 := by exact prefixLift 6480514
  have htrace : WordTrace (prefixWord ++ tailWord_6480514) baseStart_6480514 baseEnd_6480514 := by
    simpa [prefixWord, tailWord_6480514, baseEnd_6480514] using wordTrace_append hprefix tailTrace_6480514
  have hstable : (prefixWord ++ tailWord_6480514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480514).length < 2 ^ (prefixWord ++ tailWord_6480514).sum := by decide
  have hdescent : baseEnd_6480514 < baseStart_6480514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480540 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 1, 6]
def baseStart_6480540 : Nat := 118140960795 + 6480540 * 2 ^ 59
def prefixEnd_6480540 : Nat := 4983230072969 + 3 ^ 40 * 6480540 * 2
def baseEnd_6480540 : Nat := 1109210640229393363715515

theorem tailTrace_6480540 : CollatzResearch.WordTrace tailWord_6480540 prefixEnd_6480540 1109210640229393363715515 := by
  unfold tailWord_6480540
  simp only [CollatzResearch.WordTrace]
  refine ⟨118182355971058921480603537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157576474628078561974138049 118182355971058921480603537)
  ·
    refine ⟨88636766978294191110452653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118182355971058921480603537 88636766978294191110452653)
    ·
      refine ⟨33238787616860321666419745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88636766978294191110452653 33238787616860321666419745)
      ·
        refine ⟨24929090712645241249814809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33238787616860321666419745 24929090712645241249814809)
        ·
          refine ⟨18696818034483930937361107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24929090712645241249814809 18696818034483930937361107)
          ·
            refine ⟨28045227051725896406041661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18696818034483930937361107 28045227051725896406041661)
            ·
              refine ⟨10516960144397211152265623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28045227051725896406041661 10516960144397211152265623)
              ·
                refine ⟨15775440216595816728398435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10516960144397211152265623 15775440216595816728398435)
                ·
                  refine ⟨23663160324893725092597653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15775440216595816728398435 23663160324893725092597653)
                  ·
                    refine ⟨1109210640229393363715515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23663160324893725092597653 1109210640229393363715515)
                    ·
                      rfl

theorem cell23_6480540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_6480540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480540 prefixEnd_6480540 := by exact prefixLift 6480540
  have htrace : WordTrace (prefixWord ++ tailWord_6480540) baseStart_6480540 baseEnd_6480540 := by
    simpa [prefixWord, tailWord_6480540, baseEnd_6480540] using wordTrace_append hprefix tailTrace_6480540
  have hstable : (prefixWord ++ tailWord_6480540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480540).length < 2 ^ (prefixWord ++ tailWord_6480540).sum := by decide
  have hdescent : baseEnd_6480540 < baseStart_6480540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480558 : List Nat := [4, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_6480558 : Nat := 118140960795 + 6480558 * 2 ^ 59
def prefixEnd_6480558 : Nat := 4983230072969 + 3 ^ 40 * 6480558 * 2
def baseEnd_6480558 : Nat := 3327641163339961020721463

theorem tailTrace_6480558 : CollatzResearch.WordTrace tailWord_6480558 prefixEnd_6480558 3327641163339961020721463 := by
  unfold tailWord_6480558
  simp only [CollatzResearch.WordTrace]
  refine ⟨29545671057006579004420291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157576912304035088023574885 29545671057006579004420291)
  ·
    refine ⟨44318506585509868506630437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29545671057006579004420291 44318506585509868506630437)
    ·
      refine ⟨8309719984783100344993207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44318506585509868506630437 8309719984783100344993207)
      ·
        refine ⟨12464579977174650517489811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8309719984783100344993207 12464579977174650517489811)
        ·
          refine ⟨18696869965761975776234717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12464579977174650517489811 18696869965761975776234717)
          ·
            refine ⟨7011326237160740916088019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18696869965761975776234717 7011326237160740916088019)
            ·
              refine ⟨10516989355741111374132029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7011326237160740916088019 10516989355741111374132029)
              ·
                refine ⟨3943871008402916765299511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10516989355741111374132029 3943871008402916765299511)
                ·
                  refine ⟨5915806512604375147949267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943871008402916765299511 5915806512604375147949267)
                  ·
                    refine ⟨8873709768906562721923901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5915806512604375147949267 8873709768906562721923901)
                    ·
                      refine ⟨3327641163339961020721463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8873709768906562721923901 3327641163339961020721463)
                      ·
                        rfl

theorem cell23_6480558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_6480558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480558 prefixEnd_6480558 := by exact prefixLift 6480558
  have htrace : WordTrace (prefixWord ++ tailWord_6480558) baseStart_6480558 baseEnd_6480558 := by
    simpa [prefixWord, tailWord_6480558, baseEnd_6480558] using wordTrace_append hprefix tailTrace_6480558
  have hstable : (prefixWord ++ tailWord_6480558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480558).length < 2 ^ (prefixWord ++ tailWord_6480558).sum := by decide
  have hdescent : baseEnd_6480558 < baseStart_6480558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480607 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 3, 3, 2]
def baseStart_6480607 : Nat := 118140960795 + 6480607 * 2 ^ 59
def prefixEnd_6480607 : Nat := 4983230072969 + 3 ^ 40 * 6480607 * 2
def baseEnd_6480607 : Nat := 3327666323892031329008737

theorem tailTrace_6480607 : CollatzResearch.WordTrace tailWord_6480607 prefixEnd_6480607 3327666323892031329008737 := by
  unfold tailWord_6480607
  simp only [CollatzResearch.WordTrace]
  refine ⟨236367155632875113403896075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157578103755250075602597383 236367155632875113403896075)
  ·
    refine ⟨354550733449312670105844113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236367155632875113403896075 354550733449312670105844113)
    ·
      refine ⟨265913050086984502579383085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354550733449312670105844113 265913050086984502579383085)
      ·
        refine ⟨99717393782619188467268657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265913050086984502579383085 99717393782619188467268657)
        ·
          refine ⟨74788045336964391350451493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99717393782619188467268657 74788045336964391350451493)
          ·
            refine ⟨14022758500680823378209655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74788045336964391350451493 14022758500680823378209655)
            ·
              refine ⟨21034137751021235067314483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14022758500680823378209655 21034137751021235067314483)
              ·
                refine ⟨31551206626531852600971725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21034137751021235067314483 31551206626531852600971725)
                ·
                  refine ⟨11831702484949444725364397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31551206626531852600971725 11831702484949444725364397)
                  ·
                    refine ⟨4436888431856041772011649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11831702484949444725364397 4436888431856041772011649)
                    ·
                      refine ⟨3327666323892031329008737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4436888431856041772011649 3327666323892031329008737)
                      ·
                        rfl

theorem cell23_6480607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_6480607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480607 prefixEnd_6480607 := by exact prefixLift 6480607
  have htrace : WordTrace (prefixWord ++ tailWord_6480607) baseStart_6480607 baseEnd_6480607 := by
    simpa [prefixWord, tailWord_6480607, baseEnd_6480607] using wordTrace_append hprefix tailTrace_6480607
  have hstable : (prefixWord ++ tailWord_6480607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480607).length < 2 ^ (prefixWord ++ tailWord_6480607).sum := by decide
  have hdescent : baseEnd_6480607 < baseStart_6480607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480624 : List Nat := [2, 1, 1, 1, 3, 1, 7, 1, 1, 3, 2]
def baseStart_6480624 : Nat := 118140960795 + 6480624 * 2 ^ 59
def prefixEnd_6480624 : Nat := 4983230072969 + 3 ^ 40 * 6480624 * 2
def baseEnd_6480624 : Nat := 3327675053063157762496159

theorem tailTrace_6480624 : CollatzResearch.WordTrace tailWord_6480624 prefixEnd_6480624 3327675053063157762496159 := by
  unfold tailWord_6480624
  simp only [CollatzResearch.WordTrace]
  refine ⟨118183887836906762653632463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157578517115875683538176617 118183887836906762653632463)
  ·
    refine ⟨177275831755360143980448695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118183887836906762653632463 177275831755360143980448695)
    ·
      refine ⟨265913747633040215970673043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177275831755360143980448695 265913747633040215970673043)
      ·
        refine ⟨398870621449560323956009565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265913747633040215970673043 398870621449560323956009565)
        ·
          refine ⟨149576483043585121483503587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398870621449560323956009565 149576483043585121483503587)
          ·
            refine ⟨224364724565377682225255381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149576483043585121483503587 224364724565377682225255381)
            ·
              refine ⟨5258548232001039427154423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 224364724565377682225255381 5258548232001039427154423)
              ·
                refine ⟨7887822348001559140731635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258548232001039427154423 7887822348001559140731635)
                ·
                  refine ⟨11831733522002338711097453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7887822348001559140731635 11831733522002338711097453)
                  ·
                    refine ⟨4436900070750877016661545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11831733522002338711097453 4436900070750877016661545)
                    ·
                      refine ⟨3327675053063157762496159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4436900070750877016661545 3327675053063157762496159)
                      ·
                        rfl

theorem cell23_6480624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 1, 3, 2].length) (baseStart_6480624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480624 prefixEnd_6480624 := by exact prefixLift 6480624
  have htrace : WordTrace (prefixWord ++ tailWord_6480624) baseStart_6480624 baseEnd_6480624 := by
    simpa [prefixWord, tailWord_6480624, baseEnd_6480624] using wordTrace_append hprefix tailTrace_6480624
  have hstable : (prefixWord ++ tailWord_6480624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480624).length < 2 ^ (prefixWord ++ tailWord_6480624).sum := by decide
  have hdescent : baseEnd_6480624 < baseStart_6480624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480630 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_6480630 : Nat := 118140960795 + 6480630 * 2 ^ 59
def prefixEnd_6480630 : Nat := 4983230072969 + 3 ^ 40 * 6480630 * 2
def baseEnd_6480630 : Nat := 1109226044649028246340377

theorem tailTrace_6480630 : CollatzResearch.WordTrace tailWord_6480630 prefixEnd_6480630 1109226044649028246340377 := by
  unfold tailWord_6480630
  simp only [CollatzResearch.WordTrace]
  refine ⟨14772999656986986770748959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157578663007861192221322229 14772999656986986770748959)
  ·
    refine ⟨22159499485480480156123439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14772999656986986770748959 22159499485480480156123439)
    ·
      refine ⟨33239249228220720234185159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22159499485480480156123439 33239249228220720234185159)
      ·
        refine ⟨49858873842331080351277739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33239249228220720234185159 49858873842331080351277739)
        ·
          refine ⟨74788310763496620526916609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49858873842331080351277739 74788310763496620526916609)
          ·
            refine ⟨56091233072622465395187457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74788310763496620526916609 56091233072622465395187457)
            ·
              refine ⟨42068424804466849046390593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56091233072622465395187457 42068424804466849046390593)
              ·
                refine ⟨31551318603350136784792945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42068424804466849046390593 31551318603350136784792945)
                ·
                  refine ⟨23663488952512602588594709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31551318603350136784792945 23663488952512602588594709)
                  ·
                    refine ⟨1109226044649028246340377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23663488952512602588594709 1109226044649028246340377)
                    ·
                      rfl

theorem cell23_6480630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_6480630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480630 prefixEnd_6480630 := by exact prefixLift 6480630
  have htrace : WordTrace (prefixWord ++ tailWord_6480630) baseStart_6480630 baseEnd_6480630 := by
    simpa [prefixWord, tailWord_6480630, baseEnd_6480630] using wordTrace_append hprefix tailTrace_6480630
  have hstable : (prefixWord ++ tailWord_6480630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480630).length < 2 ^ (prefixWord ++ tailWord_6480630).sum := by decide
  have hdescent : baseEnd_6480630 < baseStart_6480630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480633 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 3, 4, 4]
def baseStart_6480633 : Nat := 118140960795 + 6480633 * 2 ^ 59
def prefixEnd_6480633 : Nat := 4983230072969 + 3 ^ 40 * 6480633 * 2
def baseEnd_6480633 : Nat := 3327679674389048227283617

theorem tailTrace_6480633 : CollatzResearch.WordTrace tailWord_6480633 prefixEnd_6480633 3327679674389048227283617 := by
  unfold tailWord_6480633
  simp only [CollatzResearch.WordTrace]
  refine ⟨236368103930780919844342553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157578735953853946562895035 236368103930780919844342553)
  ·
    refine ⟨177276077948085689883256915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236368103930780919844342553 177276077948085689883256915)
    ·
      refine ⟨265914116922128534824885373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177276077948085689883256915 265914116922128534824885373)
      ·
        refine ⟨99717793845798200559332015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265914116922128534824885373 99717793845798200559332015)
        ·
          refine ⟨149576690768697300838998023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99717793845798200559332015 149576690768697300838998023)
          ·
            refine ⟨224365036153045951258497035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149576690768697300838998023 224365036153045951258497035)
            ·
              refine ⟨336547554229568926887745553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224365036153045951258497035 336547554229568926887745553)
              ·
                refine ⟨252410665672176695165809165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336547554229568926887745553 252410665672176695165809165)
                ·
                  refine ⟨94653999627066260687178437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252410665672176695165809165 94653999627066260687178437)
                  ·
                    refine ⟨17747624930074923878845957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94653999627066260687178437 17747624930074923878845957)
                    ·
                      refine ⟨3327679674389048227283617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17747624930074923878845957 3327679674389048227283617)
                      ·
                        rfl

theorem cell23_6480633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_6480633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480633 prefixEnd_6480633 := by exact prefixLift 6480633
  have htrace : WordTrace (prefixWord ++ tailWord_6480633) baseStart_6480633 baseEnd_6480633 := by
    simpa [prefixWord, tailWord_6480633, baseEnd_6480633] using wordTrace_append hprefix tailTrace_6480633
  have hstable : (prefixWord ++ tailWord_6480633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480633).length < 2 ^ (prefixWord ++ tailWord_6480633).sum := by decide
  have hdescent : baseEnd_6480633 < baseStart_6480633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480643 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 7]
def baseStart_6480643 : Nat := 118140960795 + 6480643 * 2 ^ 59
def prefixEnd_6480643 : Nat := 4983230072969 + 3 ^ 40 * 6480643 * 2
def baseEnd_6480643 : Nat := 369742756577288132017619

theorem tailTrace_6480643 : CollatzResearch.WordTrace tailWord_6480643 prefixEnd_6480643 369742756577288132017619 := by
  unfold tailWord_6480643
  simp only [CollatzResearch.WordTrace]
  refine ⟨236368468660744691552206583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157578979107163127701471055 236368468660744691552206583)
  ·
    refine ⟨354552702991117037328309875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236368468660744691552206583 354552702991117037328309875)
    ·
      refine ⟨531829054486675555992464813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354552702991117037328309875 531829054486675555992464813)
      ·
        refine ⟨199435895432503333497174305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 531829054486675555992464813 199435895432503333497174305)
        ·
          refine ⟨149576921574377500122880729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199435895432503333497174305 149576921574377500122880729)
          ·
            refine ⟨112182691180783125092160547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149576921574377500122880729 112182691180783125092160547)
            ·
              refine ⟨168274036771174687638240821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112182691180783125092160547 168274036771174687638240821)
              ·
                refine ⟨15775690947297626966085077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168274036771174687638240821 15775690947297626966085077)
                ·
                  refine ⟨369742756577288132017619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15775690947297626966085077 369742756577288132017619)
                  ·
                    rfl

theorem cell23_6480643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 7].length) (baseStart_6480643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480643 prefixEnd_6480643 := by exact prefixLift 6480643
  have htrace : WordTrace (prefixWord ++ tailWord_6480643) baseStart_6480643 baseEnd_6480643 := by
    simpa [prefixWord, tailWord_6480643, baseEnd_6480643] using wordTrace_append hprefix tailTrace_6480643
  have hstable : (prefixWord ++ tailWord_6480643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480643).length < 2 ^ (prefixWord ++ tailWord_6480643).sum := by decide
  have hdescent : baseEnd_6480643 < baseStart_6480643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480650 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_6480650 : Nat := 118140960795 + 6480650 * 2 ^ 59
def prefixEnd_6480650 : Nat := 4983230072969 + 3 ^ 40 * 6480650 * 2
def baseEnd_6480650 : Nat := 3327688403560174660771039

theorem tailTrace_6480650 : CollatzResearch.WordTrace tailWord_6480650 prefixEnd_6480650 3327688403560174660771039 := by
  unfold tailWord_6480650
  simp only [CollatzResearch.WordTrace]
  refine ⟨59092180992929832936927851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157579149314479554498474269 59092180992929832936927851)
  ·
    refine ⟨88638271489394749405391777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59092180992929832936927851 88638271489394749405391777)
    ·
      refine ⟨66478703617046062054043833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88638271489394749405391777 66478703617046062054043833)
      ·
        refine ⟨49859027712784546540532875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66478703617046062054043833 49859027712784546540532875)
        ·
          refine ⟨74788541569176819810799313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49859027712784546540532875 74788541569176819810799313)
          ·
            refine ⟨56091406176882614858099485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74788541569176819810799313 56091406176882614858099485)
            ·
              refine ⟨21034277316330980571787307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56091406176882614858099485 21034277316330980571787307)
              ·
                refine ⟨31551415974496470857680961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21034277316330980571787307 31551415974496470857680961)
                ·
                  refine ⟨23663561980872353143260721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31551415974496470857680961 23663561980872353143260721)
                  ·
                    refine ⟨17747671485654264857445541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23663561980872353143260721 17747671485654264857445541)
                    ·
                      refine ⟨3327688403560174660771039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17747671485654264857445541 3327688403560174660771039)
                      ·
                        rfl

theorem cell23_6480650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_6480650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480650 prefixEnd_6480650 := by exact prefixLift 6480650
  have htrace : WordTrace (prefixWord ++ tailWord_6480650) baseStart_6480650 baseEnd_6480650 := by
    simpa [prefixWord, tailWord_6480650, baseEnd_6480650] using wordTrace_append hprefix tailTrace_6480650
  have hstable : (prefixWord ++ tailWord_6480650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480650).length < 2 ^ (prefixWord ++ tailWord_6480650).sum := by decide
  have hdescent : baseEnd_6480650 < baseStart_6480650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480677 : List Nat := [1, 3, 1, 2, 3, 1, 4, 3, 5]
def baseStart_6480677 : Nat := 118140960795 + 6480677 * 2 ^ 59
def prefixEnd_6480677 : Nat := 4983230072969 + 3 ^ 40 * 6480677 * 2
def baseEnd_6480677 : Nat := 369744696393094006125935

theorem tailTrace_6480677 : CollatzResearch.WordTrace tailWord_6480677 prefixEnd_6480677 369744696393094006125935 := by
  unfold tailWord_6480677
  simp only [CollatzResearch.WordTrace]
  refine ⟨236369708742621515358944285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157579805828414343572629523 236369708742621515358944285)
  ·
    refine ⟨88638640778483068259604107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236369708742621515358944285 88638640778483068259604107)
    ·
      refine ⟨132957961167724602389406161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88638640778483068259604107 132957961167724602389406161)
      ·
        refine ⟨99718470875793451792054621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132957961167724602389406161 99718470875793451792054621)
        ·
          refine ⟨37394426578422544422020483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99718470875793451792054621 37394426578422544422020483)
          ·
            refine ⟨56091639867633816633030725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37394426578422544422020483 56091639867633816633030725)
            ·
              refine ⟨10517182475181340618693261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56091639867633816633030725 10517182475181340618693261)
              ·
                refine ⟨3943943428193002732009973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10517182475181340618693261 3943943428193002732009973)
                ·
                  refine ⟨369744696393094006125935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3943943428193002732009973 369744696393094006125935)
                  ·
                    rfl

theorem cell23_6480677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 5].length) (baseStart_6480677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480677 prefixEnd_6480677 := by exact prefixLift 6480677
  have htrace : WordTrace (prefixWord ++ tailWord_6480677) baseStart_6480677 baseEnd_6480677 := by
    simpa [prefixWord, tailWord_6480677, baseEnd_6480677] using wordTrace_append hprefix tailTrace_6480677
  have hstable : (prefixWord ++ tailWord_6480677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480677).length < 2 ^ (prefixWord ++ tailWord_6480677).sum := by decide
  have hdescent : baseEnd_6480677 < baseStart_6480677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480690 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_6480690 : Nat := 118140960795 + 6480690 * 2 ^ 59
def prefixEnd_6480690 : Nat := 4983230072969 + 3 ^ 40 * 6480690 * 2
def baseEnd_6480690 : Nat := 1109236314262118168090285

theorem tailTrace_6480690 : CollatzResearch.WordTrace tailWord_6480690 prefixEnd_6480690 1109236314262118168090285 := by
  unfold tailWord_6480690
  simp only [CollatzResearch.WordTrace]
  refine ⟨59092545722893604644791881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157580121927716279052778349 59092545722893604644791881)
  ·
    refine ⟨44319409292170203483593911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59092545722893604644791881 44319409292170203483593911)
    ·
      refine ⟨66479113938255305225390867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44319409292170203483593911 66479113938255305225390867)
      ·
        refine ⟨99718670907382957838086301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66479113938255305225390867 99718670907382957838086301)
        ·
          refine ⟨37394501590268609189282363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99718670907382957838086301 37394501590268609189282363)
          ·
            refine ⟨56091752385402913783923545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37394501590268609189282363 56091752385402913783923545)
            ·
              refine ⟨42068814289052185337942659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56091752385402913783923545 42068814289052185337942659)
              ·
                refine ⟨63103221433578278006913989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42068814289052185337942659 63103221433578278006913989)
                ·
                  refine ⟨11831854018795927126296373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63103221433578278006913989 11831854018795927126296373)
                  ·
                    refine ⟨1109236314262118168090285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11831854018795927126296373 1109236314262118168090285)
                    ·
                      rfl

theorem cell23_6480690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_6480690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480690 prefixEnd_6480690 := by exact prefixLift 6480690
  have htrace : WordTrace (prefixWord ++ tailWord_6480690) baseStart_6480690 baseEnd_6480690 := by
    simpa [prefixWord, tailWord_6480690, baseEnd_6480690] using wordTrace_append hprefix tailTrace_6480690
  have hstable : (prefixWord ++ tailWord_6480690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480690).length < 2 ^ (prefixWord ++ tailWord_6480690).sum := by decide
  have hdescent : baseEnd_6480690 < baseStart_6480690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480694 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_6480694 : Nat := 118140960795 + 6480694 * 2 ^ 59
def prefixEnd_6480694 : Nat := 4983230072969 + 3 ^ 40 * 6480694 * 2
def baseEnd_6480694 : Nat := 369745666300996943180093

theorem tailTrace_6480694 : CollatzResearch.WordTrace tailWord_6480694 prefixEnd_6480694 369745666300996943180093 := by
  unfold tailWord_6480694
  simp only [CollatzResearch.WordTrace]
  refine ⟨14773145548972495453894571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157580219189039951508208757 14773145548972495453894571)
  ·
    refine ⟨22159718323458743180841857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14773145548972495453894571 22159718323458743180841857)
    ·
      refine ⟨16619788742594057385631393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22159718323458743180841857 16619788742594057385631393)
      ·
        refine ⟨12464841556945543039223545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16619788742594057385631393 12464841556945543039223545)
        ·
          refine ⟨9348631167709157279417659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12464841556945543039223545 9348631167709157279417659)
          ·
            refine ⟨14022946751563735919126489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9348631167709157279417659 14022946751563735919126489)
            ·
              refine ⟨10517210063672801939344867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14022946751563735919126489 10517210063672801939344867)
              ·
                refine ⟨15775815095509202909017301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10517210063672801939344867 15775815095509202909017301)
                ·
                  refine ⟨369745666300996943180093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15775815095509202909017301 369745666300996943180093)
                  ·
                    rfl

theorem cell23_6480694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_6480694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480694 prefixEnd_6480694 := by exact prefixLift 6480694
  have htrace : WordTrace (prefixWord ++ tailWord_6480694) baseStart_6480694 baseEnd_6480694 := by
    simpa [prefixWord, tailWord_6480694, baseEnd_6480694] using wordTrace_append hprefix tailTrace_6480694
  have hstable : (prefixWord ++ tailWord_6480694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480694).length < 2 ^ (prefixWord ++ tailWord_6480694).sum := by decide
  have hdescent : baseEnd_6480694 < baseStart_6480694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480705 : List Nat := [1, 2, 5, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6480705 : Nat := 118140960795 + 6480705 * 2 ^ 59
def prefixEnd_6480705 : Nat := 4983230072969 + 3 ^ 40 * 6480705 * 2
def baseEnd_6480705 : Nat := 3327716644996171945583287

theorem tailTrace_6480705 : CollatzResearch.WordTrace tailWord_6480705 prefixEnd_6480705 3327716644996171945583287 := by
  unfold tailWord_6480705
  simp only [CollatzResearch.WordTrace]
  refine ⟨236370729986520076140963569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157580486657680050760642379 236370729986520076140963569)
  ·
    refine ⟨177278047489890057105722677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236370729986520076140963569 177278047489890057105722677)
    ·
      refine ⟨16619816952177192853661501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177278047489890057105722677 16619816952177192853661501)
      ·
        refine ⟨6232431357066447320123063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16619816952177192853661501 6232431357066447320123063)
        ·
          refine ⟨9348647035599670980184595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6232431357066447320123063 9348647035599670980184595)
          ·
            refine ⟨14022970553399506470276893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9348647035599670980184595 14022970553399506470276893)
            ·
              refine ⟨5258613957524814926353835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14022970553399506470276893 5258613957524814926353835)
              ·
                refine ⟨7887920936287222389530753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258613957524814926353835 7887920936287222389530753)
                ·
                  refine ⟨5915940702215416792148065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7887920936287222389530753 5915940702215416792148065)
                  ·
                    refine ⟨4436955526661562594111049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5915940702215416792148065 4436955526661562594111049)
                    ·
                      refine ⟨3327716644996171945583287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4436955526661562594111049 3327716644996171945583287)
                      ·
                        rfl

theorem cell23_6480705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6480705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480705 prefixEnd_6480705 := by exact prefixLift 6480705
  have htrace : WordTrace (prefixWord ++ tailWord_6480705) baseStart_6480705 baseEnd_6480705 := by
    simpa [prefixWord, tailWord_6480705, baseEnd_6480705] using wordTrace_append hprefix tailTrace_6480705
  have hstable : (prefixWord ++ tailWord_6480705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480705).length < 2 ^ (prefixWord ++ tailWord_6480705).sum := by decide
  have hdescent : baseEnd_6480705 < baseStart_6480705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480754 : List Nat := [3, 2, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_6480754 : Nat := 118140960795 + 6480754 * 2 ^ 59
def prefixEnd_6480754 : Nat := 4983230072969 + 3 ^ 40 * 6480754 * 2
def baseEnd_6480754 : Nat := 1109247268516080751290187

theorem tailTrace_6480754 : CollatzResearch.WordTrace tailWord_6480754 prefixEnd_6480754 1109247268516080751290187 := by
  unfold tailWord_6480754
  simp only [CollatzResearch.WordTrace]
  refine ⟨59093129290835639377374329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157581678108895038339664877 59093129290835639377374329)
  ·
    refine ⟨44319846968126729533030747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59093129290835639377374329 44319846968126729533030747)
    ·
      refine ⟨66479770452190094299546121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44319846968126729533030747 66479770452190094299546121)
      ·
        refine ⟨49859827839142570724659591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66479770452190094299546121 49859827839142570724659591)
        ·
          refine ⟨74789741758713856086989387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49859827839142570724659591 74789741758713856086989387)
          ·
            refine ⟨112184612638070784130484081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74789741758713856086989387 112184612638070784130484081)
            ·
              refine ⟨84138459478553088097863061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112184612638070784130484081 84138459478553088097863061)
              ·
                refine ⟨3943990288057176004587331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84138459478553088097863061 3943990288057176004587331)
                ·
                  refine ⟨5915985432085764006880997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943990288057176004587331 5915985432085764006880997)
                  ·
                    refine ⟨1109247268516080751290187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5915985432085764006880997 1109247268516080751290187)
                    ·
                      rfl

theorem cell23_6480754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_6480754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480754 prefixEnd_6480754 := by exact prefixLift 6480754
  have htrace : WordTrace (prefixWord ++ tailWord_6480754) baseStart_6480754 baseEnd_6480754 := by
    simpa [prefixWord, tailWord_6480754, baseEnd_6480754] using wordTrace_append hprefix tailTrace_6480754
  have hstable : (prefixWord ++ tailWord_6480754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480754).length < 2 ^ (prefixWord ++ tailWord_6480754).sum := by decide
  have hdescent : baseEnd_6480754 < baseStart_6480754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480760 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 2, 5, 3]
def baseStart_6480760 : Nat := 118140960795 + 6480760 * 2 ^ 59
def prefixEnd_6480760 : Nat := 4983230072969 + 3 ^ 40 * 6480760 * 2
def baseEnd_6480760 : Nat := 3327744886432169230395533

theorem tailTrace_6480760 : CollatzResearch.WordTrace tailWord_6480760 prefixEnd_6480760 3327744886432169230395533 := by
  unfold tailWord_6480760
  simp only [CollatzResearch.WordTrace]
  refine ⟨118186368000660410267107867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157581824000880547022810489 118186368000660410267107867)
  ·
    refine ⟨177279552000990615400661801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118186368000660410267107867 177279552000990615400661801)
    ·
      refine ⟨132959664000742961550496351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177279552000990615400661801 132959664000742961550496351)
      ·
        refine ⟨199439496001114442325744527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132959664000742961550496351 199439496001114442325744527)
        ·
          refine ⟨299159244001671663488616791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199439496001114442325744527 299159244001671663488616791)
          ·
            refine ⟨448738866002507495232925187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299159244001671663488616791 448738866002507495232925187)
            ·
              refine ⟨673108299003761242849387781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448738866002507495232925187 673108299003761242849387781)
              ·
                refine ⟨126207806063205233034260209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 673108299003761242849387781 126207806063205233034260209)
                ·
                  refine ⟨94655854547403924775695157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126207806063205233034260209 94655854547403924775695157)
                  ·
                    refine ⟨8873986363819117947721421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94655854547403924775695157 8873986363819117947721421)
                    ·
                      refine ⟨3327744886432169230395533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8873986363819117947721421 3327744886432169230395533)
                      ·
                        rfl

theorem cell23_6480760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_6480760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480760 prefixEnd_6480760 := by exact prefixLift 6480760
  have htrace : WordTrace (prefixWord ++ tailWord_6480760) baseStart_6480760 baseEnd_6480760 := by
    simpa [prefixWord, tailWord_6480760, baseEnd_6480760] using wordTrace_append hprefix tailTrace_6480760
  have hstable : (prefixWord ++ tailWord_6480760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480760).length < 2 ^ (prefixWord ++ tailWord_6480760).sum := by decide
  have hdescent : baseEnd_6480760 < baseStart_6480760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480767 : List Nat := [1, 1, 2, 2, 1, 1, 8, 1, 6]
def baseStart_6480767 : Nat := 118140960795 + 6480767 * 2 ^ 59
def prefixEnd_6480767 : Nat := 4983230072969 + 3 ^ 40 * 6480767 * 2
def baseEnd_6480767 : Nat := 369749831199638967000889

theorem tailTrace_6480767 : CollatzResearch.WordTrace tailWord_6480767 prefixEnd_6480767 369749831199638967000889 := by
  unfold tailWord_6480767
  simp only [CollatzResearch.WordTrace]
  refine ⟨236372991312295460729720555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157581994208196973819813703 236372991312295460729720555)
  ·
    refine ⟨354559486968443191094580833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236372991312295460729720555 354559486968443191094580833)
    ·
      refine ⟨265919615226332393320935625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354559486968443191094580833 265919615226332393320935625)
      ·
        refine ⟨199439711419749294990701719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265919615226332393320935625 199439711419749294990701719)
        ·
          refine ⟨299159567129623942486052579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199439711419749294990701719 299159567129623942486052579)
          ·
            refine ⟨448739350694435913729078869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299159567129623942486052579 448739350694435913729078869)
            ·
              refine ⟨5258664265950420864012643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 448739350694435913729078869 5258664265950420864012643)
              ·
                refine ⟨7887996398925631296018965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258664265950420864012643 7887996398925631296018965)
                ·
                  refine ⟨369749831199638967000889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7887996398925631296018965 369749831199638967000889)
                  ·
                    rfl

theorem cell23_6480767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 6].length) (baseStart_6480767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480767 prefixEnd_6480767 := by exact prefixLift 6480767
  have htrace : WordTrace (prefixWord ++ tailWord_6480767) baseStart_6480767 baseEnd_6480767 := by
    simpa [prefixWord, tailWord_6480767, baseEnd_6480767] using wordTrace_append hprefix tailTrace_6480767
  have hstable : (prefixWord ++ tailWord_6480767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480767).length < 2 ^ (prefixWord ++ tailWord_6480767).sum := by decide
  have hdescent : baseEnd_6480767 < baseStart_6480767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480804 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 2, 3, 2]
def baseStart_6480804 : Nat := 118140960795 + 6480804 * 2 ^ 59
def prefixEnd_6480804 : Nat := 4983230072969 + 3 ^ 40 * 6480804 * 2
def baseEnd_6480804 : Nat := 3327767479580967058245331

theorem tailTrace_6480804 : CollatzResearch.WordTrace tailWord_6480804 prefixEnd_6480804 3327767479580967058245331 := by
  unfold tailWord_6480804
  simp only [CollatzResearch.WordTrace]
  refine ⟨118187170406580708024408733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157582893875440944032544977 118187170406580708024408733)
  ·
    refine ⟨44320188902467765509153275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118187170406580708024408733 44320188902467765509153275)
    ·
      refine ⟨66480283353701648263729913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44320188902467765509153275 66480283353701648263729913)
      ·
        refine ⟨49860212515276236197797435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66480283353701648263729913 49860212515276236197797435)
        ·
          refine ⟨74790318772914354296696153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49860212515276236197797435 74790318772914354296696153)
          ·
            refine ⟨56092739079685765722522115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74790318772914354296696153 56092739079685765722522115)
            ·
              refine ⟨84139108619528648583783173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56092739079685765722522115 84139108619528648583783173)
              ·
                refine ⟨15776082866161621609459345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84139108619528648583783173 15776082866161621609459345)
                ·
                  refine ⟨11832062149621216207094509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15776082866161621609459345 11832062149621216207094509)
                  ·
                    refine ⟨4437023306107956077660441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11832062149621216207094509 4437023306107956077660441)
                    ·
                      refine ⟨3327767479580967058245331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4437023306107956077660441 3327767479580967058245331)
                      ·
                        rfl

theorem cell23_6480804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_6480804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480804 prefixEnd_6480804 := by exact prefixLift 6480804
  have htrace : WordTrace (prefixWord ++ tailWord_6480804) baseStart_6480804 baseEnd_6480804 := by
    simpa [prefixWord, tailWord_6480804, baseEnd_6480804] using wordTrace_append hprefix tailTrace_6480804
  have hstable : (prefixWord ++ tailWord_6480804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480804).length < 2 ^ (prefixWord ++ tailWord_6480804).sum := by decide
  have hdescent : baseEnd_6480804 < baseStart_6480804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480847 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 4]
def baseStart_6480847 : Nat := 118140960795 + 6480847 * 2 ^ 59
def prefixEnd_6480847 : Nat := 4983230072969 + 3 ^ 40 * 6480847 * 2
def baseEnd_6480847 : Nat := 3327789559249110390007633

theorem tailTrace_6480847 : CollatzResearch.WordTrace tailWord_6480847 prefixEnd_6480847 3327789559249110390007633 := by
  unfold tailWord_6480847
  simp only [CollatzResearch.WordTrace]
  refine ⟨236375909152005634392632795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157583939434670422928421863 236375909152005634392632795)
  ·
    refine ⟨354563863728008451588949193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236375909152005634392632795 354563863728008451588949193)
    ·
      refine ⟨265922897796006338691711895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354563863728008451588949193 265922897796006338691711895)
      ·
        refine ⟨398884346694009508037567843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265922897796006338691711895 398884346694009508037567843)
        ·
          refine ⟨598326520041014262056351765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398884346694009508037567843 598326520041014262056351765)
          ·
            refine ⟨28046555626922543533891489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 598326520041014262056351765 28046555626922543533891489)
            ·
              refine ⟨21034916720191907650418617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28046555626922543533891489 21034916720191907650418617)
              ·
                refine ⟨15776187540143930737813963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21034916720191907650418617 15776187540143930737813963)
                ·
                  refine ⟨23664281310215896106720945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15776187540143930737813963 23664281310215896106720945)
                  ·
                    refine ⟨17748210982661922080040709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23664281310215896106720945 17748210982661922080040709)
                    ·
                      refine ⟨3327789559249110390007633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17748210982661922080040709 3327789559249110390007633)
                      ·
                        rfl

theorem cell23_6480847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_6480847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480847 prefixEnd_6480847 := by exact prefixLift 6480847
  have htrace : WordTrace (prefixWord ++ tailWord_6480847) baseStart_6480847 baseEnd_6480847 := by
    simpa [prefixWord, tailWord_6480847, baseEnd_6480847] using wordTrace_append hprefix tailTrace_6480847
  have hstable : (prefixWord ++ tailWord_6480847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480847).length < 2 ^ (prefixWord ++ tailWord_6480847).sum := by decide
  have hdescent : baseEnd_6480847 < baseStart_6480847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480861 : List Nat := [1, 4, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_6480861 : Nat := 118140960795 + 6480861 * 2 ^ 59
def prefixEnd_6480861 : Nat := 4983230072969 + 3 ^ 40 * 6480861 * 2
def baseEnd_6480861 : Nat := 1109265582659424445077523

theorem tailTrace_6480861 : CollatzResearch.WordTrace tailWord_6480861 prefixEnd_6480861 1109265582659424445077523 := by
  unfold tailWord_6480861
  simp only [CollatzResearch.WordTrace]
  refine ⟨236376419773954914783642437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157584279849303276522428291 236376419773954914783642437)
  ·
    refine ⟨44320578707616546521932957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236376419773954914783642437 44320578707616546521932957)
    ·
      refine ⟨16620217015356204945724859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44320578707616546521932957 16620217015356204945724859)
      ·
        refine ⟨24930325523034307418587289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16620217015356204945724859 24930325523034307418587289)
        ·
          refine ⟨18697744142275730563940467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24930325523034307418587289 18697744142275730563940467)
          ·
            refine ⟨28046616213413595845910701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18697744142275730563940467 28046616213413595845910701)
            ·
              refine ⟨10517481080030098442216513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28046616213413595845910701 10517481080030098442216513)
              ·
                refine ⟨7888110810022573831662385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10517481080030098442216513 7888110810022573831662385)
                ·
                  refine ⟨5916083107516930373746789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7888110810022573831662385 5916083107516930373746789)
                  ·
                    refine ⟨1109265582659424445077523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5916083107516930373746789 1109265582659424445077523)
                    ·
                      rfl

theorem cell23_6480861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_6480861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480861 prefixEnd_6480861 := by exact prefixLift 6480861
  have htrace : WordTrace (prefixWord ++ tailWord_6480861) baseStart_6480861 baseEnd_6480861 := by
    simpa [prefixWord, tailWord_6480861, baseEnd_6480861] using wordTrace_append hprefix tailTrace_6480861
  have hstable : (prefixWord ++ tailWord_6480861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480861).length < 2 ^ (prefixWord ++ tailWord_6480861).sum := by decide
  have hdescent : baseEnd_6480861 < baseStart_6480861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480878 : List Nat := [4, 1, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_6480878 : Nat := 118140960795 + 6480878 * 2 ^ 59
def prefixEnd_6480878 : Nat := 4983230072969 + 3 ^ 40 * 6480878 * 2
def baseEnd_6480878 : Nat := 1109268492383133256239997

theorem tailTrace_6480878 : CollatzResearch.WordTrace tailWord_6480878 prefixEnd_6480878 1109268492383133256239997 := by
  unfold tailWord_6480878
  simp only [CollatzResearch.WordTrace]
  refine ⟨29547129976861665835876411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157584693209928884458007525 29547129976861665835876411)
  ·
    refine ⟨44320694965292498753814617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29547129976861665835876411 44320694965292498753814617)
    ·
      refine ⟨33240521223969374065360963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44320694965292498753814617 33240521223969374065360963)
      ·
        refine ⟨49860781835954061098041445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33240521223969374065360963 49860781835954061098041445)
        ·
          refine ⟨9348896594241386455882771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49860781835954061098041445 9348896594241386455882771)
          ·
            refine ⟨14023344891362079683824157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9348896594241386455882771 14023344891362079683824157)
            ·
              refine ⟨5258754334260779881434059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14023344891362079683824157 5258754334260779881434059)
              ·
                refine ⟨7888131501391169822151089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258754334260779881434059 7888131501391169822151089)
                ·
                  refine ⟨5916098626043377366613317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7888131501391169822151089 5916098626043377366613317)
                  ·
                    refine ⟨1109268492383133256239997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5916098626043377366613317 1109268492383133256239997)
                    ·
                      rfl

theorem cell23_6480878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_6480878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480878 prefixEnd_6480878 := by exact prefixLift 6480878
  have htrace : WordTrace (prefixWord ++ tailWord_6480878) baseStart_6480878 baseEnd_6480878 := by
    simpa [prefixWord, tailWord_6480878, baseEnd_6480878] using wordTrace_append hprefix tailTrace_6480878
  have hstable : (prefixWord ++ tailWord_6480878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480878).length < 2 ^ (prefixWord ++ tailWord_6480878).sum := by decide
  have hdescent : baseEnd_6480878 < baseStart_6480878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480897 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_6480897 : Nat := 118140960795 + 6480897 * 2 ^ 59
def prefixEnd_6480897 : Nat := 4983230072969 + 3 ^ 40 * 6480897 * 2
def baseEnd_6480897 : Nat := 3327815233281835194382403

theorem tailTrace_6480897 : CollatzResearch.WordTrace tailWord_6480897 prefixEnd_6480897 3327815233281835194382403 := by
  unfold tailWord_6480897
  simp only [CollatzResearch.WordTrace]
  refine ⟨236377732801824492931952945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157585155201216328621301963 236377732801824492931952945)
  ·
    refine ⟨177283299601368369698964709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236377732801824492931952945 177283299601368369698964709)
    ·
      refine ⟨33240618675256569318555883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177283299601368369698964709 33240618675256569318555883)
      ·
        refine ⟨49860928012884853977833825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33240618675256569318555883 49860928012884853977833825)
        ·
          refine ⟨37395696009663640483375369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49860928012884853977833825 37395696009663640483375369)
          ·
            refine ⟨28046772007247730362531527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37395696009663640483375369 28046772007247730362531527)
            ·
              refine ⟨42070158010871595543797291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28046772007247730362531527 42070158010871595543797291)
              ·
                refine ⟨63105237016307393315695937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42070158010871595543797291 63105237016307393315695937)
                ·
                  refine ⟨47328927762230544986771953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63105237016307393315695937 47328927762230544986771953)
                  ·
                    refine ⟨35496695821672908740078965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47328927762230544986771953 35496695821672908740078965)
                    ·
                      refine ⟨3327815233281835194382403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35496695821672908740078965 3327815233281835194382403)
                      ·
                        rfl

theorem cell23_6480897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_6480897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480897 prefixEnd_6480897 := by exact prefixLift 6480897
  have htrace : WordTrace (prefixWord ++ tailWord_6480897) baseStart_6480897 baseEnd_6480897 := by
    simpa [prefixWord, tailWord_6480897, baseEnd_6480897] using wordTrace_append hprefix tailTrace_6480897
  have hstable : (prefixWord ++ tailWord_6480897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480897).length < 2 ^ (prefixWord ++ tailWord_6480897).sum := by decide
  have hdescent : baseEnd_6480897 < baseStart_6480897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480935 : List Nat := [1, 1, 7, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_6480935 : Nat := 118140960795 + 6480935 * 2 ^ 59
def prefixEnd_6480935 : Nat := 4983230072969 + 3 ^ 40 * 6480935 * 2
def baseEnd_6480935 : Nat := 3327834745546706045707229

theorem tailTrace_6480935 : CollatzResearch.WordTrace tailWord_6480935 prefixEnd_6480935 3327834745546706045707229 := by
  unfold tailWord_6480935
  simp only [CollatzResearch.WordTrace]
  refine ⟨236379118775686825421836259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157586079183791216947890839 236379118775686825421836259)
  ·
    refine ⟨354568678163530238132754389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236379118775686825421836259 354568678163530238132754389)
    ·
      refine ⟨8310203394457739956236431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 354568678163530238132754389 8310203394457739956236431)
      ·
        refine ⟨12465305091686609934354647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8310203394457739956236431 12465305091686609934354647)
        ·
          refine ⟨18697957637529914901531971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12465305091686609934354647 18697957637529914901531971)
          ·
            refine ⟨28046936456294872352297957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18697957637529914901531971 28046936456294872352297957)
            ·
              refine ⟨5258800585555288566055867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28046936456294872352297957 5258800585555288566055867)
              ·
                refine ⟨7888200878332932849083801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258800585555288566055867 7888200878332932849083801)
                ·
                  refine ⟨5916150658749699636812851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7888200878332932849083801 5916150658749699636812851)
                  ·
                    refine ⟨8874225988124549455219277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5916150658749699636812851 8874225988124549455219277)
                    ·
                      refine ⟨3327834745546706045707229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8874225988124549455219277 3327834745546706045707229)
                      ·
                        rfl

theorem cell23_6480935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_6480935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480935 prefixEnd_6480935 := by exact prefixLift 6480935
  have htrace : WordTrace (prefixWord ++ tailWord_6480935) baseStart_6480935 baseEnd_6480935 := by
    simpa [prefixWord, tailWord_6480935, baseEnd_6480935] using wordTrace_append hprefix tailTrace_6480935
  have hstable : (prefixWord ++ tailWord_6480935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480935).length < 2 ^ (prefixWord ++ tailWord_6480935).sum := by decide
  have hdescent : baseEnd_6480935 < baseStart_6480935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480958 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_6480958 : Nat := 118140960795 + 6480958 * 2 ^ 59
def prefixEnd_6480958 : Nat := 4983230072969 + 3 ^ 40 * 6480958 * 2
def baseEnd_6480958 : Nat := 3327846555601759455719623

theorem tailTrace_6480958 : CollatzResearch.WordTrace tailWord_6480958 prefixEnd_6480958 3327846555601759455719623 := by
  unfold tailWord_6480958
  simp only [CollatzResearch.WordTrace]
  refine ⟨29547494706825437543740441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157586638436402333566615685 29547494706825437543740441)
  ·
    refine ⟨22160621030119078157805331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29547494706825437543740441 22160621030119078157805331)
    ·
      refine ⟨33240931545178617236707997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22160621030119078157805331 33240931545178617236707997)
      ·
        refine ⟨12465349329441981463765499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33240931545178617236707997 12465349329441981463765499)
        ·
          refine ⟨18698023994162972195648249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12465349329441981463765499 18698023994162972195648249)
          ·
            refine ⟨14023517995622229146736187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18698023994162972195648249 14023517995622229146736187)
            ·
              refine ⟨21035276993433343720104281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14023517995622229146736187 21035276993433343720104281)
              ·
                refine ⟨15776457745075007790078211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21035276993433343720104281 15776457745075007790078211)
                ·
                  refine ⟨23664686617612511685117317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15776457745075007790078211 23664686617612511685117317)
                  ·
                    refine ⟨4437128740802345940959497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23664686617612511685117317 4437128740802345940959497)
                    ·
                      refine ⟨3327846555601759455719623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4437128740802345940959497 3327846555601759455719623)
                      ·
                        rfl

theorem cell23_6480958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_6480958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480958 prefixEnd_6480958 := by exact prefixLift 6480958
  have htrace : WordTrace (prefixWord ++ tailWord_6480958) baseStart_6480958 baseEnd_6480958 := by
    simpa [prefixWord, tailWord_6480958, baseEnd_6480958] using wordTrace_append hprefix tailTrace_6480958
  have hstable : (prefixWord ++ tailWord_6480958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480958).length < 2 ^ (prefixWord ++ tailWord_6480958).sum := by decide
  have hdescent : baseEnd_6480958 < baseStart_6480958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480974 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_6480974 : Nat := 118140960795 + 6480974 * 2 ^ 59
def prefixEnd_6480974 : Nat := 4983230072969 + 3 ^ 40 * 6480974 * 2
def baseEnd_6480974 : Nat := 3327854771292231393119549

theorem tailTrace_6480974 : CollatzResearch.WordTrace tailWord_6480974 prefixEnd_6480974 3327854771292231393119549 := by
  unfold tailWord_6480974
  simp only [CollatzResearch.WordTrace]
  refine ⟨29547567652818191885313247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157587027481697023388337317 29547567652818191885313247)
  ·
    refine ⟨44321351479227287827969871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29547567652818191885313247 44321351479227287827969871)
    ·
      refine ⟨66482027218840931741954807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44321351479227287827969871 66482027218840931741954807)
      ·
        refine ⟨99723040828261397612932211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66482027218840931741954807 99723040828261397612932211)
        ·
          refine ⟨149584561242392096419398317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99723040828261397612932211 149584561242392096419398317)
          ·
            refine ⟨56094210465897036157274369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149584561242392096419398317 56094210465897036157274369)
            ·
              refine ⟨42070657849422777117955777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56094210465897036157274369 42070657849422777117955777)
              ·
                refine ⟨31552993387067082838466833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42070657849422777117955777 31552993387067082838466833)
                ·
                  refine ⟨23664745040300312128850125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31552993387067082838466833 23664745040300312128850125)
                  ·
                    refine ⟨8874279390112617048318797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23664745040300312128850125 8874279390112617048318797)
                    ·
                      refine ⟨3327854771292231393119549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8874279390112617048318797 3327854771292231393119549)
                      ·
                        rfl

theorem cell23_6480974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_6480974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480974 prefixEnd_6480974 := by exact prefixLift 6480974
  have htrace : WordTrace (prefixWord ++ tailWord_6480974) baseStart_6480974 baseEnd_6480974 := by
    simpa [prefixWord, tailWord_6480974, baseEnd_6480974] using wordTrace_append hprefix tailTrace_6480974
  have hstable : (prefixWord ++ tailWord_6480974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480974).length < 2 ^ (prefixWord ++ tailWord_6480974).sum := by decide
  have hdescent : baseEnd_6480974 < baseStart_6480974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480984 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 1, 7, 2]
def baseStart_6480984 : Nat := 118140960795 + 6480984 * 2 ^ 59
def prefixEnd_6480984 : Nat := 4983230072969 + 3 ^ 40 * 6480984 * 2
def baseEnd_6480984 : Nat := 3327859906098776353994503

theorem tailTrace_6480984 : CollatzResearch.WordTrace tailWord_6480984 prefixEnd_6480984 3327859906098776353994503 := by
  unfold tailWord_6480984
  simp only [CollatzResearch.WordTrace]
  refine ⟨118190452976254653395185003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157587270635006204526913337 118190452976254653395185003)
  ·
    refine ⟨177285679464381980092777505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118190452976254653395185003 177285679464381980092777505)
    ·
      refine ⟨132964259598286485069583129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177285679464381980092777505 132964259598286485069583129)
      ·
        refine ⟨99723194698714863802187347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132964259598286485069583129 99723194698714863802187347)
        ·
          refine ⟨149584792048072295703281021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99723194698714863802187347 149584792048072295703281021)
          ·
            refine ⟨56094297018027110888730383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149584792048072295703281021 56094297018027110888730383)
            ·
              refine ⟨84141445527040666333095575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56094297018027110888730383 84141445527040666333095575)
              ·
                refine ⟨126212168290560999499643363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84141445527040666333095575 126212168290560999499643363)
                ·
                  refine ⟨189318252435841499249465045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126212168290560999499643363 189318252435841499249465045)
                  ·
                    refine ⟨4437146541465035138659337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 189318252435841499249465045 4437146541465035138659337)
                    ·
                      refine ⟨3327859906098776353994503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4437146541465035138659337 3327859906098776353994503)
                      ·
                        rfl

theorem cell23_6480984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_6480984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6480984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6480984 prefixEnd_6480984 := by exact prefixLift 6480984
  have htrace : WordTrace (prefixWord ++ tailWord_6480984) baseStart_6480984 baseEnd_6480984 := by
    simpa [prefixWord, tailWord_6480984, baseEnd_6480984] using wordTrace_append hprefix tailTrace_6480984
  have hstable : (prefixWord ++ tailWord_6480984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480984).length < 2 ^ (prefixWord ++ tailWord_6480984).sum := by decide
  have hdescent : baseEnd_6480984 < baseStart_6480984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481027 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 6]
def baseStart_6481027 : Nat := 118140960795 + 6481027 * 2 ^ 59
def prefixEnd_6481027 : Nat := 4983230072969 + 3 ^ 40 * 6481027 * 2
def baseEnd_6481027 : Nat := 3327881985766919685756805

theorem tailTrace_6481027 : CollatzResearch.WordTrace tailWord_6481027 prefixEnd_6481027 3327881985766919685756805 := by
  unfold tailWord_6481027
  simp only [CollatzResearch.WordTrace]
  refine ⟨236382474291353525134185335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157588316194235683422790223 236382474291353525134185335)
  ·
    refine ⟨354573711437030287701278003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236382474291353525134185335 354573711437030287701278003)
    ·
      refine ⟨531860567155545431551917005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354573711437030287701278003 531860567155545431551917005)
      ·
        refine ⟨199447712683329536831968877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 531860567155545431551917005 199447712683329536831968877)
        ·
          refine ⟨74792892256248576311988329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199447712683329536831968877 74792892256248576311988329)
          ·
            refine ⟨56094669192186432233991247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74792892256248576311988329 56094669192186432233991247)
            ·
              refine ⟨84142003788279648350986871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56094669192186432233991247 84142003788279648350986871)
              ·
                refine ⟨126213005682419472526480307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84142003788279648350986871 126213005682419472526480307)
                ·
                  refine ⟨189319508523629208789720461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126213005682419472526480307 189319508523629208789720461)
                  ·
                    refine ⟨70994815696360953296145173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189319508523629208789720461 70994815696360953296145173)
                    ·
                      refine ⟨3327881985766919685756805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70994815696360953296145173 3327881985766919685756805)
                      ·
                        rfl

theorem cell23_6481027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_6481027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481027 prefixEnd_6481027 := by exact prefixLift 6481027
  have htrace : WordTrace (prefixWord ++ tailWord_6481027) baseStart_6481027 baseEnd_6481027 := by
    simpa [prefixWord, tailWord_6481027, baseEnd_6481027] using wordTrace_append hprefix tailTrace_6481027
  have hstable : (prefixWord ++ tailWord_6481027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481027).length < 2 ^ (prefixWord ++ tailWord_6481027).sum := by decide
  have hdescent : baseEnd_6481027 < baseStart_6481027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481092 : List Nat := [2, 3, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_6481092 : Nat := 118140960795 + 6481092 * 2 ^ 59
def prefixEnd_6481092 : Nat := 4983230072969 + 3 ^ 40 * 6481092 * 2
def baseEnd_6481092 : Nat := 1109305120669820643814669

theorem tailTrace_6481092 : CollatzResearch.WordTrace tailWord_6481092 prefixEnd_6481092 1109305120669820643814669 := by
  unfold tailWord_6481092
  simp only [CollatzResearch.WordTrace]
  refine ⟨118192422518059020617650765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157589896690745360823534353 118192422518059020617650765)
  ·
    refine ⟨44322158444272132731619037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118192422518059020617650765 44322158444272132731619037)
    ·
      refine ⟨16620809416602049774357139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44322158444272132731619037 16620809416602049774357139)
      ·
        refine ⟨24931214124903074661535709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16620809416602049774357139 24931214124903074661535709)
        ·
          refine ⟨9349205296838652998075891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24931214124903074661535709 9349205296838652998075891)
          ·
            refine ⟨14023807945257979497113837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9349205296838652998075891 14023807945257979497113837)
            ·
              refine ⟨5258927979471742311417689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14023807945257979497113837 5258927979471742311417689)
              ·
                refine ⟨3944195984603806733563267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5258927979471742311417689 3944195984603806733563267)
                ·
                  refine ⟨5916293976905710100344901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3944195984603806733563267 5916293976905710100344901)
                  ·
                    refine ⟨1109305120669820643814669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5916293976905710100344901 1109305120669820643814669)
                    ·
                      rfl

theorem cell23_6481092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_6481092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481092 prefixEnd_6481092 := by exact prefixLift 6481092
  have htrace : WordTrace (prefixWord ++ tailWord_6481092) baseStart_6481092 baseEnd_6481092 := by
    simpa [prefixWord, tailWord_6481092, baseEnd_6481092] using wordTrace_append hprefix tailTrace_6481092
  have hstable : (prefixWord ++ tailWord_6481092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481092).length < 2 ^ (prefixWord ++ tailWord_6481092).sum := by decide
  have hdescent : baseEnd_6481092 < baseStart_6481092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481098 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_6481098 : Nat := 118140960795 + 6481098 * 2 ^ 59
def prefixEnd_6481098 : Nat := 4983230072969 + 3 ^ 40 * 6481098 * 2
def baseEnd_6481098 : Nat := 3327918442893388907968979

theorem tailTrace_6481098 : CollatzResearch.WordTrace tailWord_6481098 prefixEnd_6481098 3327918442893388907968979 := by
  unfold tailWord_6481098
  simp only [CollatzResearch.WordTrace]
  refine ⟨59096265968524076065004987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157590042582730869506679965 59096265968524076065004987)
  ·
    refine ⟨88644398952786114097507481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59096265968524076065004987 88644398952786114097507481)
    ·
      refine ⟨66483299214589585573130611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88644398952786114097507481 66483299214589585573130611)
      ·
        refine ⟨99724948821884378359695917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66483299214589585573130611 99724948821884378359695917)
        ·
          refine ⟨37396855808206641884885969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99724948821884378359695917 37396855808206641884885969)
          ·
            refine ⟨28047641856154981413664477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37396855808206641884885969 28047641856154981413664477)
            ·
              refine ⟨10517865696058118030124179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28047641856154981413664477 10517865696058118030124179)
              ·
                refine ⟨15776798544087177045186269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10517865696058118030124179 15776798544087177045186269)
                ·
                  refine ⟨5916299454032691391944851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15776798544087177045186269 5916299454032691391944851)
                  ·
                    refine ⟨8874449181049037087917277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5916299454032691391944851 8874449181049037087917277)
                    ·
                      refine ⟨3327918442893388907968979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8874449181049037087917277 3327918442893388907968979)
                      ·
                        rfl

theorem cell23_6481098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_6481098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481098 prefixEnd_6481098 := by exact prefixLift 6481098
  have htrace : WordTrace (prefixWord ++ tailWord_6481098) baseStart_6481098 baseEnd_6481098 := by
    simpa [prefixWord, tailWord_6481098, baseEnd_6481098] using wordTrace_append hprefix tailTrace_6481098
  have hstable : (prefixWord ++ tailWord_6481098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481098).length < 2 ^ (prefixWord ++ tailWord_6481098).sum := by decide
  have hdescent : baseEnd_6481098 < baseStart_6481098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481114 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 1, 6]
def baseStart_6481114 : Nat := 118140960795 + 6481114 * 2 ^ 59
def prefixEnd_6481114 : Nat := 4983230072969 + 3 ^ 40 * 6481114 * 2
def baseEnd_6481114 : Nat := 1109308886194620281789635

theorem tailTrace_6481114 : CollatzResearch.WordTrace tailWord_6481114 prefixEnd_6481114 1109308886194620281789635 := by
  unfold tailWord_6481114
  simp only [CollatzResearch.WordTrace]
  refine ⟨59096411860509584748150599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157590431628025559328401597 59096411860509584748150599)
  ·
    refine ⟨88644617790764377122225899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59096411860509584748150599 88644617790764377122225899)
    ·
      refine ⟨132966926686146565683338849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88644617790764377122225899 132966926686146565683338849)
      ·
        refine ⟨99725195014609924262504137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132966926686146565683338849 99725195014609924262504137)
        ·
          refine ⟨74793896260957443196878103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99725195014609924262504137 74793896260957443196878103)
          ·
            refine ⟨112190844391436164795317155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74793896260957443196878103 112190844391436164795317155)
            ·
              refine ⟨168286266587154247192975733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112190844391436164795317155 168286266587154247192975733)
              ·
                refine ⟨15776837492545710674341475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168286266587154247192975733 15776837492545710674341475)
                ·
                  refine ⟨23665256238818566011512213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15776837492545710674341475 23665256238818566011512213)
                  ·
                    refine ⟨1109308886194620281789635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23665256238818566011512213 1109308886194620281789635)
                    ·
                      rfl

theorem cell23_6481114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_6481114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481114 prefixEnd_6481114 := by exact prefixLift 6481114
  have htrace : WordTrace (prefixWord ++ tailWord_6481114) baseStart_6481114 baseEnd_6481114 := by
    simpa [prefixWord, tailWord_6481114, baseEnd_6481114] using wordTrace_append hprefix tailTrace_6481114
  have hstable : (prefixWord ++ tailWord_6481114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481114).length < 2 ^ (prefixWord ++ tailWord_6481114).sum := by decide
  have hdescent : baseEnd_6481114 < baseStart_6481114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481121 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_6481121 : Nat := 118140960795 + 6481121 * 2 ^ 59
def prefixEnd_6481121 : Nat := 4983230072969 + 3 ^ 40 * 6481121 * 2
def baseEnd_6481121 : Nat := 3327930252948442317981373

theorem tailTrace_6481121 : CollatzResearch.WordTrace tailWord_6481121 prefixEnd_6481121 3327930252948442317981373 := by
  unfold tailWord_6481121
  simp only [CollatzResearch.WordTrace]
  refine ⟨236385902753012979188107217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157590601835341986125404811 236385902753012979188107217)
  ·
    refine ⟨177289427064759734391080413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236385902753012979188107217 177289427064759734391080413)
    ·
      refine ⟨66483535149284900396655155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177289427064759734391080413 66483535149284900396655155)
      ·
        refine ⟨99725302723927350594982733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66483535149284900396655155 99725302723927350594982733)
        ·
          refine ⟨37396988521472756473118525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99725302723927350594982733 37396988521472756473118525)
          ·
            refine ⟨14023870695552283677419447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37396988521472756473118525 14023870695552283677419447)
            ·
              refine ⟨21035806043328425516129171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14023870695552283677419447 21035806043328425516129171)
              ·
                refine ⟨31553709064992638274193757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21035806043328425516129171 31553709064992638274193757)
                ·
                  refine ⟨11832640899372239352822659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31553709064992638274193757 11832640899372239352822659)
                  ·
                    refine ⟨17748961349058359029233989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11832640899372239352822659 17748961349058359029233989)
                    ·
                      refine ⟨3327930252948442317981373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17748961349058359029233989 3327930252948442317981373)
                      ·
                        rfl

theorem cell23_6481121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_6481121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481121 prefixEnd_6481121 := by exact prefixLift 6481121
  have htrace : WordTrace (prefixWord ++ tailWord_6481121) baseStart_6481121 baseEnd_6481121 := by
    simpa [prefixWord, tailWord_6481121, baseEnd_6481121] using wordTrace_append hprefix tailTrace_6481121
  have hstable : (prefixWord ++ tailWord_6481121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481121).length < 2 ^ (prefixWord ++ tailWord_6481121).sum := by decide
  have hdescent : baseEnd_6481121 < baseStart_6481121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481124 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_6481124 : Nat := 118140960795 + 6481124 * 2 ^ 59
def prefixEnd_6481124 : Nat := 4983230072969 + 3 ^ 40 * 6481124 * 2
def baseEnd_6481124 : Nat := 3327931793390405806243859

theorem tailTrace_6481124 : CollatzResearch.WordTrace tailWord_6481124 prefixEnd_6481124 3327931793390405806243859 := by
  unfold tailWord_6481124
  simp only [CollatzResearch.WordTrace]
  refine ⟨118193006086001055350233213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157590674781334740466977617 118193006086001055350233213)
  ·
    refine ⟨44322377282250395756337455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118193006086001055350233213 44322377282250395756337455)
    ·
      refine ⟨66483565923375593634506183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44322377282250395756337455 66483565923375593634506183)
      ·
        refine ⟨99725348885063390451759275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66483565923375593634506183 99725348885063390451759275)
        ·
          refine ⟨149588023327595085677638913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99725348885063390451759275 149588023327595085677638913)
          ·
            refine ⟨112191017495696314258229185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149588023327595085677638913 112191017495696314258229185)
            ·
              refine ⟨84143263121772235693671889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112191017495696314258229185 84143263121772235693671889)
              ·
                refine ⟨63107447341329176770253917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84143263121772235693671889 63107447341329176770253917)
                ·
                  refine ⟨23665292752998441288845219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63107447341329176770253917 23665292752998441288845219)
                  ·
                    refine ⟨35497939129497661933267829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23665292752998441288845219 35497939129497661933267829)
                    ·
                      refine ⟨3327931793390405806243859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35497939129497661933267829 3327931793390405806243859)
                      ·
                        rfl

theorem cell23_6481124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_6481124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481124 prefixEnd_6481124 := by exact prefixLift 6481124
  have htrace : WordTrace (prefixWord ++ tailWord_6481124) baseStart_6481124 baseEnd_6481124 := by
    simpa [prefixWord, tailWord_6481124, baseEnd_6481124] using wordTrace_append hprefix tailTrace_6481124
  have hstable : (prefixWord ++ tailWord_6481124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481124).length < 2 ^ (prefixWord ++ tailWord_6481124).sum := by decide
  have hdescent : baseEnd_6481124 < baseStart_6481124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481125 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 2, 3, 2]
def baseStart_6481125 : Nat := 118140960795 + 6481125 * 2 ^ 59
def prefixEnd_6481125 : Nat := 4983230072969 + 3 ^ 40 * 6481125 * 2
def baseEnd_6481125 : Nat := 3327932306871060302331355

theorem tailTrace_6481125 : CollatzResearch.WordTrace tailWord_6481125 prefixEnd_6481125 3327932306871060302331355 := by
  unfold tailWord_6481125
  simp only [CollatzResearch.WordTrace]
  refine ⟨236386048644998487871252829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157590699096665658580835219 236386048644998487871252829)
  ·
    refine ⟨88644768241874432951719811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236386048644998487871252829 88644768241874432951719811)
    ·
      refine ⟨132967152362811649427579717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88644768241874432951719811 132967152362811649427579717)
      ·
        refine ⟨24931341068027184267671197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132967152362811649427579717 24931341068027184267671197)
        ·
          refine ⟨9349252900510194100376699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24931341068027184267671197 9349252900510194100376699)
          ·
            refine ⟨14023879350765291150565049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9349252900510194100376699 14023879350765291150565049)
            ·
              refine ⟨10517909513073968362923787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14023879350765291150565049 10517909513073968362923787)
              ·
                refine ⟨15776864269610952544385681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10517909513073968362923787 15776864269610952544385681)
                ·
                  refine ⟨11832648202208214408289261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15776864269610952544385681 11832648202208214408289261)
                  ·
                    refine ⟨4437243075828080403108473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11832648202208214408289261 4437243075828080403108473)
                    ·
                      refine ⟨3327932306871060302331355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4437243075828080403108473 3327932306871060302331355)
                      ·
                        rfl

theorem cell23_6481125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_6481125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481125 prefixEnd_6481125 := by exact prefixLift 6481125
  have htrace : WordTrace (prefixWord ++ tailWord_6481125) baseStart_6481125 baseEnd_6481125 := by
    simpa [prefixWord, tailWord_6481125, baseEnd_6481125] using wordTrace_append hprefix tailTrace_6481125
  have hstable : (prefixWord ++ tailWord_6481125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481125).length < 2 ^ (prefixWord ++ tailWord_6481125).sum := by decide
  have hdescent : baseEnd_6481125 < baseStart_6481125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481171 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 8, 1, 3]
def baseStart_6481171 : Nat := 118140960795 + 6481171 * 2 ^ 59
def prefixEnd_6481171 : Nat := 4983230072969 + 3 ^ 40 * 6481171 * 2
def baseEnd_6481171 : Nat := 3327955926981167122356143

theorem tailTrace_6481171 : CollatzResearch.WordTrace tailWord_6481171 prefixEnd_6481171 3327955926981167122356143 := by
  unfold tailWord_6481171
  simp only [CollatzResearch.WordTrace]
  refine ⟨236387726402831837727427367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157591817601887891818284911 236387726402831837727427367)
  ·
    refine ⟨354581589604247756591141051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236387726402831837727427367 354581589604247756591141051)
    ·
      refine ⟨531872384406371634886711577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354581589604247756591141051 531872384406371634886711577)
      ·
        refine ⟨398904288304778726165033683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531872384406371634886711577 398904288304778726165033683)
        ·
          refine ⟨598356432457168089247550525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398904288304778726165033683 598356432457168089247550525)
          ·
            refine ⟨224383662171438033467831447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 598356432457168089247550525 224383662171438033467831447)
            ·
              refine ⟨336575493257157050201747171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224383662171438033467831447 336575493257157050201747171)
              ·
                refine ⟨504863239885735575302620757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336575493257157050201747171 504863239885735575302620757)
                ·
                  refine ⟨5916366092410963773077587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 504863239885735575302620757 5916366092410963773077587)
                  ·
                    refine ⟨8874549138616445659616381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5916366092410963773077587 8874549138616445659616381)
                    ·
                      refine ⟨3327955926981167122356143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8874549138616445659616381 3327955926981167122356143)
                      ·
                        rfl

theorem cell23_6481171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 1, 3].length) (baseStart_6481171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481171 prefixEnd_6481171 := by exact prefixLift 6481171
  have htrace : WordTrace (prefixWord ++ tailWord_6481171) baseStart_6481171 baseEnd_6481171 := by
    simpa [prefixWord, tailWord_6481171, baseEnd_6481171] using wordTrace_append hprefix tailTrace_6481171
  have hstable : (prefixWord ++ tailWord_6481171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481171).length < 2 ^ (prefixWord ++ tailWord_6481171).sum := by decide
  have hdescent : baseEnd_6481171 < baseStart_6481171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481188 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_6481188 : Nat := 118140960795 + 6481188 * 2 ^ 59
def prefixEnd_6481188 : Nat := 4983230072969 + 3 ^ 40 * 6481188 * 2
def baseEnd_6481188 : Nat := 3327964656152293555843565

theorem tailTrace_6481188 : CollatzResearch.WordTrace tailWord_6481188 prefixEnd_6481188 3327964656152293555843565 := by
  unfold tailWord_6481188
  simp only [CollatzResearch.WordTrace]
  refine ⟨118194173221885124815398109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157592230962513499753864145 118194173221885124815398109)
  ·
    refine ⟨44322814958206921805774291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118194173221885124815398109 44322814958206921805774291)
    ·
      refine ⟨66484222437310382708661437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44322814958206921805774291 66484222437310382708661437)
      ·
        refine ⟨24931583413991393515748039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66484222437310382708661437 24931583413991393515748039)
        ·
          refine ⟨37397375120987090273622059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24931583413991393515748039 37397375120987090273622059)
          ·
            refine ⟨56096062681480635410433089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37397375120987090273622059 56096062681480635410433089)
            ·
              refine ⟨42072047011110476557824817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56096062681480635410433089 42072047011110476557824817)
              ·
                refine ⟨31554035258332857418368613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42072047011110476557824817 31554035258332857418368613)
                ·
                  refine ⟨5916381610937410765944115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31554035258332857418368613 5916381610937410765944115)
                  ·
                    refine ⟨8874572416406116148916173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5916381610937410765944115 8874572416406116148916173)
                    ·
                      refine ⟨3327964656152293555843565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8874572416406116148916173 3327964656152293555843565)
                      ·
                        rfl

theorem cell23_6481188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_6481188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481188 prefixEnd_6481188 := by exact prefixLift 6481188
  have htrace : WordTrace (prefixWord ++ tailWord_6481188) baseStart_6481188 baseEnd_6481188 := by
    simpa [prefixWord, tailWord_6481188, baseEnd_6481188] using wordTrace_append hprefix tailTrace_6481188
  have hstable : (prefixWord ++ tailWord_6481188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481188).length < 2 ^ (prefixWord ++ tailWord_6481188).sum := by decide
  have hdescent : baseEnd_6481188 < baseStart_6481188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481192 : List Nat := [2, 1, 5, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_6481192 : Nat := 118140960795 + 6481192 * 2 ^ 59
def prefixEnd_6481192 : Nat := 4983230072969 + 3 ^ 40 * 6481192 * 2
def baseEnd_6481192 : Nat := 3327966710074911540193547

theorem tailTrace_6481192 : CollatzResearch.WordTrace tailWord_6481192 prefixEnd_6481192 3327966710074911540193547 := by
  unfold tailWord_6481192
  simp only [CollatzResearch.WordTrace]
  refine ⟨118194246167877879156970915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157592328223837172209294553 118194246167877879156970915)
  ·
    refine ⟨177291369251816818735456373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118194246167877879156970915 177291369251816818735456373)
    ·
      refine ⟨16621065867357826756449035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177291369251816818735456373 16621065867357826756449035)
      ·
        refine ⟨24931598801036740134673553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16621065867357826756449035 24931598801036740134673553)
        ·
          refine ⟨18698699100777555101005165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24931598801036740134673553 18698699100777555101005165)
          ·
            refine ⟨7012012162791583162876937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18698699100777555101005165 7012012162791583162876937)
            ·
              refine ⟨5259009122093687372157703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7012012162791583162876937 5259009122093687372157703)
              ·
                refine ⟨7888513683140531058236555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5259009122093687372157703 7888513683140531058236555)
                ·
                  refine ⟨11832770524710796587354833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7888513683140531058236555 11832770524710796587354833)
                  ·
                    refine ⟨8874577893533097440516125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11832770524710796587354833 8874577893533097440516125)
                    ·
                      refine ⟨3327966710074911540193547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8874577893533097440516125 3327966710074911540193547)
                      ·
                        rfl

theorem cell23_6481192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_6481192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481192 prefixEnd_6481192 := by exact prefixLift 6481192
  have htrace : WordTrace (prefixWord ++ tailWord_6481192) baseStart_6481192 baseEnd_6481192 := by
    simpa [prefixWord, tailWord_6481192, baseEnd_6481192] using wordTrace_append hprefix tailTrace_6481192
  have hstable : (prefixWord ++ tailWord_6481192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481192).length < 2 ^ (prefixWord ++ tailWord_6481192).sum := by decide
  have hdescent : baseEnd_6481192 < baseStart_6481192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481205 : List Nat := [1, 3, 3, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_6481205 : Nat := 118140960795 + 6481205 * 2 ^ 59
def prefixEnd_6481205 : Nat := 4983230072969 + 3 ^ 40 * 6481205 * 2
def baseEnd_6481205 : Nat := 3327973385323419989330987

theorem tailTrace_6481205 : CollatzResearch.WordTrace tailWord_6481205 prefixEnd_6481205 3327973385323419989330987 := by
  unfold tailWord_6481205
  simp only [CollatzResearch.WordTrace]
  refine ⟨236388966484708661534165069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157592644323139107689443379 236388966484708661534165069)
  ·
    refine ⟨88645862431765748075311901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236388966484708661534165069 88645862431765748075311901)
    ·
      refine ⟨33242198411912155528241963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88645862431765748075311901 33242198411912155528241963)
      ·
        refine ⟨49863297617868233292362945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33242198411912155528241963 49863297617868233292362945)
        ·
          refine ⟨37397473213401174969272209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49863297617868233292362945 37397473213401174969272209)
          ·
            refine ⟨28048104910050881226954157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37397473213401174969272209 28048104910050881226954157)
            ·
              refine ⟨10518039341269080460107809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28048104910050881226954157 10518039341269080460107809)
              ·
                refine ⟨7888529505951810345080857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10518039341269080460107809 7888529505951810345080857)
                ·
                  refine ⟨5916397129463857758810643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7888529505951810345080857 5916397129463857758810643)
                  ·
                    refine ⟨8874595694195786638215965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5916397129463857758810643 8874595694195786638215965)
                    ·
                      refine ⟨3327973385323419989330987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8874595694195786638215965 3327973385323419989330987)
                      ·
                        rfl

theorem cell23_6481205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_6481205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481205 prefixEnd_6481205 := by exact prefixLift 6481205
  have htrace : WordTrace (prefixWord ++ tailWord_6481205) baseStart_6481205 baseEnd_6481205 := by
    simpa [prefixWord, tailWord_6481205, baseEnd_6481205] using wordTrace_append hprefix tailTrace_6481205
  have hstable : (prefixWord ++ tailWord_6481205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481205).length < 2 ^ (prefixWord ++ tailWord_6481205).sum := by decide
  have hdescent : baseEnd_6481205 < baseStart_6481205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481301 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_6481301 : Nat := 118140960795 + 6481301 * 2 ^ 59
def prefixEnd_6481301 : Nat := 4983230072969 + 3 ^ 40 * 6481301 * 2
def baseEnd_6481301 : Nat := 3328022679466251613730545

theorem tailTrace_6481301 : CollatzResearch.WordTrace tailWord_6481301 prefixEnd_6481301 3328022679466251613730545 := by
  unfold tailWord_6481301
  simp only [CollatzResearch.WordTrace]
  refine ⟨236392467892360869929659757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157594978594907246619773171 236392467892360869929659757)
  ·
    refine ⟨88647175459635326223622409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236392467892360869929659757 88647175459635326223622409)
    ·
      refine ⟨66485381594726494667716807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88647175459635326223622409 66485381594726494667716807)
      ·
        refine ⟨99728072392089742001575211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66485381594726494667716807 99728072392089742001575211)
        ·
          refine ⟨149592108588134613002362817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99728072392089742001575211 149592108588134613002362817)
          ·
            refine ⟨112194081441100959751772113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149592108588134613002362817 112194081441100959751772113)
            ·
              refine ⟨84145561080825719813829085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112194081441100959751772113 84145561080825719813829085)
              ·
                refine ⟨31554585405309644930185907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84145561080825719813829085 31554585405309644930185907)
                ·
                  refine ⟨47331878107964467395278861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31554585405309644930185907 47331878107964467395278861)
                  ·
                    refine ⟨17749454290486675273229573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47331878107964467395278861 17749454290486675273229573)
                    ·
                      refine ⟨3328022679466251613730545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17749454290486675273229573 3328022679466251613730545)
                      ·
                        rfl

theorem cell23_6481301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_6481301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481301 prefixEnd_6481301 := by exact prefixLift 6481301
  have htrace : WordTrace (prefixWord ++ tailWord_6481301) baseStart_6481301 baseEnd_6481301 := by
    simpa [prefixWord, tailWord_6481301, baseEnd_6481301] using wordTrace_append hprefix tailTrace_6481301
  have hstable : (prefixWord ++ tailWord_6481301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481301).length < 2 ^ (prefixWord ++ tailWord_6481301).sum := by decide
  have hdescent : baseEnd_6481301 < baseStart_6481301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481321 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 5, 4, 3]
def baseStart_6481321 : Nat := 118140960795 + 6481321 * 2 ^ 59
def prefixEnd_6481321 : Nat := 4983230072969 + 3 ^ 40 * 6481321 * 2
def baseEnd_6481321 : Nat := 3328032949079341535480453

theorem tailTrace_6481321 : CollatzResearch.WordTrace tailWord_6481321 prefixEnd_6481321 3328032949079341535480453 := by
  unfold tailWord_6481321
  simp only [CollatzResearch.WordTrace]
  refine ⟨236393197352288413345387817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157595464901525608896925211 236393197352288413345387817)
  ·
    refine ⟨177294898014216310009040863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236393197352288413345387817 177294898014216310009040863)
    ·
      refine ⟨265942347021324465013561295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177294898014216310009040863 265942347021324465013561295)
      ·
        refine ⟨398913520531986697520341943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265942347021324465013561295 398913520531986697520341943)
        ·
          refine ⟨598370280797980046280512915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398913520531986697520341943 598370280797980046280512915)
          ·
            refine ⟨897555421196970069420769373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598370280797980046280512915 897555421196970069420769373)
            ·
              refine ⟨336583282948863776032788515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 897555421196970069420769373 336583282948863776032788515)
              ·
                refine ⟨504874924423295664049182773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336583282948863776032788515 504874924423295664049182773)
                ·
                  refine ⟨47332024164683968504610885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 504874924423295664049182773 47332024164683968504610885)
                  ·
                    refine ⟨8874754530878244094614541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47332024164683968504610885 8874754530878244094614541)
                    ·
                      refine ⟨3328032949079341535480453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8874754530878244094614541 3328032949079341535480453)
                      ·
                        rfl

theorem cell23_6481321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 4, 3].length) (baseStart_6481321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481321 prefixEnd_6481321 := by exact prefixLift 6481321
  have htrace : WordTrace (prefixWord ++ tailWord_6481321) baseStart_6481321 baseEnd_6481321 := by
    simpa [prefixWord, tailWord_6481321, baseEnd_6481321] using wordTrace_append hprefix tailTrace_6481321
  have hstable : (prefixWord ++ tailWord_6481321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481321).length < 2 ^ (prefixWord ++ tailWord_6481321).sum := by decide
  have hdescent : baseEnd_6481321 < baseStart_6481321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481405 : List Nat := [1, 4, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_6481405 : Nat := 118140960795 + 6481405 * 2 ^ 59
def prefixEnd_6481405 : Nat := 4983230072969 + 3 ^ 40 * 6481405 * 2
def baseEnd_6481405 : Nat := 1109358693818106402276689

theorem tailTrace_6481405 : CollatzResearch.WordTrace tailWord_6481405 prefixEnd_6481405 1109358693818106402276689 := by
  unfold tailWord_6481405
  simp only [CollatzResearch.WordTrace]
  refine ⟨236396261083984095691445669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157597507389322730460963779 236396261083984095691445669)
  ·
    refine ⟨44324298953247017942146063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236396261083984095691445669 44324298953247017942146063)
    ·
      refine ⟨66486448429870526913219095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44324298953247017942146063 66486448429870526913219095)
      ·
        refine ⟨99729672644805790369828643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66486448429870526913219095 99729672644805790369828643)
        ·
          refine ⟨149594508967208685554742965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99729672644805790369828643 149594508967208685554742965)
          ·
            refine ⟨14024485215675814270757153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149594508967208685554742965 14024485215675814270757153)
            ·
              refine ⟨10518363911756860703067865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14024485215675814270757153 10518363911756860703067865)
              ·
                refine ⟨7888772933817645527300899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10518363911756860703067865 7888772933817645527300899)
                ·
                  refine ⟨11833159400726468290951349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7888772933817645527300899 11833159400726468290951349)
                  ·
                    refine ⟨1109358693818106402276689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11833159400726468290951349 1109358693818106402276689)
                    ·
                      rfl

theorem cell23_6481405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_6481405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481405 prefixEnd_6481405 := by exact prefixLift 6481405
  have htrace : WordTrace (prefixWord ++ tailWord_6481405) baseStart_6481405 baseEnd_6481405 := by
    simpa [prefixWord, tailWord_6481405, baseEnd_6481405] using wordTrace_append hprefix tailTrace_6481405
  have hstable : (prefixWord ++ tailWord_6481405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481405).length < 2 ^ (prefixWord ++ tailWord_6481405).sum := by decide
  have hdescent : baseEnd_6481405 < baseStart_6481405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481479 : List Nat := [1, 1, 4, 1, 5, 1, 3, 1, 1, 2, 3]
def baseStart_6481479 : Nat := 118140960795 + 6481479 * 2 ^ 59
def prefixEnd_6481479 : Nat := 4983230072969 + 3 ^ 40 * 6481479 * 2
def baseEnd_6481479 : Nat := 3328114079022751917304727

theorem tailTrace_6481479 : CollatzResearch.WordTrace tailWord_6481479 prefixEnd_6481479 3328114079022751917304727 := by
  unfold tailWord_6481479
  simp only [CollatzResearch.WordTrace]
  refine ⟨236398960085716006329639491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157599306723810670886426327 236398960085716006329639491)
  ·
    refine ⟨354598440128574009494459237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236398960085716006329639491 354598440128574009494459237)
    ·
      refine ⟨66487207524107626780211107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354598440128574009494459237 66487207524107626780211107)
      ·
        refine ⟨99730811286161440170316661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66487207524107626780211107 99730811286161440170316661)
        ·
          refine ⟨9349763558077635015967187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99730811286161440170316661 9349763558077635015967187)
          ·
            refine ⟨14024645337116452523950781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9349763558077635015967187 14024645337116452523950781)
            ·
              refine ⟨5259242001418669696481543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14024645337116452523950781 5259242001418669696481543)
              ·
                refine ⟨7888863002128004544722315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5259242001418669696481543 7888863002128004544722315)
                ·
                  refine ⟨11833294503192006817083473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7888863002128004544722315 11833294503192006817083473)
                  ·
                    refine ⟨8874970877394005112812605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11833294503192006817083473 8874970877394005112812605)
                    ·
                      refine ⟨3328114079022751917304727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8874970877394005112812605 3328114079022751917304727)
                      ·
                        rfl

theorem cell23_6481479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_6481479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481479 prefixEnd_6481479 := by exact prefixLift 6481479
  have htrace : WordTrace (prefixWord ++ tailWord_6481479) baseStart_6481479 baseEnd_6481479 := by
    simpa [prefixWord, tailWord_6481479, baseEnd_6481479] using wordTrace_append hprefix tailTrace_6481479
  have hstable : (prefixWord ++ tailWord_6481479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481479).length < 2 ^ (prefixWord ++ tailWord_6481479).sum := by decide
  have hdescent : baseEnd_6481479 < baseStart_6481479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481508 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_6481508 : Nat := 118140960795 + 6481508 * 2 ^ 59
def prefixEnd_6481508 : Nat := 4983230072969 + 3 ^ 40 * 6481508 * 2
def baseEnd_6481508 : Nat := 1109376323320577434614031

theorem tailTrace_6481508 : CollatzResearch.WordTrace tailWord_6481508 prefixEnd_6481508 1109376323320577434614031 := by
  unfold tailWord_6481508
  simp only [CollatzResearch.WordTrace]
  refine ⟨118200008901305472141222589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157600011868407296188296785 118200008901305472141222589)
  ·
    refine ⟨44325003337989552052958471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118200008901305472141222589 44325003337989552052958471)
    ·
      refine ⟨66487505006984328079437707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44325003337989552052958471 66487505006984328079437707)
      ·
        refine ⟨99731257510476492119156561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66487505006984328079437707 99731257510476492119156561)
        ·
          refine ⟨74798443132857369089367421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99731257510476492119156561 74798443132857369089367421)
          ·
            refine ⟨28049416174821513408512783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74798443132857369089367421 28049416174821513408512783)
            ·
              refine ⟨42074124262232270112769175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28049416174821513408512783 42074124262232270112769175)
              ·
                refine ⟨63111186393348405169153763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42074124262232270112769175 63111186393348405169153763)
                ·
                  refine ⟨94666779590022607753730645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63111186393348405169153763 94666779590022607753730645)
                  ·
                    refine ⟨1109376323320577434614031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94666779590022607753730645 1109376323320577434614031)
                    ·
                      rfl

theorem cell23_6481508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_6481508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481508 prefixEnd_6481508 := by exact prefixLift 6481508
  have htrace : WordTrace (prefixWord ++ tailWord_6481508) baseStart_6481508 baseEnd_6481508 := by
    simpa [prefixWord, tailWord_6481508, baseEnd_6481508] using wordTrace_append hprefix tailTrace_6481508
  have hstable : (prefixWord ++ tailWord_6481508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481508).length < 2 ^ (prefixWord ++ tailWord_6481508).sum := by decide
  have hdescent : baseEnd_6481508 < baseStart_6481508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481528 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_6481528 : Nat := 118140960795 + 6481528 * 2 ^ 59
def prefixEnd_6481528 : Nat := 4983230072969 + 3 ^ 40 * 6481528 * 2
def baseEnd_6481528 : Nat := 3328139239574822225592001

theorem tailTrace_6481528 : CollatzResearch.WordTrace tailWord_6481528 prefixEnd_6481528 3328139239574822225592001 := by
  unfold tailWord_6481528
  simp only [CollatzResearch.WordTrace]
  refine ⟨118200373631269243849086619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157600498175025658465448825 118200373631269243849086619)
  ·
    refine ⟨177300560446903865773629929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118200373631269243849086619 177300560446903865773629929)
    ·
      refine ⟨132975420335177899330222447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177300560446903865773629929 132975420335177899330222447)
      ·
        refine ⟨199463130502766848995333671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132975420335177899330222447 199463130502766848995333671)
        ·
          refine ⟨299194695754150273493000507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199463130502766848995333671 299194695754150273493000507)
          ·
            refine ⟨448792043631225410239500761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299194695754150273493000507 448792043631225410239500761)
            ·
              refine ⟨336594032723419057679625571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448792043631225410239500761 336594032723419057679625571)
              ·
                refine ⟨504891049085128586519438357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336594032723419057679625571 504891049085128586519438357)
                ·
                  refine ⟨23666767925865402493098673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 504891049085128586519438357 23666767925865402493098673)
                  ·
                    refine ⟨17750075944399051869824005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23666767925865402493098673 17750075944399051869824005)
                    ·
                      refine ⟨3328139239574822225592001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17750075944399051869824005 3328139239574822225592001)
                      ·
                        rfl

theorem cell23_6481528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_6481528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481528 prefixEnd_6481528 := by exact prefixLift 6481528
  have htrace : WordTrace (prefixWord ++ tailWord_6481528) baseStart_6481528 baseEnd_6481528 := by
    simpa [prefixWord, tailWord_6481528, baseEnd_6481528] using wordTrace_append hprefix tailTrace_6481528
  have hstable : (prefixWord ++ tailWord_6481528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481528).length < 2 ^ (prefixWord ++ tailWord_6481528).sum := by decide
  have hdescent : baseEnd_6481528 < baseStart_6481528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481532 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 4, 2, 2]
def baseStart_6481532 : Nat := 118140960795 + 6481532 * 2 ^ 59
def prefixEnd_6481532 : Nat := 4983230072969 + 3 ^ 40 * 6481532 * 2
def baseEnd_6481532 : Nat := 3328141293497440209941983

theorem tailTrace_6481532 : CollatzResearch.WordTrace tailWord_6481532 prefixEnd_6481532 3328141293497440209941983 := by
  unfold tailWord_6481532
  simp only [CollatzResearch.WordTrace]
  refine ⟨118200446577261998190659425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157600595436349330920879233 118200446577261998190659425)
  ·
    refine ⟨88650334932946498642994569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118200446577261998190659425 88650334932946498642994569)
    ·
      refine ⟨66487751199709873982245927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88650334932946498642994569 66487751199709873982245927)
      ·
        refine ⟨99731626799564810973368891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66487751199709873982245927 99731626799564810973368891)
        ·
          refine ⟨149597440199347216460053337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99731626799564810973368891 149597440199347216460053337)
          ·
            refine ⟨112198080149510412345040003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149597440199347216460053337 112198080149510412345040003)
            ·
              refine ⟨168297120224265618517560005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112198080149510412345040003 168297120224265618517560005)
              ·
                refine ⟨31555710042049803472042501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168297120224265618517560005 31555710042049803472042501)
                ·
                  refine ⟨5916695632884338151007969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31555710042049803472042501 5916695632884338151007969)
                  ·
                    refine ⟨4437521724663253613255977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5916695632884338151007969 4437521724663253613255977)
                    ·
                      refine ⟨3328141293497440209941983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4437521724663253613255977 3328141293497440209941983)
                      ·
                        rfl

theorem cell23_6481532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_6481532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481532 prefixEnd_6481532 := by exact prefixLift 6481532
  have htrace : WordTrace (prefixWord ++ tailWord_6481532) baseStart_6481532 baseEnd_6481532 := by
    simpa [prefixWord, tailWord_6481532, baseEnd_6481532] using wordTrace_append hprefix tailTrace_6481532
  have hstable : (prefixWord ++ tailWord_6481532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481532).length < 2 ^ (prefixWord ++ tailWord_6481532).sum := by decide
  have hdescent : baseEnd_6481532 < baseStart_6481532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481566 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_6481566 : Nat := 118140960795 + 6481566 * 2 ^ 59
def prefixEnd_6481566 : Nat := 4983230072969 + 3 ^ 40 * 6481566 * 2
def baseEnd_6481566 : Nat := 3328158751839693076916827

theorem tailTrace_6481566 : CollatzResearch.WordTrace tailWord_6481566 prefixEnd_6481566 3328158751839693076916827 := by
  unfold tailWord_6481566
  simp only [CollatzResearch.WordTrace]
  refine ⟨29550266654550102523507069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157601422157600546792037701 29550266654550102523507069)
  ·
    refine ⟨11081349995456288446315151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29550266654550102523507069 11081349995456288446315151)
    ·
      refine ⟨16622024993184432669472727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11081349995456288446315151 16622024993184432669472727)
      ·
        refine ⟨24933037489776649004209091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16622024993184432669472727 24933037489776649004209091)
        ·
          refine ⟨37399556234664973506313637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24933037489776649004209091 37399556234664973506313637)
          ·
            refine ⟨7012416793999682532433807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37399556234664973506313637 7012416793999682532433807)
            ·
              refine ⟨10518625190999523798650711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7012416793999682532433807 10518625190999523798650711)
              ·
                refine ⟨15777937786499285697976067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10518625190999523798650711 15777937786499285697976067)
                ·
                  refine ⟨23666906679748928546964101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15777937786499285697976067 23666906679748928546964101)
                  ·
                    refine ⟨4437545002452924102555769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23666906679748928546964101 4437545002452924102555769)
                    ·
                      refine ⟨3328158751839693076916827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4437545002452924102555769 3328158751839693076916827)
                      ·
                        rfl

theorem cell23_6481566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_6481566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481566 prefixEnd_6481566 := by exact prefixLift 6481566
  have htrace : WordTrace (prefixWord ++ tailWord_6481566) baseStart_6481566 baseEnd_6481566 := by
    simpa [prefixWord, tailWord_6481566, baseEnd_6481566] using wordTrace_append hprefix tailTrace_6481566
  have hstable : (prefixWord ++ tailWord_6481566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481566).length < 2 ^ (prefixWord ++ tailWord_6481566).sum := by decide
  have hdescent : baseEnd_6481566 < baseStart_6481566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481605 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_6481605 : Nat := 118140960795 + 6481605 * 2 ^ 59
def prefixEnd_6481605 : Nat := 4983230072969 + 3 ^ 40 * 6481605 * 2
def baseEnd_6481605 : Nat := 3328178777585218424329147

theorem tailTrace_6481605 : CollatzResearch.WordTrace tailWord_6481605 prefixEnd_6481605 3328178777585218424329147 := by
  unfold tailWord_6481605
  simp only [CollatzResearch.WordTrace]
  refine ⟨236403555683259529848726269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157602370455506353232484179 236403555683259529848726269)
  ·
    refine ⟨88651333381222323693272351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236403555683259529848726269 88651333381222323693272351)
    ·
      refine ⟨132977000071833485539908527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88651333381222323693272351 132977000071833485539908527)
      ·
        refine ⟨199465500107750228309862791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132977000071833485539908527 199465500107750228309862791)
        ·
          refine ⟨299198250161625342464794187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199465500107750228309862791 299198250161625342464794187)
          ·
            refine ⟨448797375242438013697191281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299198250161625342464794187 448797375242438013697191281)
            ·
              refine ⟨336598031431828510272893461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448797375242438013697191281 336598031431828510272893461)
              ·
                refine ⟨15778032723366961419041881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 336598031431828510272893461 15778032723366961419041881)
                ·
                  refine ⟨11833524542525221064281411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15778032723366961419041881 11833524542525221064281411)
                  ·
                    refine ⟨17750286813787831596422117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11833524542525221064281411 17750286813787831596422117)
                    ·
                      refine ⟨3328178777585218424329147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17750286813787831596422117 3328178777585218424329147)
                      ·
                        rfl

theorem cell23_6481605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_6481605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481605 prefixEnd_6481605 := by exact prefixLift 6481605
  have htrace : WordTrace (prefixWord ++ tailWord_6481605) baseStart_6481605 baseEnd_6481605 := by
    simpa [prefixWord, tailWord_6481605, baseEnd_6481605] using wordTrace_append hprefix tailTrace_6481605
  have hstable : (prefixWord ++ tailWord_6481605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481605).length < 2 ^ (prefixWord ++ tailWord_6481605).sum := by decide
  have hdescent : baseEnd_6481605 < baseStart_6481605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481606 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_6481606 : Nat := 118140960795 + 6481606 * 2 ^ 59
def prefixEnd_6481606 : Nat := 4983230072969 + 3 ^ 40 * 6481606 * 2
def baseEnd_6481606 : Nat := 369797699007319213379627

theorem tailTrace_6481606 : CollatzResearch.WordTrace tailWord_6481606 prefixEnd_6481606 369797699007319213379627 := by
  unfold tailWord_6481606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7387612254882997094359771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157602394770837271346341781 7387612254882997094359771)
  ·
    refine ⟨11081418382324495641539657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7387612254882997094359771 11081418382324495641539657)
    ·
      refine ⟨8311063786743371731154743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11081418382324495641539657 8311063786743371731154743)
      ·
        refine ⟨12466595680115057596732115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8311063786743371731154743 12466595680115057596732115)
        ·
          refine ⟨18699893520172586395098173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12466595680115057596732115 18699893520172586395098173)
          ·
            refine ⟨7012460070064719898161815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18699893520172586395098173 7012460070064719898161815)
            ·
              refine ⟨10518690105097079847242723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7012460070064719898161815 10518690105097079847242723)
              ·
                refine ⟨15778035157645619770864085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10518690105097079847242723 15778035157645619770864085)
                ·
                  refine ⟨369797699007319213379627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15778035157645619770864085 369797699007319213379627)
                  ·
                    rfl

theorem cell23_6481606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_6481606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481606 prefixEnd_6481606 := by exact prefixLift 6481606
  have htrace : WordTrace (prefixWord ++ tailWord_6481606) baseStart_6481606 baseEnd_6481606 := by
    simpa [prefixWord, tailWord_6481606, baseEnd_6481606] using wordTrace_append hprefix tailTrace_6481606
  have hstable : (prefixWord ++ tailWord_6481606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481606).length < 2 ^ (prefixWord ++ tailWord_6481606).sum := by decide
  have hdescent : baseEnd_6481606 < baseStart_6481606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481612 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 1, 2, 5]
def baseStart_6481612 : Nat := 118140960795 + 6481612 * 2 ^ 59
def prefixEnd_6481612 : Nat := 4983230072969 + 3 ^ 40 * 6481612 * 2
def baseEnd_6481612 : Nat := 3328182371949799896941615

theorem tailTrace_6481612 : CollatzResearch.WordTrace tailWord_6481612 prefixEnd_6481612 3328182371949799896941615 := by
  unfold tailWord_6481612
  simp only [CollatzResearch.WordTrace]
  refine ⟨118201905497117085022115545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157602540662822780029487393 118201905497117085022115545)
  ·
    refine ⟨88651429122837813766586659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118201905497117085022115545 88651429122837813766586659)
    ·
      refine ⟨132977143684256720649879989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88651429122837813766586659 132977143684256720649879989)
      ·
        refine ⟨12466607220399067560926249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132977143684256720649879989 12466607220399067560926249)
        ·
          refine ⟨9349955415299300670694687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12466607220399067560926249 9349955415299300670694687)
          ·
            refine ⟨14024933122948951006042031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9349955415299300670694687 14024933122948951006042031)
            ·
              refine ⟨21037399684423426509063047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14024933122948951006042031 21037399684423426509063047)
              ·
                refine ⟨31556099526635139763594571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21037399684423426509063047 31556099526635139763594571)
                ·
                  refine ⟨47334149289952709645391857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31556099526635139763594571 47334149289952709645391857)
                  ·
                    refine ⟨35500611967464532234043893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47334149289952709645391857 35500611967464532234043893)
                    ·
                      refine ⟨3328182371949799896941615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35500611967464532234043893 3328182371949799896941615)
                      ·
                        rfl

theorem cell23_6481612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_6481612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481612 prefixEnd_6481612 := by exact prefixLift 6481612
  have htrace : WordTrace (prefixWord ++ tailWord_6481612) baseStart_6481612 baseEnd_6481612 := by
    simpa [prefixWord, tailWord_6481612, baseEnd_6481612] using wordTrace_append hprefix tailTrace_6481612
  have hstable : (prefixWord ++ tailWord_6481612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481612).length < 2 ^ (prefixWord ++ tailWord_6481612).sum := by decide
  have hdescent : baseEnd_6481612 < baseStart_6481612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481642 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_6481642 : Nat := 118140960795 + 6481642 * 2 ^ 59
def prefixEnd_6481642 : Nat := 4983230072969 + 3 ^ 40 * 6481642 * 2
def baseEnd_6481642 : Nat := 3328197776369434779566477

theorem tailTrace_6481642 : CollatzResearch.WordTrace tailWord_6481642 prefixEnd_6481642 3328197776369434779566477 := by
  unfold tailWord_6481642
  simp only [CollatzResearch.WordTrace]
  refine ⟨59101226296031371291955795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157603270122750323445215453 59101226296031371291955795)
  ·
    refine ⟨88651839444047056937933693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59101226296031371291955795 88651839444047056937933693)
    ·
      refine ⟨33244439791517646351725135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88651839444047056937933693 33244439791517646351725135)
      ·
        refine ⟨49866659687276469527587703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33244439791517646351725135 49866659687276469527587703)
        ·
          refine ⟨74799989530914704291381555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49866659687276469527587703 74799989530914704291381555)
          ·
            refine ⟨112199984296372056437072333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74799989530914704291381555 112199984296372056437072333)
            ·
              refine ⟨42074994111139521163902125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112199984296372056437072333 42074994111139521163902125)
              ·
                refine ⟨15778122791677320436463297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42074994111139521163902125 15778122791677320436463297)
                ·
                  refine ⟨11833592093757990327347473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15778122791677320436463297 11833592093757990327347473)
                  ·
                    refine ⟨8875194070318492745510605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11833592093757990327347473 8875194070318492745510605)
                    ·
                      refine ⟨3328197776369434779566477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8875194070318492745510605 3328197776369434779566477)
                      ·
                        rfl

theorem cell23_6481642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_6481642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481642 prefixEnd_6481642 := by exact prefixLift 6481642
  have htrace : WordTrace (prefixWord ++ tailWord_6481642) baseStart_6481642 baseEnd_6481642 := by
    simpa [prefixWord, tailWord_6481642, baseEnd_6481642] using wordTrace_append hprefix tailTrace_6481642
  have hstable : (prefixWord ++ tailWord_6481642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481642).length < 2 ^ (prefixWord ++ tailWord_6481642).sum := by decide
  have hdescent : baseEnd_6481642 < baseStart_6481642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481666 : List Nat := [3, 4, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_6481666 : Nat := 118140960795 + 6481666 * 2 ^ 59
def prefixEnd_6481666 : Nat := 4983230072969 + 3 ^ 40 * 6481666 * 2
def baseEnd_6481666 : Nat := 1109403366635047561888789

theorem tailTrace_6481666 : CollatzResearch.WordTrace tailWord_6481666 prefixEnd_6481666 1109403366635047561888789 := by
  unfold tailWord_6481666
  simp only [CollatzResearch.WordTrace]
  refine ⟨59101445134009634316674213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157603853690692358177797901 59101445134009634316674213)
  ·
    refine ⟨11081520962626806434376415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59101445134009634316674213 11081520962626806434376415)
    ·
      refine ⟨16622281443940209651564623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11081520962626806434376415 16622281443940209651564623)
      ·
        refine ⟨24933422165910314477346935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16622281443940209651564623 24933422165910314477346935)
        ·
          refine ⟨37400133248865471716020403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24933422165910314477346935 37400133248865471716020403)
          ·
            refine ⟨56100199873298207574030605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37400133248865471716020403 56100199873298207574030605)
            ·
              refine ⟨21037574952486827840261477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56100199873298207574030605 21037574952486827840261477)
              ·
                refine ⟨3944545303591280220049027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21037574952486827840261477 3944545303591280220049027)
                ·
                  refine ⟨5916817955386920330073541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3944545303591280220049027 5916817955386920330073541)
                  ·
                    refine ⟨1109403366635047561888789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5916817955386920330073541 1109403366635047561888789)
                    ·
                      rfl

theorem cell23_6481666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_6481666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481666 prefixEnd_6481666 := by exact prefixLift 6481666
  have htrace : WordTrace (prefixWord ++ tailWord_6481666) baseStart_6481666 baseEnd_6481666 := by
    simpa [prefixWord, tailWord_6481666, baseEnd_6481666] using wordTrace_append hprefix tailTrace_6481666
  have hstable : (prefixWord ++ tailWord_6481666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481666).length < 2 ^ (prefixWord ++ tailWord_6481666).sum := by decide
  have hdescent : baseEnd_6481666 < baseStart_6481666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481675 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 3, 5]
def baseStart_6481675 : Nat := 118140960795 + 6481675 * 2 ^ 59
def prefixEnd_6481675 : Nat := 4983230072969 + 3 ^ 40 * 6481675 * 2
def baseEnd_6481675 : Nat := 1109404907077011050151275

theorem tailTrace_6481675 : CollatzResearch.WordTrace tailWord_6481675 prefixEnd_6481675 1109404907077011050151275 := by
  unfold tailWord_6481675
  simp only [CollatzResearch.WordTrace]
  refine ⟨236406108793005931803774479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157604072528670621202516319 236406108793005931803774479)
  ·
    refine ⟨354609163189508897705661719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236406108793005931803774479 354609163189508897705661719)
    ·
      refine ⟨531913744784263346558492579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354609163189508897705661719 531913744784263346558492579)
      ·
        refine ⟨797870617176395019837738869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531913744784263346558492579 797870617176395019837738869)
        ·
          refine ⟨74800370360287033109788019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 797870617176395019837738869 74800370360287033109788019)
          ·
            refine ⟨112200555540430549664682029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74800370360287033109788019 112200555540430549664682029)
            ·
              refine ⟨42075208327661456124255761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112200555540430549664682029 42075208327661456124255761)
              ·
                refine ⟨31556406245746092093191821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42075208327661456124255761 31556406245746092093191821)
                ·
                  refine ⟨11833652342154784534946933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31556406245746092093191821 11833652342154784534946933)
                  ·
                    refine ⟨1109404907077011050151275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11833652342154784534946933 1109404907077011050151275)
                    ·
                      rfl

theorem cell23_6481675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 5].length) (baseStart_6481675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481675 prefixEnd_6481675 := by exact prefixLift 6481675
  have htrace : WordTrace (prefixWord ++ tailWord_6481675) baseStart_6481675 baseEnd_6481675 := by
    simpa [prefixWord, tailWord_6481675, baseEnd_6481675] using wordTrace_append hprefix tailTrace_6481675
  have hstable : (prefixWord ++ tailWord_6481675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481675).length < 2 ^ (prefixWord ++ tailWord_6481675).sum := by decide
  have hdescent : baseEnd_6481675 < baseStart_6481675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481692 : List Nat := [2, 2, 3, 1, 1, 2, 2, 4, 1, 5]
def baseStart_6481692 : Nat := 118140960795 + 6481692 * 2 ^ 59
def prefixEnd_6481692 : Nat := 4983230072969 + 3 ^ 40 * 6481692 * 2
def baseEnd_6481692 : Nat := 1109407816800719861313749

theorem tailTrace_6481692 : CollatzResearch.WordTrace tailWord_6481692 prefixEnd_6481692 1109407816800719861313749 := by
  unfold tailWord_6481692
  simp only [CollatzResearch.WordTrace]
  refine ⟨118203364416972171853571665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157604485889296229138095553 118203364416972171853571665)
  ·
    refine ⟨88652523312729128890178749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118203364416972171853571665 88652523312729128890178749)
    ·
      refine ⟨33244696242273423333817031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88652523312729128890178749 33244696242273423333817031)
      ·
        refine ⟨49867044363410135000725547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33244696242273423333817031 49867044363410135000725547)
        ·
          refine ⟨74800566545115202501088321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49867044363410135000725547 74800566545115202501088321)
          ·
            refine ⟨56100424908836401875816241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74800566545115202501088321 56100424908836401875816241)
            ·
              refine ⟨42075318681627301406862181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56100424908836401875816241 42075318681627301406862181)
              ·
                refine ⟨7889122252805119013786659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42075318681627301406862181 7889122252805119013786659)
                ·
                  refine ⟨11833683379207678520679989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7889122252805119013786659 11833683379207678520679989)
                  ·
                    refine ⟨1109407816800719861313749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11833683379207678520679989 1109407816800719861313749)
                    ·
                      rfl

theorem cell23_6481692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_6481692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481692 prefixEnd_6481692 := by exact prefixLift 6481692
  have htrace : WordTrace (prefixWord ++ tailWord_6481692) baseStart_6481692 baseEnd_6481692 := by
    simpa [prefixWord, tailWord_6481692, baseEnd_6481692] using wordTrace_append hprefix tailTrace_6481692
  have hstable : (prefixWord ++ tailWord_6481692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481692).length < 2 ^ (prefixWord ++ tailWord_6481692).sum := by decide
  have hdescent : baseEnd_6481692 < baseStart_6481692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481699 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 2, 3, 2]
def baseStart_6481699 : Nat := 118140960795 + 6481699 * 2 ^ 59
def prefixEnd_6481699 : Nat := 4983230072969 + 3 ^ 40 * 6481699 * 2
def baseEnd_6481699 : Nat := 3328227044766741056553715

theorem tailTrace_6481699 : CollatzResearch.WordTrace tailWord_6481699 prefixEnd_6481699 3328227044766741056553715 := by
  unfold tailWord_6481699
  simp only [CollatzResearch.WordTrace]
  refine ⟨236406984144918983902648151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157604656096612655935098767 236406984144918983902648151)
  ·
    refine ⟨354610476217378475853972227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236406984144918983902648151 354610476217378475853972227)
    ·
      refine ⟨531915714326067713780958341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354610476217378475853972227 531915714326067713780958341)
      ·
        refine ⟨99734196436137696333929689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 531915714326067713780958341 99734196436137696333929689)
        ·
          refine ⟨74800647327103272250447267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99734196436137696333929689 74800647327103272250447267)
          ·
            refine ⟨112200970990654908375670901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74800647327103272250447267 112200970990654908375670901)
            ·
              refine ⟨10518841030373897660219147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112200970990654908375670901 10518841030373897660219147)
              ·
                refine ⟨15778261545560846490328721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10518841030373897660219147 15778261545560846490328721)
                ·
                  refine ⟨11833696159170634867746541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15778261545560846490328721 11833696159170634867746541)
                  ·
                    refine ⟨4437636059688988075404953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11833696159170634867746541 4437636059688988075404953)
                    ·
                      refine ⟨3328227044766741056553715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4437636059688988075404953 3328227044766741056553715)
                      ·
                        rfl

theorem cell23_6481699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_6481699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481699 prefixEnd_6481699 := by exact prefixLift 6481699
  have htrace : WordTrace (prefixWord ++ tailWord_6481699) baseStart_6481699 baseEnd_6481699 := by
    simpa [prefixWord, tailWord_6481699, baseEnd_6481699] using wordTrace_append hprefix tailTrace_6481699
  have hstable : (prefixWord ++ tailWord_6481699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481699).length < 2 ^ (prefixWord ++ tailWord_6481699).sum := by decide
  have hdescent : baseEnd_6481699 < baseStart_6481699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481746 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_6481746 : Nat := 118140960795 + 6481746 * 2 ^ 59
def prefixEnd_6481746 : Nat := 4983230072969 + 3 ^ 40 * 6481746 * 2
def baseEnd_6481746 : Nat := 3328251178357502372665999

theorem tailTrace_6481746 : CollatzResearch.WordTrace tailWord_6481746 prefixEnd_6481746 3328251178357502372665999 := by
  unfold tailWord_6481746
  simp only [CollatzResearch.WordTrace]
  refine ⟨59102174593937177732402273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157605798917165807286406061 59102174593937177732402273)
  ·
    refine ⟨44326630945452883299301705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59102174593937177732402273 44326630945452883299301705)
    ·
      refine ⟨33244973209089662474476279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44326630945452883299301705 33244973209089662474476279)
      ·
        refine ⟨49867459813634493711714419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33244973209089662474476279 49867459813634493711714419)
        ·
          refine ⟨74801189720451740567571629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49867459813634493711714419 74801189720451740567571629)
          ·
            refine ⟨28050446145169402712839361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74801189720451740567571629 28050446145169402712839361)
            ·
              refine ⟨21037834608877052034629521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28050446145169402712839361 21037834608877052034629521)
              ·
                refine ⟨15778375956657789025972141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21037834608877052034629521 15778375956657789025972141)
                ·
                  refine ⟨5916890983746670884739553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15778375956657789025972141 5916890983746670884739553)
                  ·
                    refine ⟨4437668237810003163554665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5916890983746670884739553 4437668237810003163554665)
                    ·
                      refine ⟨3328251178357502372665999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4437668237810003163554665 3328251178357502372665999)
                      ·
                        rfl

theorem cell23_6481746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_6481746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481746 prefixEnd_6481746 := by exact prefixLift 6481746
  have htrace : WordTrace (prefixWord ++ tailWord_6481746) baseStart_6481746 baseEnd_6481746 := by
    simpa [prefixWord, tailWord_6481746, baseEnd_6481746] using wordTrace_append hprefix tailTrace_6481746
  have hstable : (prefixWord ++ tailWord_6481746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481746).length < 2 ^ (prefixWord ++ tailWord_6481746).sum := by decide
  have hdescent : baseEnd_6481746 < baseStart_6481746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481749 : List Nat := [1, 3, 2, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_6481749 : Nat := 118140960795 + 6481749 * 2 ^ 59
def prefixEnd_6481749 : Nat := 4983230072969 + 3 ^ 40 * 6481749 * 2
def baseEnd_6481749 : Nat := 3328252718799465860928485

theorem tailTrace_6481749 : CollatzResearch.WordTrace tailWord_6481749 prefixEnd_6481749 3328252718799465860928485 := by
  unfold tailWord_6481749
  simp only [CollatzResearch.WordTrace]
  refine ⟨236408807794737842441968301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157605871863158561627978867 236408807794737842441968301)
  ·
    refine ⟨88653302923026690915738113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236408807794737842441968301 88653302923026690915738113)
    ·
      refine ⟨66489977192270018186803585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88653302923026690915738113 66489977192270018186803585)
      ·
        refine ⟨49867482894202513640102689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66489977192270018186803585 49867482894202513640102689)
        ·
          refine ⟨37400612170651885230077017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49867482894202513640102689 37400612170651885230077017)
          ·
            refine ⟨28050459127988913922557763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37400612170651885230077017 28050459127988913922557763)
            ·
              refine ⟨42075688691983370883836645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28050459127988913922557763 42075688691983370883836645)
              ·
                refine ⟨7889191629746882040719371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42075688691983370883836645 7889191629746882040719371)
                ·
                  refine ⟨11833787444620323061079057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7889191629746882040719371 11833787444620323061079057)
                  ·
                    refine ⟨8875340583465242295809293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11833787444620323061079057 8875340583465242295809293)
                    ·
                      refine ⟨3328252718799465860928485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8875340583465242295809293 3328252718799465860928485)
                      ·
                        rfl

theorem cell23_6481749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_6481749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481749 prefixEnd_6481749 := by exact prefixLift 6481749
  have htrace : WordTrace (prefixWord ++ tailWord_6481749) baseStart_6481749 baseEnd_6481749 := by
    simpa [prefixWord, tailWord_6481749, baseEnd_6481749] using wordTrace_append hprefix tailTrace_6481749
  have hstable : (prefixWord ++ tailWord_6481749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481749).length < 2 ^ (prefixWord ++ tailWord_6481749).sum := by decide
  have hdescent : baseEnd_6481749 < baseStart_6481749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481765 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 1, 9]
def baseStart_6481765 : Nat := 118140960795 + 6481765 * 2 ^ 59
def prefixEnd_6481765 : Nat := 4983230072969 + 3 ^ 40 * 6481765 * 2
def baseEnd_6481765 : Nat := 1109420311496645932776137

theorem tailTrace_6481765 : CollatzResearch.WordTrace tailWord_6481765 prefixEnd_6481765 1109420311496645932776137 := by
  unfold tailWord_6481765
  simp only [CollatzResearch.WordTrace]
  refine ⟨236409391362679877174550749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157606260908453251449700499 236409391362679877174550749)
  ·
    refine ⟨88653521761004953940456531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236409391362679877174550749 88653521761004953940456531)
    ·
      refine ⟨132980282641507430910684797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88653521761004953940456531 132980282641507430910684797)
      ·
        refine ⟨49867605990565286591506799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132980282641507430910684797 49867605990565286591506799)
        ·
          refine ⟨74801408985847929887260199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49867605990565286591506799 74801408985847929887260199)
          ·
            refine ⟨112202113478771894830890299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74801408985847929887260199 112202113478771894830890299)
            ·
              refine ⟨168303170218157842246335449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112202113478771894830890299 168303170218157842246335449)
              ·
                refine ⟨126227377663618381684751587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168303170218157842246335449 126227377663618381684751587)
                ·
                  refine ⟨189341066495427572527127381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126227377663618381684751587 189341066495427572527127381)
                  ·
                    refine ⟨1109420311496645932776137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 189341066495427572527127381 1109420311496645932776137)
                    ·
                      rfl

theorem cell23_6481765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_6481765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481765 prefixEnd_6481765 := by exact prefixLift 6481765
  have htrace : WordTrace (prefixWord ++ tailWord_6481765) baseStart_6481765 baseEnd_6481765 := by
    simpa [prefixWord, tailWord_6481765, baseEnd_6481765] using wordTrace_append hprefix tailTrace_6481765
  have hstable : (prefixWord ++ tailWord_6481765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481765).length < 2 ^ (prefixWord ++ tailWord_6481765).sum := by decide
  have hdescent : baseEnd_6481765 < baseStart_6481765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481779 : List Nat := [1, 1, 1, 2, 2, 1, 3, 6, 2, 1, 3]
def baseStart_6481779 : Nat := 118140960795 + 6481779 * 2 ^ 59
def prefixEnd_6481779 : Nat := 4983230072969 + 3 ^ 40 * 6481779 * 2
def baseEnd_6481779 : Nat := 3328268123219100743553347

theorem tailTrace_6481779 : CollatzResearch.WordTrace tailWord_6481779 prefixEnd_6481779 3328268123219100743553347 := by
  unfold tailWord_6481779
  simp only [CollatzResearch.WordTrace]
  refine ⟨236409901984629157565560391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157606601323086105043706927 236409901984629157565560391)
  ·
    refine ⟨354614852976943736348340587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236409901984629157565560391 354614852976943736348340587)
    ·
      refine ⟨531922279465415604522510881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354614852976943736348340587 531922279465415604522510881)
      ·
        refine ⟨398941709599061703391883161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531922279465415604522510881 398941709599061703391883161)
        ·
          refine ⟨299206282199296277543912371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398941709599061703391883161 299206282199296277543912371)
          ·
            refine ⟨448809423298944416315868557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299206282199296277543912371 448809423298944416315868557)
            ·
              refine ⟨168303533737104156118450709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 448809423298944416315868557 168303533737104156118450709)
              ·
                refine ⟨7889228143926757318052377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 168303533737104156118450709 7889228143926757318052377)
                ·
                  refine ⟨5916921107945067988539283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7889228143926757318052377 5916921107945067988539283)
                  ·
                    refine ⟨8875381661917601982808925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5916921107945067988539283 8875381661917601982808925)
                    ·
                      refine ⟨3328268123219100743553347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8875381661917601982808925 3328268123219100743553347)
                      ·
                        rfl

theorem cell23_6481779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 1, 3].length) (baseStart_6481779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481779 prefixEnd_6481779 := by exact prefixLift 6481779
  have htrace : WordTrace (prefixWord ++ tailWord_6481779) baseStart_6481779 baseEnd_6481779 := by
    simpa [prefixWord, tailWord_6481779, baseEnd_6481779] using wordTrace_append hprefix tailTrace_6481779
  have hstable : (prefixWord ++ tailWord_6481779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481779).length < 2 ^ (prefixWord ++ tailWord_6481779).sum := by decide
  have hdescent : baseEnd_6481779 < baseStart_6481779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481789 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 3, 3, 2]
def baseStart_6481789 : Nat := 118140960795 + 6481789 * 2 ^ 59
def prefixEnd_6481789 : Nat := 4983230072969 + 3 ^ 40 * 6481789 * 2
def baseEnd_6481789 : Nat := 3328273258025645704428301

theorem tailTrace_6481789 : CollatzResearch.WordTrace tailWord_6481789 prefixEnd_6481789 3328273258025645704428301 := by
  unfold tailWord_6481789
  simp only [CollatzResearch.WordTrace]
  refine ⟨236410266714592929273424421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157606844476395286182282947 236410266714592929273424421)
  ·
    refine ⟨44326925008986174238767079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236410266714592929273424421 44326925008986174238767079)
    ·
      refine ⟨66490387513479261358150619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44326925008986174238767079 66490387513479261358150619)
      ·
        refine ⟨99735581270218892037225929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66490387513479261358150619 99735581270218892037225929)
        ·
          refine ⟨74801685952664169027919447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99735581270218892037225929 74801685952664169027919447)
          ·
            refine ⟨112202528928996253541879171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74801685952664169027919447 112202528928996253541879171)
            ·
              refine ⟨168303793393494380312818757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112202528928996253541879171 168303793393494380312818757)
              ·
                refine ⟨31556961261280196308653517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168303793393494380312818757 31556961261280196308653517)
                ·
                  refine ⟨11833860472980073615745069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31556961261280196308653517 11833860472980073615745069)
                  ·
                    refine ⟨4437697677367527605904401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11833860472980073615745069 4437697677367527605904401)
                    ·
                      refine ⟨3328273258025645704428301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4437697677367527605904401 3328273258025645704428301)
                      ·
                        rfl

theorem cell23_6481789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_6481789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481789 prefixEnd_6481789 := by exact prefixLift 6481789
  have htrace : WordTrace (prefixWord ++ tailWord_6481789) baseStart_6481789 baseEnd_6481789 := by
    simpa [prefixWord, tailWord_6481789, baseEnd_6481789] using wordTrace_append hprefix tailTrace_6481789
  have hstable : (prefixWord ++ tailWord_6481789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481789).length < 2 ^ (prefixWord ++ tailWord_6481789).sum := by decide
  have hdescent : baseEnd_6481789 < baseStart_6481789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481790 : List Nat := [4, 2, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_6481790 : Nat := 118140960795 + 6481790 * 2 ^ 59
def prefixEnd_6481790 : Nat := 4983230072969 + 3 ^ 40 * 6481790 * 2
def baseEnd_6481790 : Nat := 1109424590502100066838599

theorem tailTrace_6481790 : CollatzResearch.WordTrace tailWord_6481790 prefixEnd_6481790 1109424590502100066838599 := by
  unfold tailWord_6481790
  simp only [CollatzResearch.WordTrace]
  refine ⟨29551287898448663305526353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157606868791726204296140549 29551287898448663305526353)
  ·
    refine ⟨22163465923836497479144765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29551287898448663305526353 22163465923836497479144765)
    ·
      refine ⟨8311299721438686554679287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22163465923836497479144765 8311299721438686554679287)
      ·
        refine ⟨12466949582158029832018931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8311299721438686554679287 12466949582158029832018931)
        ·
          refine ⟨18700424373237044748028397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12466949582158029832018931 18700424373237044748028397)
          ·
            refine ⟨7012659139963891780510649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18700424373237044748028397 7012659139963891780510649)
            ·
              refine ⟨5259494354972918835382987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7012659139963891780510649 5259494354972918835382987)
              ·
                refine ⟨7889241532459378253074481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5259494354972918835382987 7889241532459378253074481)
                ·
                  refine ⟨5916931149344533689805861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7889241532459378253074481 5916931149344533689805861)
                  ·
                    refine ⟨1109424590502100066838599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5916931149344533689805861 1109424590502100066838599)
                    ·
                      rfl

theorem cell23_6481790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_6481790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481790 prefixEnd_6481790 := by exact prefixLift 6481790
  have htrace : WordTrace (prefixWord ++ tailWord_6481790) baseStart_6481790 baseEnd_6481790 := by
    simpa [prefixWord, tailWord_6481790, baseEnd_6481790] using wordTrace_append hprefix tailTrace_6481790
  have hstable : (prefixWord ++ tailWord_6481790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481790).length < 2 ^ (prefixWord ++ tailWord_6481790).sum := by decide
  have hdescent : baseEnd_6481790 < baseStart_6481790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481853 : List Nat := [1, 4, 1, 2, 3, 1, 2, 3, 2, 2, 2]
def baseStart_6481853 : Nat := 118140960795 + 6481853 * 2 ^ 59
def prefixEnd_6481853 : Nat := 4983230072969 + 3 ^ 40 * 6481853 * 2
def baseEnd_6481853 : Nat := 3328306120787533454028007

theorem tailTrace_6481853 : CollatzResearch.WordTrace tailWord_6481853 prefixEnd_6481853 3328306120787533454028007 := by
  unfold tailWord_6481853
  simp only [CollatzResearch.WordTrace]
  refine ⟨236412600986361068203754213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157608400657574045469169475 236412600986361068203754213)
  ·
    refine ⟨44327362684942700288203915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236412600986361068203754213 44327362684942700288203915)
    ·
      refine ⟨66491044027414050432305873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44327362684942700288203915 66491044027414050432305873)
      ·
        refine ⟨49868283020560537824229405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66491044027414050432305873 49868283020560537824229405)
        ·
          refine ⟨18700606132710201684086027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49868283020560537824229405 18700606132710201684086027)
          ·
            refine ⟨28050909199065302526129041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18700606132710201684086027 28050909199065302526129041)
            ·
              refine ⟨21038181899298976894596781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28050909199065302526129041 21038181899298976894596781)
              ·
                refine ⟨7889318212237116335473793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21038181899298976894596781 7889318212237116335473793)
                ·
                  refine ⟨5916988659177837251605345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7889318212237116335473793 5916988659177837251605345)
                  ·
                    refine ⟨4437741494383377938704009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5916988659177837251605345 4437741494383377938704009)
                    ·
                      refine ⟨3328306120787533454028007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4437741494383377938704009 3328306120787533454028007)
                      ·
                        rfl

theorem cell23_6481853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_6481853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481853 prefixEnd_6481853 := by exact prefixLift 6481853
  have htrace : WordTrace (prefixWord ++ tailWord_6481853) baseStart_6481853 baseEnd_6481853 := by
    simpa [prefixWord, tailWord_6481853, baseEnd_6481853] using wordTrace_append hprefix tailTrace_6481853
  have hstable : (prefixWord ++ tailWord_6481853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481853).length < 2 ^ (prefixWord ++ tailWord_6481853).sum := by decide
  have hdescent : baseEnd_6481853 < baseStart_6481853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481876 : List Nat := [2, 4, 1, 2, 1, 1, 4, 3, 5]
def baseStart_6481876 : Nat := 118140960795 + 6481876 * 2 ^ 59
def prefixEnd_6481876 : Nat := 4983230072969 + 3 ^ 40 * 6481876 * 2
def baseEnd_6481876 : Nat := 369813103426954096004489

theorem tailTrace_6481876 : CollatzResearch.WordTrace tailWord_6481876 prefixEnd_6481876 369813103426954096004489 := by
  unfold tailWord_6481876
  simp only [CollatzResearch.WordTrace]
  refine ⟨118206719932638871565920741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157608959910185162087894321 118206719932638871565920741)
  ·
    refine ⟨22163759987369788418610139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118206719932638871565920741 22163759987369788418610139)
    ·
      refine ⟨33245639981054682627915209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22163759987369788418610139 33245639981054682627915209)
      ·
        refine ⟨24934229985791011970936407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33245639981054682627915209 24934229985791011970936407)
        ·
          refine ⟨37401344978686517956404611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24934229985791011970936407 37401344978686517956404611)
          ·
            refine ⟨56102017468029776934606917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37401344978686517956404611 56102017468029776934606917)
            ·
              refine ⟨10519128275255583175238797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56102017468029776934606917 10519128275255583175238797)
              ·
                refine ⟨3944673103220843690714549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10519128275255583175238797 3944673103220843690714549)
                ·
                  refine ⟨369813103426954096004489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3944673103220843690714549 369813103426954096004489)
                  ·
                    rfl

theorem cell23_6481876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_6481876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481876 prefixEnd_6481876 := by exact prefixLift 6481876
  have htrace : WordTrace (prefixWord ++ tailWord_6481876) baseStart_6481876 baseEnd_6481876 := by
    simpa [prefixWord, tailWord_6481876, baseEnd_6481876] using wordTrace_append hprefix tailTrace_6481876
  have hstable : (prefixWord ++ tailWord_6481876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481876).length < 2 ^ (prefixWord ++ tailWord_6481876).sum := by decide
  have hdescent : baseEnd_6481876 < baseStart_6481876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481932 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 10]
def baseStart_6481932 : Nat := 118140960795 + 6481932 * 2 ^ 59
def prefixEnd_6481932 : Nat := 4983230072969 + 3 ^ 40 * 6481932 * 2
def baseEnd_6481932 : Nat := 369816298417693182771127

theorem tailTrace_6481932 : CollatzResearch.WordTrace tailWord_6481932 prefixEnd_6481932 369816298417693182771127 := by
  unfold tailWord_6481932
  simp only [CollatzResearch.WordTrace]
  refine ⟨118207741176537432347940025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157610321568716576463920033 118207741176537432347940025)
  ·
    refine ⟨88655805882403074260955019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118207741176537432347940025 88655805882403074260955019)
    ·
      refine ⟨132983708823604611391432529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88655805882403074260955019 132983708823604611391432529)
      ·
        refine ⟨99737781617703458543574397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132983708823604611391432529 99737781617703458543574397)
        ·
          refine ⟨37401668106638796953840399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99737781617703458543574397 37401668106638796953840399)
          ·
            refine ⟨56102502159958195430760599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37401668106638796953840399 56102502159958195430760599)
            ·
              refine ⟨84153753239937293146140899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56102502159958195430760599 84153753239937293146140899)
              ·
                refine ⟨126230629859905939719211349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84153753239937293146140899 126230629859905939719211349)
                ·
                  refine ⟨369816298417693182771127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 126230629859905939719211349 369816298417693182771127)
                  ·
                    rfl

theorem cell23_6481932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_6481932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481932 prefixEnd_6481932 := by exact prefixLift 6481932
  have htrace : WordTrace (prefixWord ++ tailWord_6481932) baseStart_6481932 baseEnd_6481932 := by
    simpa [prefixWord, tailWord_6481932, baseEnd_6481932] using wordTrace_append hprefix tailTrace_6481932
  have hstable : (prefixWord ++ tailWord_6481932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481932).length < 2 ^ (prefixWord ++ tailWord_6481932).sum := by decide
  have hdescent : baseEnd_6481932 < baseStart_6481932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481946 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3]
def baseStart_6481946 : Nat := 118140960795 + 6481946 * 2 ^ 59
def prefixEnd_6481946 : Nat := 4983230072969 + 3 ^ 40 * 6481946 * 2
def baseEnd_6481946 : Nat := 3328353874488401590165079

theorem tailTrace_6481946 : CollatzResearch.WordTrace tailWord_6481946 prefixEnd_6481946 3328353874488401590165079 := by
  unfold tailWord_6481946
  simp only [CollatzResearch.WordTrace]
  refine ⟨59103998243756036271722423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157610661983349430057926461 59103998243756036271722423)
  ·
    refine ⟨88655997365634054407583635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59103998243756036271722423 88655997365634054407583635)
    ·
      refine ⟨132983996048451081611375453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88655997365634054407583635 132983996048451081611375453)
      ·
        refine ⟨49868998518169155604265795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132983996048451081611375453 49868998518169155604265795)
        ·
          refine ⟨74803497777253733406398693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49868998518169155604265795 74803497777253733406398693)
          ·
            refine ⟨14025655833235075013699755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74803497777253733406398693 14025655833235075013699755)
            ·
              refine ⟨21038483749852612520549633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14025655833235075013699755 21038483749852612520549633)
              ·
                refine ⟨15778862812389459390412225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21038483749852612520549633 15778862812389459390412225)
                ·
                  refine ⟨11834147109292094542809169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15778862812389459390412225 11834147109292094542809169)
                  ·
                    refine ⟨8875610331969070907106877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11834147109292094542809169 8875610331969070907106877)
                    ·
                      refine ⟨3328353874488401590165079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8875610331969070907106877 3328353874488401590165079)
                      ·
                        rfl

theorem cell23_6481946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_6481946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481946 prefixEnd_6481946 := by exact prefixLift 6481946
  have htrace : WordTrace (prefixWord ++ tailWord_6481946) baseStart_6481946 baseEnd_6481946 := by
    simpa [prefixWord, tailWord_6481946, baseEnd_6481946] using wordTrace_append hprefix tailTrace_6481946
  have hstable : (prefixWord ++ tailWord_6481946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481946).length < 2 ^ (prefixWord ++ tailWord_6481946).sum := by decide
  have hdescent : baseEnd_6481946 < baseStart_6481946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481949 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 8]
def baseStart_6481949 : Nat := 118140960795 + 6481949 * 2 ^ 59
def prefixEnd_6481949 : Nat := 4983230072969 + 3 ^ 40 * 6481949 * 2
def baseEnd_6481949 : Nat := 369817268325596119825285

theorem tailTrace_6481949 : CollatzResearch.WordTrace tailWord_6481949 prefixEnd_6481949 369817268325596119825285 := by
  unfold tailWord_6481949
  simp only [CollatzResearch.WordTrace]
  refine ⟨236416102394013276599248901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157610734929342184399499267 236416102394013276599248901)
  ·
    refine ⟨44328019198877489362359169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236416102394013276599248901 44328019198877489362359169)
    ·
      refine ⟨33246014399158117021769377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44328019198877489362359169 33246014399158117021769377)
      ·
        refine ⟨24934510799368587766327033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33246014399158117021769377 24934510799368587766327033)
        ·
          refine ⟨18700883099526440824745275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24934510799368587766327033 18700883099526440824745275)
          ·
            refine ⟨28051324649289661237117913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18700883099526440824745275 28051324649289661237117913)
            ·
              refine ⟨21038493486967245927838435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28051324649289661237117913 21038493486967245927838435)
              ·
                refine ⟨31557740230450868891757653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21038493486967245927838435 31557740230450868891757653)
                ·
                  refine ⟨369817268325596119825285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31557740230450868891757653 369817268325596119825285)
                  ·
                    rfl

theorem cell23_6481949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_6481949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481949 prefixEnd_6481949 := by exact prefixLift 6481949
  have htrace : WordTrace (prefixWord ++ tailWord_6481949) baseStart_6481949 baseEnd_6481949 := by
    simpa [prefixWord, tailWord_6481949, baseEnd_6481949] using wordTrace_append hprefix tailTrace_6481949
  have hstable : (prefixWord ++ tailWord_6481949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481949).length < 2 ^ (prefixWord ++ tailWord_6481949).sum := by decide
  have hdescent : baseEnd_6481949 < baseStart_6481949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481953 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 3, 4]
def baseStart_6481953 : Nat := 118140960795 + 6481953 * 2 ^ 59
def prefixEnd_6481953 : Nat := 4983230072969 + 3 ^ 40 * 6481953 * 2
def baseEnd_6481953 : Nat := 1109452489617661020925849

theorem tailTrace_6481953 : CollatzResearch.WordTrace tailWord_6481953 prefixEnd_6481953 1109452489617661020925849 := by
  unfold tailWord_6481953
  simp only [CollatzResearch.WordTrace]
  refine ⟨236416248285998785282394513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157610832190665856854929675 236416248285998785282394513)
  ·
    refine ⟨177312186214499088961795885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236416248285998785282394513 177312186214499088961795885)
    ·
      refine ⟨66492069830437158360673457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177312186214499088961795885 66492069830437158360673457)
      ·
        refine ⟨49869052372827868770505093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66492069830437158360673457 49869052372827868770505093)
        ·
          refine ⟨9350447319905225394469705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49869052372827868770505093 9350447319905225394469705)
          ·
            refine ⟨7012835489928919045852279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9350447319905225394469705 7012835489928919045852279)
            ·
              refine ⟨10519253234893378568778419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7012835489928919045852279 10519253234893378568778419)
              ·
                refine ⟨15778879852340067853167629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10519253234893378568778419 15778879852340067853167629)
                ·
                  refine ⟨5917079944627525444937861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15778879852340067853167629 5917079944627525444937861)
                  ·
                    refine ⟨1109452489617661020925849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5917079944627525444937861 1109452489617661020925849)
                    ·
                      rfl

theorem cell23_6481953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_6481953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481953 prefixEnd_6481953 := by exact prefixLift 6481953
  have htrace : WordTrace (prefixWord ++ tailWord_6481953) baseStart_6481953 baseEnd_6481953 := by
    simpa [prefixWord, tailWord_6481953, baseEnd_6481953] using wordTrace_append hprefix tailTrace_6481953
  have hstable : (prefixWord ++ tailWord_6481953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481953).length < 2 ^ (prefixWord ++ tailWord_6481953).sum := by decide
  have hdescent : baseEnd_6481953 < baseStart_6481953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481966 : List Nat := [4, 1, 3, 1, 1, 3, 1, 3, 6]
def baseStart_6481966 : Nat := 118140960795 + 6481966 * 2 ^ 59
def prefixEnd_6481966 : Nat := 4983230072969 + 3 ^ 40 * 6481966 * 2
def baseEnd_6481966 : Nat := 369818238233499056879443

theorem tailTrace_6481966 : CollatzResearch.WordTrace tailWord_6481966 prefixEnd_6481966 369818238233499056879443 := by
  unfold tailWord_6481966
  simp only [CollatzResearch.WordTrace]
  refine ⟨29552090304368961062827219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157611148289967792335078501 29552090304368961062827219)
  ·
    refine ⟨44328135456553441594240829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29552090304368961062827219 44328135456553441594240829)
    ·
      refine ⟨16623050796207540597840311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44328135456553441594240829 16623050796207540597840311)
      ·
        refine ⟨24934576194311310896760467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16623050796207540597840311 24934576194311310896760467)
        ·
          refine ⟨37401864291466966345140701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24934576194311310896760467 37401864291466966345140701)
          ·
            refine ⟨14025699109300112379427763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37401864291466966345140701 14025699109300112379427763)
            ·
              refine ⟨21038548663950168569141645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14025699109300112379427763 21038548663950168569141645)
              ·
                refine ⟨7889455748981313213428117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21038548663950168569141645 7889455748981313213428117)
                ·
                  refine ⟨369818238233499056879443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7889455748981313213428117 369818238233499056879443)
                  ·
                    rfl

theorem cell23_6481966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_6481966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481966 prefixEnd_6481966 := by exact prefixLift 6481966
  have htrace : WordTrace (prefixWord ++ tailWord_6481966) baseStart_6481966 baseEnd_6481966 := by
    simpa [prefixWord, tailWord_6481966, baseEnd_6481966] using wordTrace_append hprefix tailTrace_6481966
  have hstable : (prefixWord ++ tailWord_6481966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481966).length < 2 ^ (prefixWord ++ tailWord_6481966).sum := by decide
  have hdescent : baseEnd_6481966 < baseStart_6481966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6481993 : List Nat := [1, 2, 1, 1, 2, 2, 4, 5, 1, 1, 3]
def baseStart_6481993 : Nat := 118140960795 + 6481993 * 2 ^ 59
def prefixEnd_6481993 : Nat := 4983230072969 + 3 ^ 40 * 6481993 * 2
def baseEnd_6481993 : Nat := 3328378008079162906277363

theorem tailTrace_6481993 : CollatzResearch.WordTrace tailWord_6481993 prefixEnd_6481993 3328378008079162906277363 := by
  unfold tailWord_6481993
  simp only [CollatzResearch.WordTrace]
  refine ⟨236417707205853872113850633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157611804803902581409233755 236417707205853872113850633)
  ·
    refine ⟨177313280404390404085387975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236417707205853872113850633 177313280404390404085387975)
    ·
      refine ⟨265969920606585606128081963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177313280404390404085387975 265969920606585606128081963)
      ·
        refine ⟨398954880909878409192122945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265969920606585606128081963 398954880909878409192122945)
        ·
          refine ⟨299216160682408806894092209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398954880909878409192122945 299216160682408806894092209)
          ·
            refine ⟨224412120511806605170569157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299216160682408806894092209 224412120511806605170569157)
            ·
              refine ⟨42077272595963738469481717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224412120511806605170569157 42077272595963738469481717)
              ·
                refine ⟨3944744305871600481513911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42077272595963738469481717 3944744305871600481513911)
                ·
                  refine ⟨5917116458807400722270867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3944744305871600481513911 5917116458807400722270867)
                  ·
                    refine ⟨8875674688211101083406301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5917116458807400722270867 8875674688211101083406301)
                    ·
                      refine ⟨3328378008079162906277363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8875674688211101083406301 3328378008079162906277363)
                      ·
                        rfl

theorem cell23_6481993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 1, 1, 3].length) (baseStart_6481993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6481993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6481993 prefixEnd_6481993 := by exact prefixLift 6481993
  have htrace : WordTrace (prefixWord ++ tailWord_6481993) baseStart_6481993 baseEnd_6481993 := by
    simpa [prefixWord, tailWord_6481993, baseEnd_6481993] using wordTrace_append hprefix tailTrace_6481993
  have hstable : (prefixWord ++ tailWord_6481993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6481993).length < 2 ^ (prefixWord ++ tailWord_6481993).sum := by decide
  have hdescent : baseEnd_6481993 < baseStart_6481993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6481993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482019 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 5]
def baseStart_6482019 : Nat := 118140960795 + 6482019 * 2 ^ 59
def prefixEnd_6482019 : Nat := 4983230072969 + 3 ^ 40 * 6482019 * 2
def baseEnd_6482019 : Nat := 3328391358576179804552243

theorem tailTrace_6482019 : CollatzResearch.WordTrace tailWord_6482019 prefixEnd_6482019 3328391358576179804552243 := by
  unfold tailWord_6482019
  simp only [CollatzResearch.WordTrace]
  refine ⟨236418655503759678554297111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157612437002506452369531407 236418655503759678554297111)
  ·
    refine ⟨354627983255639517831445667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236418655503759678554297111 354627983255639517831445667)
    ·
      refine ⟨531941974883459276747168501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354627983255639517831445667 531941974883459276747168501)
      ·
        refine ⟨49869560145324307195047047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 531941974883459276747168501 49869560145324307195047047)
        ·
          refine ⟨74804340217986460792570571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49869560145324307195047047 74804340217986460792570571)
          ·
            refine ⟨112206510326979691188855857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74804340217986460792570571 112206510326979691188855857)
            ·
              refine ⟨84154882745234768391641893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112206510326979691188855857 84154882745234768391641893)
              ·
                refine ⟨15779040514731519073432855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84154882745234768391641893 15779040514731519073432855)
                ·
                  refine ⟨23668560772097278610149283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15779040514731519073432855 23668560772097278610149283)
                  ·
                    refine ⟨35502841158145917915223925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23668560772097278610149283 35502841158145917915223925)
                    ·
                      refine ⟨3328391358576179804552243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35502841158145917915223925 3328391358576179804552243)
                      ·
                        rfl

theorem cell23_6482019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_6482019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482019 prefixEnd_6482019 := by exact prefixLift 6482019
  have htrace : WordTrace (prefixWord ++ tailWord_6482019) baseStart_6482019 baseEnd_6482019 := by
    simpa [prefixWord, tailWord_6482019, baseEnd_6482019] using wordTrace_append hprefix tailTrace_6482019
  have hstable : (prefixWord ++ tailWord_6482019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482019).length < 2 ^ (prefixWord ++ tailWord_6482019).sum := by decide
  have hdescent : baseEnd_6482019 < baseStart_6482019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482033 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 3, 2, 2]
def baseStart_6482033 : Nat := 118140960795 + 6482033 * 2 ^ 59
def prefixEnd_6482033 : Nat := 4983230072969 + 3 ^ 40 * 6482033 * 2
def baseEnd_6482033 : Nat := 3328398547305342749777179

theorem tailTrace_6482033 : CollatzResearch.WordTrace tailWord_6482033 prefixEnd_6482033 3328398547305342749777179 := by
  unfold tailWord_6482033
  simp only [CollatzResearch.WordTrace]
  refine ⟨236419166125708958945306753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157612777417139305963537835 236419166125708958945306753)
  ·
    refine ⟨177314374594281719208980065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236419166125708958945306753 177314374594281719208980065)
    ·
      refine ⟨132985780945711289406735049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177314374594281719208980065 132985780945711289406735049)
      ·
        refine ⟨99739335709283467055051287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132985780945711289406735049 99739335709283467055051287)
        ·
          refine ⟨149609003563925200582576931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99739335709283467055051287 149609003563925200582576931)
          ·
            refine ⟨224413505345887800873865397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149609003563925200582576931 224413505345887800873865397)
            ·
              refine ⟨21038766126176981331924881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224413505345887800873865397 21038766126176981331924881)
              ·
                refine ⟨15779074594632735998943661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21038766126176981331924881 15779074594632735998943661)
                ·
                  refine ⟨5917152972987275999603873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15779074594632735998943661 5917152972987275999603873)
                  ·
                    refine ⟨4437864729740456999702905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5917152972987275999603873 4437864729740456999702905)
                    ·
                      refine ⟨3328398547305342749777179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4437864729740456999702905 3328398547305342749777179)
                      ·
                        rfl

theorem cell23_6482033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_6482033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482033 prefixEnd_6482033 := by exact prefixLift 6482033
  have htrace : WordTrace (prefixWord ++ tailWord_6482033) baseStart_6482033 baseEnd_6482033 := by
    simpa [prefixWord, tailWord_6482033, baseEnd_6482033] using wordTrace_append hprefix tailTrace_6482033
  have hstable : (prefixWord ++ tailWord_6482033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482033).length < 2 ^ (prefixWord ++ tailWord_6482033).sum := by decide
  have hdescent : baseEnd_6482033 < baseStart_6482033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482053 : List Nat := [1, 3, 1, 1, 5, 2, 1, 3, 1, 2, 3]
def baseStart_6482053 : Nat := 118140960795 + 6482053 * 2 ^ 59
def prefixEnd_6482053 : Nat := 4983230072969 + 3 ^ 40 * 6482053 * 2
def baseEnd_6482053 : Nat := 3328408816918432671527087

theorem tailTrace_6482053 : CollatzResearch.WordTrace tailWord_6482053 prefixEnd_6482053 3328408816918432671527087 := by
  unfold tailWord_6482053
  simp only [CollatzResearch.WordTrace]
  refine ⟨236419895585636502361034813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157613263723757668240689875 236419895585636502361034813)
  ·
    refine ⟨88657460844613688385388055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236419895585636502361034813 88657460844613688385388055)
    ·
      refine ⟨132986191266920532578082083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88657460844613688385388055 132986191266920532578082083)
      ·
        refine ⟨199479286900380798867123125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132986191266920532578082083 199479286900380798867123125)
        ·
          refine ⟨18701183146910699893792793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199479286900380798867123125 18701183146910699893792793)
          ·
            refine ⟨14025887360183024920344595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18701183146910699893792793 14025887360183024920344595)
            ·
              refine ⟨21038831040274537380516893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14025887360183024920344595 21038831040274537380516893)
              ·
                refine ⟨7889561640102951517693835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21038831040274537380516893 7889561640102951517693835)
                ·
                  refine ⟨11834342460154427276540753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7889561640102951517693835 11834342460154427276540753)
                  ·
                    refine ⟨8875756845115820457405565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11834342460154427276540753 8875756845115820457405565)
                    ·
                      refine ⟨3328408816918432671527087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8875756845115820457405565 3328408816918432671527087)
                      ·
                        rfl

theorem cell23_6482053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_6482053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482053 prefixEnd_6482053 := by exact prefixLift 6482053
  have htrace : WordTrace (prefixWord ++ tailWord_6482053) baseStart_6482053 baseEnd_6482053 := by
    simpa [prefixWord, tailWord_6482053, baseEnd_6482053] using wordTrace_append hprefix tailTrace_6482053
  have hstable : (prefixWord ++ tailWord_6482053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482053).length < 2 ^ (prefixWord ++ tailWord_6482053).sum := by decide
  have hdescent : baseEnd_6482053 < baseStart_6482053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482090 : List Nat := [3, 1, 5, 1, 2, 2, 2, 7]
def baseStart_6482090 : Nat := 118140960795 + 6482090 * 2 ^ 59
def prefixEnd_6482090 : Nat := 4983230072969 + 3 ^ 40 * 6482090 * 2
def baseEnd_6482090 : Nat := 123275104285283297287571

theorem tailTrace_6482090 : CollatzResearch.WordTrace tailWord_6482090 prefixEnd_6482090 123275104285283297287571 := by
  unfold tailWord_6482090
  simp only [CollatzResearch.WordTrace]
  refine ⟨59105311271625614420032931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157614163391001638453421149 59105311271625614420032931)
  ·
    refine ⟨88657966907438421630049397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59105311271625614420032931 88657966907438421630049397)
    ·
      refine ⟨8311684397572352027817131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88657966907438421630049397 8311684397572352027817131)
      ·
        refine ⟨12467526596358528041725697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8311684397572352027817131 12467526596358528041725697)
        ·
          refine ⟨9350644947268896031294273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12467526596358528041725697 9350644947268896031294273)
          ·
            refine ⟨7012983710451672023470705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9350644947268896031294273 7012983710451672023470705)
            ·
              refine ⟨5259737782838754017603029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7012983710451672023470705 5259737782838754017603029)
              ·
                refine ⟨123275104285283297287571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5259737782838754017603029 123275104285283297287571)
                ·
                  rfl

theorem cell23_6482090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 7].length) (baseStart_6482090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482090 prefixEnd_6482090 := by exact prefixLift 6482090
  have htrace : WordTrace (prefixWord ++ tailWord_6482090) baseStart_6482090 baseEnd_6482090 := by
    simpa [prefixWord, tailWord_6482090, baseEnd_6482090] using wordTrace_append hprefix tailTrace_6482090
  have hstable : (prefixWord ++ tailWord_6482090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482090).length < 2 ^ (prefixWord ++ tailWord_6482090).sum := by decide
  have hdescent : baseEnd_6482090 < baseStart_6482090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482101 : List Nat := [1, 3, 3, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_6482101 : Nat := 118140960795 + 6482101 * 2 ^ 59
def prefixEnd_6482101 : Nat := 4983230072969 + 3 ^ 40 * 6482101 * 2
def baseEnd_6482101 : Nat := 3328433463989848483726867

theorem tailTrace_6482101 : CollatzResearch.WordTrace tailWord_6482101 prefixEnd_6482101 3328433463989848483726867 := by
  unfold tailWord_6482101
  simp only [CollatzResearch.WordTrace]
  refine ⟨236421646289462606558782157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157614430859641737705854771 236421646289462606558782157)
  ·
    refine ⟨88658117358548477459543309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236421646289462606558782157 88658117358548477459543309)
    ·
      refine ⟨33246794009455679047328741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88658117358548477459543309 33246794009455679047328741)
      ·
        refine ⟨6233773876772939821374139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33246794009455679047328741 6233773876772939821374139)
        ·
          refine ⟨9350660815159409732061209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6233773876772939821374139 9350660815159409732061209)
          ·
            refine ⟨7012995611369557299045907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9350660815159409732061209 7012995611369557299045907)
            ·
              refine ⟨10519493417054335948568861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7012995611369557299045907 10519493417054335948568861)
              ·
                refine ⟨3944810031395375980713323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10519493417054335948568861 3944810031395375980713323)
                ·
                  refine ⟨5917215047093063971069985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3944810031395375980713323 5917215047093063971069985)
                  ·
                    refine ⟨4437911285319797978302489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5917215047093063971069985 4437911285319797978302489)
                    ·
                      refine ⟨3328433463989848483726867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4437911285319797978302489 3328433463989848483726867)
                      ·
                        rfl

theorem cell23_6482101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_6482101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482101 prefixEnd_6482101 := by exact prefixLift 6482101
  have htrace : WordTrace (prefixWord ++ tailWord_6482101) baseStart_6482101 baseEnd_6482101 := by
    simpa [prefixWord, tailWord_6482101, baseEnd_6482101] using wordTrace_append hprefix tailTrace_6482101
  have hstable : (prefixWord ++ tailWord_6482101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482101).length < 2 ^ (prefixWord ++ tailWord_6482101).sum := by decide
  have hdescent : baseEnd_6482101 < baseStart_6482101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482123 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 4, 2, 2]
def baseStart_6482123 : Nat := 118140960795 + 6482123 * 2 ^ 59
def prefixEnd_6482123 : Nat := 4983230072969 + 3 ^ 40 * 6482123 * 2
def baseEnd_6482123 : Nat := 3328444760564247397651765

theorem tailTrace_6482123 : CollatzResearch.WordTrace tailWord_6482123 prefixEnd_6482123 3328444760564247397651765 := by
  unfold tailWord_6482123
  simp only [CollatzResearch.WordTrace]
  refine ⟨236422448695382904316083023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157614965796921936210722015 236422448695382904316083023)
  ·
    refine ⟨354633673043074356474124535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236422448695382904316083023 354633673043074356474124535)
    ·
      refine ⟨531950509564611534711186803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354633673043074356474124535 531950509564611534711186803)
      ·
        refine ⟨797925764346917302066780205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531950509564611534711186803 797925764346917302066780205)
        ·
          refine ⟨299222161630093988275042577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 797925764346917302066780205 299222161630093988275042577)
          ·
            refine ⟨224416621222570491206281933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299222161630093988275042577 224416621222570491206281933)
            ·
              refine ⟨84156232958463934202355725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224416621222570491206281933 84156232958463934202355725)
              ·
                refine ⟨31558587359423975325883397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84156232958463934202355725 31558587359423975325883397)
                ·
                  refine ⟨5917235129891995373603137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31558587359423975325883397 5917235129891995373603137)
                  ·
                    refine ⟨4437926347418996530202353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5917235129891995373603137 4437926347418996530202353)
                    ·
                      refine ⟨3328444760564247397651765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4437926347418996530202353 3328444760564247397651765)
                      ·
                        rfl

theorem cell23_6482123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 2, 2].length) (baseStart_6482123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482123 prefixEnd_6482123 := by exact prefixLift 6482123
  have htrace : WordTrace (prefixWord ++ tailWord_6482123) baseStart_6482123 baseEnd_6482123 := by
    simpa [prefixWord, tailWord_6482123, baseEnd_6482123] using wordTrace_append hprefix tailTrace_6482123
  have hstable : (prefixWord ++ tailWord_6482123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482123).length < 2 ^ (prefixWord ++ tailWord_6482123).sum := by decide
  have hdescent : baseEnd_6482123 < baseStart_6482123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482134 : List Nat := [5, 2, 1, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_6482134 : Nat := 118140960795 + 6482134 * 2 ^ 59
def prefixEnd_6482134 : Nat := 4983230072969 + 3 ^ 40 * 6482134 * 2
def baseEnd_6482134 : Nat := 3328450408851446854614215

theorem tailTrace_6482134 : CollatzResearch.WordTrace tailWord_6482134 prefixEnd_6482134 3328450408851446854614215 := by
  unfold tailWord_6482134
  simp only [CollatzResearch.WordTrace]
  refine ⟨14776428118646440824670841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157615233265562035463155637 14776428118646440824670841)
  ·
    refine ⟨11082321088984830618503131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14776428118646440824670841 11082321088984830618503131)
    ·
      refine ⟨16623481633477245927754697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11082321088984830618503131 16623481633477245927754697)
      ·
        refine ⟨12467611225107934445816023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16623481633477245927754697 12467611225107934445816023)
        ·
          refine ⟨18701416837661901668724035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12467611225107934445816023 18701416837661901668724035)
          ·
            refine ⟨28052125256492852503086053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18701416837661901668724035 28052125256492852503086053)
            ·
              refine ⟨5259773485592409844328635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28052125256492852503086053 5259773485592409844328635)
              ·
                refine ⟨7889660228388614766492953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5259773485592409844328635 7889660228388614766492953)
                ·
                  refine ⟨5917245171291461074869715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7889660228388614766492953 5917245171291461074869715)
                  ·
                    refine ⟨8875867756937191612304573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5917245171291461074869715 8875867756937191612304573)
                    ·
                      refine ⟨3328450408851446854614215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8875867756937191612304573 3328450408851446854614215)
                      ·
                        rfl

theorem cell23_6482134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_6482134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482134 prefixEnd_6482134 := by exact prefixLift 6482134
  have htrace : WordTrace (prefixWord ++ tailWord_6482134) baseStart_6482134 baseEnd_6482134 := by
    simpa [prefixWord, tailWord_6482134, baseEnd_6482134] using wordTrace_append hprefix tailTrace_6482134
  have hstable : (prefixWord ++ tailWord_6482134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482134).length < 2 ^ (prefixWord ++ tailWord_6482134).sum := by decide
  have hdescent : baseEnd_6482134 < baseStart_6482134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482176 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 2, 5]
def baseStart_6482176 : Nat := 118140960795 + 6482176 * 2 ^ 59
def prefixEnd_6482176 : Nat := 4983230072969 + 3 ^ 40 * 6482176 * 2
def baseEnd_6482176 : Nat := 1109490658346311896763007

theorem tailTrace_6482176 : CollatzResearch.WordTrace tailWord_6482176 prefixEnd_6482176 1109490658346311896763007 := by
  unfold tailWord_6482176
  simp only [CollatzResearch.WordTrace]
  refine ⟨118212190882095447183881191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157616254509460596245174921 118212190882095447183881191)
  ·
    refine ⟨177318286323143170775821787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118212190882095447183881191 177318286323143170775821787)
    ·
      refine ⟨265977429484714756163732681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177318286323143170775821787 265977429484714756163732681)
      ·
        refine ⟨199483072113536067122799511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265977429484714756163732681 199483072113536067122799511)
        ·
          refine ⟨299224608170304100684199267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199483072113536067122799511 299224608170304100684199267)
          ·
            refine ⟨448836912255456151026298901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299224608170304100684199267 448836912255456151026298901)
            ·
              refine ⟨21039230261974507079357761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 448836912255456151026298901 21039230261974507079357761)
              ·
                refine ⟨15779422696480880309518321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21039230261974507079357761 15779422696480880309518321)
                ·
                  refine ⟨11834567022360660232138741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15779422696480880309518321 11834567022360660232138741)
                  ·
                    refine ⟨1109490658346311896763007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11834567022360660232138741 1109490658346311896763007)
                    ·
                      rfl

theorem cell23_6482176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2, 5].length) (baseStart_6482176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482176 prefixEnd_6482176 := by exact prefixLift 6482176
  have htrace : WordTrace (prefixWord ++ tailWord_6482176) baseStart_6482176 baseEnd_6482176 := by
    simpa [prefixWord, tailWord_6482176, baseEnd_6482176] using wordTrace_append hprefix tailTrace_6482176
  have hstable : (prefixWord ++ tailWord_6482176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482176).length < 2 ^ (prefixWord ++ tailWord_6482176).sum := by decide
  have hdescent : baseEnd_6482176 < baseStart_6482176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482180 : List Nat := [2, 3, 2, 2, 3, 1, 1, 4, 5]
def baseStart_6482180 : Nat := 118140960795 + 6482180 * 2 ^ 59
def prefixEnd_6482180 : Nat := 4983230072969 + 3 ^ 40 * 6482180 * 2
def baseEnd_6482180 : Nat := 369830447662394852737667

theorem tailTrace_6482180 : CollatzResearch.WordTrace tailWord_6482180 prefixEnd_6482180 369830447662394852737667 := by
  unfold tailWord_6482180
  simp only [CollatzResearch.WordTrace]
  refine ⟨118212263828088201525453997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157616351770784268700605329 118212263828088201525453997)
  ·
    refine ⟨44329598935533075572045249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118212263828088201525453997 44329598935533075572045249)
    ·
      refine ⟨33247199201649806679033937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44329598935533075572045249 33247199201649806679033937)
      ·
        refine ⟨24935399401237355009275453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33247199201649806679033937 24935399401237355009275453)
        ·
          refine ⟨9350774775464008128478295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24935399401237355009275453 9350774775464008128478295)
          ·
            refine ⟨14026162163196012192717443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9350774775464008128478295 14026162163196012192717443)
            ·
              refine ⟨21039243244794018289076165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14026162163196012192717443 21039243244794018289076165)
              ·
                refine ⟨3944858108398878429201781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21039243244794018289076165 3944858108398878429201781)
                ·
                  refine ⟨369830447662394852737667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3944858108398878429201781 369830447662394852737667)
                  ·
                    rfl

theorem cell23_6482180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_6482180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482180 prefixEnd_6482180 := by exact prefixLift 6482180
  have htrace : WordTrace (prefixWord ++ tailWord_6482180) baseStart_6482180 baseEnd_6482180 := by
    simpa [prefixWord, tailWord_6482180, baseEnd_6482180] using wordTrace_append hprefix tailTrace_6482180
  have hstable : (prefixWord ++ tailWord_6482180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482180).length < 2 ^ (prefixWord ++ tailWord_6482180).sum := by decide
  have hdescent : baseEnd_6482180 < baseStart_6482180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482186 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_6482186 : Nat := 118140960795 + 6482186 * 2 ^ 59
def prefixEnd_6482186 : Nat := 4983230072969 + 3 ^ 40 * 6482186 * 2
def baseEnd_6482186 : Nat := 3328477109845480651163975

theorem tailTrace_6482186 : CollatzResearch.WordTrace tailWord_6482186 prefixEnd_6482186 3328477109845480651163975 := by
  unfold tailWord_6482186
  simp only [CollatzResearch.WordTrace]
  refine ⟨59106186623538666518906603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157616497662769777383750941 59106186623538666518906603)
  ·
    refine ⟨88659279935307999778359905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59106186623538666518906603 88659279935307999778359905)
    ·
      refine ⟨66494459951480999833769929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88659279935307999778359905 66494459951480999833769929)
      ·
        refine ⟨49870844963610749875327447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66494459951480999833769929 49870844963610749875327447)
        ·
          refine ⟨74806267445416124812991171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49870844963610749875327447 74806267445416124812991171)
          ·
            refine ⟨112209401168124187219486757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74806267445416124812991171 112209401168124187219486757)
            ·
              refine ⟨21039262719023285103653767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112209401168124187219486757 21039262719023285103653767)
              ·
                refine ⟨31558894078534927655480651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21039262719023285103653767 31558894078534927655480651)
                ·
                  refine ⟨47338341117802391483220977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31558894078534927655480651 47338341117802391483220977)
                  ·
                    refine ⟨35503755838351793612415733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47338341117802391483220977 35503755838351793612415733)
                    ·
                      refine ⟨3328477109845480651163975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35503755838351793612415733 3328477109845480651163975)
                      ·
                        rfl

theorem cell23_6482186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_6482186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482186 prefixEnd_6482186 := by exact prefixLift 6482186
  have htrace : WordTrace (prefixWord ++ tailWord_6482186) baseStart_6482186 baseEnd_6482186 := by
    simpa [prefixWord, tailWord_6482186, baseEnd_6482186] using wordTrace_append hprefix tailTrace_6482186
  have hstable : (prefixWord ++ tailWord_6482186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482186).length < 2 ^ (prefixWord ++ tailWord_6482186).sum := by decide
  have hdescent : baseEnd_6482186 < baseStart_6482186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482210 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_6482210 : Nat := 118140960795 + 6482210 * 2 ^ 59
def prefixEnd_6482210 : Nat := 4983230072969 + 3 ^ 40 * 6482210 * 2
def baseEnd_6482210 : Nat := 1109496477793729519087955

theorem tailTrace_6482210 : CollatzResearch.WordTrace tailWord_6482210 prefixEnd_6482210 1109496477793729519087955 := by
  unfold tailWord_6482210
  simp only [CollatzResearch.WordTrace]
  refine ⟨59106405461516929543625021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157617081230711812116333389 59106405461516929543625021)
  ·
    refine ⟨22164902048068848578859383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59106405461516929543625021 22164902048068848578859383)
    ·
      refine ⟨33247353072103272868289075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22164902048068848578859383 33247353072103272868289075)
      ·
        refine ⟨49871029608154909302433613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33247353072103272868289075 49871029608154909302433613)
        ·
          refine ⟨18701636103058090988412605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49871029608154909302433613 18701636103058090988412605)
          ·
            refine ⟨7013113538646784120654727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18701636103058090988412605 7013113538646784120654727)
            ·
              refine ⟨10519670307970176180982091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7013113538646784120654727 10519670307970176180982091)
              ·
                refine ⟨15779505461955264271473137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10519670307970176180982091 15779505461955264271473137)
                ·
                  refine ⟨11834629096466448203604853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15779505461955264271473137 11834629096466448203604853)
                  ·
                    refine ⟨1109496477793729519087955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11834629096466448203604853 1109496477793729519087955)
                    ·
                      rfl

theorem cell23_6482210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_6482210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482210 prefixEnd_6482210 := by exact prefixLift 6482210
  have htrace : WordTrace (prefixWord ++ tailWord_6482210) baseStart_6482210 baseEnd_6482210 := by
    simpa [prefixWord, tailWord_6482210, baseEnd_6482210] using wordTrace_append hprefix tailTrace_6482210
  have hstable : (prefixWord ++ tailWord_6482210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482210).length < 2 ^ (prefixWord ++ tailWord_6482210).sum := by decide
  have hdescent : baseEnd_6482210 < baseStart_6482210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482213 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 1, 3, 4]
def baseStart_6482213 : Nat := 118140960795 + 6482213 * 2 ^ 59
def prefixEnd_6482213 : Nat := 4983230072969 + 3 ^ 40 * 6482213 * 2
def baseEnd_6482213 : Nat := 3328490973823152045526351

theorem tailTrace_6482213 : CollatzResearch.WordTrace tailWord_6482213 prefixEnd_6482213 3328490973823152045526351 := by
  unfold tailWord_6482213
  simp only [CollatzResearch.WordTrace]
  refine ⟨236425731265056849686859293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157617154176704566457906195 236425731265056849686859293)
  ·
    refine ⟨88659649224396318632572235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236425731265056849686859293 88659649224396318632572235)
    ·
      refine ⟨132989473836594477948858353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88659649224396318632572235 132989473836594477948858353)
      ·
        refine ⟨99742105377445858461643765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132989473836594477948858353 99742105377445858461643765)
        ·
          refine ⟨9350822379135549230779103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99742105377445858461643765 9350822379135549230779103)
          ·
            refine ⟨14026233568703323846168655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9350822379135549230779103 14026233568703323846168655)
            ·
              refine ⟨21039350353054985769252983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14026233568703323846168655 21039350353054985769252983)
              ·
                refine ⟨31559025529582478653879475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21039350353054985769252983 31559025529582478653879475)
                ·
                  refine ⟨47338538294373717980819213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31559025529582478653879475 47338538294373717980819213)
                  ·
                    refine ⟨17751951860390144242807205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47338538294373717980819213 17751951860390144242807205)
                    ·
                      refine ⟨3328490973823152045526351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17751951860390144242807205 3328490973823152045526351)
                      ·
                        rfl

theorem cell23_6482213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_6482213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482213 prefixEnd_6482213 := by exact prefixLift 6482213
  have htrace : WordTrace (prefixWord ++ tailWord_6482213) baseStart_6482213 baseEnd_6482213 := by
    simpa [prefixWord, tailWord_6482213, baseEnd_6482213] using wordTrace_append hprefix tailTrace_6482213
  have hstable : (prefixWord ++ tailWord_6482213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482213).length < 2 ^ (prefixWord ++ tailWord_6482213).sum := by decide
  have hdescent : baseEnd_6482213 < baseStart_6482213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482236 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 8]
def baseStart_6482236 : Nat := 118140960795 + 6482236 * 2 ^ 59
def prefixEnd_6482236 : Nat := 4983230072969 + 3 ^ 40 * 6482236 * 2
def baseEnd_6482236 : Nat := 369833642653133939504305

theorem tailTrace_6482236 : CollatzResearch.WordTrace tailWord_6482236 prefixEnd_6482236 369833642653133939504305 := by
  unfold tailWord_6482236
  simp only [CollatzResearch.WordTrace]
  refine ⟨118213285071986762307473281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157617713429315683076631041 118213285071986762307473281)
  ·
    refine ⟨88659963803990071730604961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118213285071986762307473281 88659963803990071730604961)
    ·
      refine ⟨66494972852992553797953721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88659963803990071730604961 66494972852992553797953721)
      ·
        refine ⟨49871229639744415348465291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66494972852992553797953721 49871229639744415348465291)
        ·
          refine ⟨74806844459616623022697937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49871229639744415348465291 74806844459616623022697937)
          ·
            refine ⟨56105133344712467267023453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74806844459616623022697937 56105133344712467267023453)
            ·
              refine ⟨21039425004267175225133795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56105133344712467267023453 21039425004267175225133795)
              ·
                refine ⟨31559137506400762837700693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21039425004267175225133795 31559137506400762837700693)
                ·
                  refine ⟨369833642653133939504305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31559137506400762837700693 369833642653133939504305)
                  ·
                    rfl

theorem cell23_6482236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_6482236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482236 prefixEnd_6482236 := by exact prefixLift 6482236
  have htrace : WordTrace (prefixWord ++ tailWord_6482236) baseStart_6482236 baseEnd_6482236 := by
    simpa [prefixWord, tailWord_6482236, baseEnd_6482236] using wordTrace_append hprefix tailTrace_6482236
  have hstable : (prefixWord ++ tailWord_6482236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482236).length < 2 ^ (prefixWord ++ tailWord_6482236).sum := by decide
  have hdescent : baseEnd_6482236 < baseStart_6482236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482274 : List Nat := [3, 3, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_6482274 : Nat := 118140960795 + 6482274 * 2 ^ 59
def prefixEnd_6482274 : Nat := 4983230072969 + 3 ^ 40 * 6482274 * 2
def baseEnd_6482274 : Nat := 1109507432047692102287857

theorem tailTrace_6482274 : CollatzResearch.WordTrace tailWord_6482274 prefixEnd_6482274 1109507432047692102287857 := by
  unfold tailWord_6482274
  simp only [CollatzResearch.WordTrace]
  refine ⟨59106989029458964276207469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157618637411890571403219917 59106989029458964276207469)
  ·
    refine ⟨22165120886047111603577801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59106989029458964276207469 22165120886047111603577801)
    ·
      refine ⟨16623840664535333702683351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22165120886047111603577801 16623840664535333702683351)
      ·
        refine ⟨24935760996803000554025027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16623840664535333702683351 24935760996803000554025027)
        ·
          refine ⟨37403641495204500831037541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24935760996803000554025027 37403641495204500831037541)
          ·
            refine ⟨7013182780350843905819539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37403641495204500831037541 7013182780350843905819539)
            ·
              refine ⟨10519774170526265858729309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7013182780350843905819539 10519774170526265858729309)
              ·
                refine ⟨3944915313947349697023491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10519774170526265858729309 3944915313947349697023491)
                ·
                  refine ⟨5917372970921024545535237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3944915313947349697023491 5917372970921024545535237)
                  ·
                    refine ⟨1109507432047692102287857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5917372970921024545535237 1109507432047692102287857)
                    ·
                      rfl

theorem cell23_6482274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_6482274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482274 prefixEnd_6482274 := by exact prefixLift 6482274
  have htrace : WordTrace (prefixWord ++ tailWord_6482274) baseStart_6482274 baseEnd_6482274 := by
    simpa [prefixWord, tailWord_6482274, baseEnd_6482274] using wordTrace_append hprefix tailTrace_6482274
  have hstable : (prefixWord ++ tailWord_6482274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482274).length < 2 ^ (prefixWord ++ tailWord_6482274).sum := by decide
  have hdescent : baseEnd_6482274 < baseStart_6482274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482290 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 4, 3, 2]
def baseStart_6482290 : Nat := 118140960795 + 6482290 * 2 ^ 59
def prefixEnd_6482290 : Nat := 4983230072969 + 3 ^ 40 * 6482290 * 2
def baseEnd_6482290 : Nat := 3328530511833548244263497

theorem tailTrace_6482290 : CollatzResearch.WordTrace tailWord_6482290 prefixEnd_6482290 3328530511833548244263497 := by
  unfold tailWord_6482290
  simp only [CollatzResearch.WordTrace]
  refine ⟨59107134921444472959353081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157619026457185261224941549 59107134921444472959353081)
  ·
    refine ⟨44330351191083354719514811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59107134921444472959353081 44330351191083354719514811)
    ·
      refine ⟨66495526786625032079272217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44330351191083354719514811 66495526786625032079272217)
      ·
        refine ⟨49871645089968774059454163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66495526786625032079272217 49871645089968774059454163)
        ·
          refine ⟨74807467634953161089181245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49871645089968774059454163 74807467634953161089181245)
          ·
            refine ⟨28052800363107435408442967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74807467634953161089181245 28052800363107435408442967)
            ·
              refine ⟨42079200544661153112664451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28052800363107435408442967 42079200544661153112664451)
              ·
                refine ⟨63118800816991729668996677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42079200544661153112664451 63118800816991729668996677)
                ·
                  refine ⟨11834775153185949312936877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63118800816991729668996677 11834775153185949312936877)
                  ·
                    refine ⟨4438040682444730992351329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11834775153185949312936877 4438040682444730992351329)
                    ·
                      refine ⟨3328530511833548244263497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4438040682444730992351329 3328530511833548244263497)
                      ·
                        rfl

theorem cell23_6482290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_6482290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482290 prefixEnd_6482290 := by exact prefixLift 6482290
  have htrace : WordTrace (prefixWord ++ tailWord_6482290) baseStart_6482290 baseEnd_6482290 := by
    simpa [prefixWord, tailWord_6482290, baseEnd_6482290] using wordTrace_append hprefix tailTrace_6482290
  have hstable : (prefixWord ++ tailWord_6482290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482290).length < 2 ^ (prefixWord ++ tailWord_6482290).sum := by decide
  have hdescent : baseEnd_6482290 < baseStart_6482290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482324 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_6482324 : Nat := 118140960795 + 6482324 * 2 ^ 59
def prefixEnd_6482324 : Nat := 4983230072969 + 3 ^ 40 * 6482324 * 2
def baseEnd_6482324 : Nat := 3328547970175801111238341

theorem tailTrace_6482324 : CollatzResearch.WordTrace tailWord_6482324 prefixEnd_6482324 3328547970175801111238341 := by
  unfold tailWord_6482324
  simp only [CollatzResearch.WordTrace]
  refine ⟨118214889883827357822075013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157619853178436477096100017 118214889883827357822075013)
  ·
    refine ⟨22165291853217629591639065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118214889883827357822075013 22165291853217629591639065)
    ·
      refine ⟨16623968889913222193729299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22165291853217629591639065 16623968889913222193729299)
      ·
        refine ⟨24935953334869833290593949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16623968889913222193729299 24935953334869833290593949)
        ·
          refine ⟨9350982500576187483972731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24935953334869833290593949 9350982500576187483972731)
          ·
            refine ⟨14026473750864281225959097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9350982500576187483972731 14026473750864281225959097)
            ·
              refine ⟨10519855313148210919469323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14026473750864281225959097 10519855313148210919469323)
              ·
                refine ⟨15779782969722316379203985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10519855313148210919469323 15779782969722316379203985)
                ·
                  refine ⟨11834837227291737284402989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15779782969722316379203985 11834837227291737284402989)
                  ·
                    refine ⟨4438063960234401481651121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11834837227291737284402989 4438063960234401481651121)
                    ·
                      refine ⟨3328547970175801111238341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4438063960234401481651121 3328547970175801111238341)
                      ·
                        rfl

theorem cell23_6482324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_6482324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482324 prefixEnd_6482324 := by exact prefixLift 6482324
  have htrace : WordTrace (prefixWord ++ tailWord_6482324) baseStart_6482324 baseEnd_6482324 := by
    simpa [prefixWord, tailWord_6482324, baseEnd_6482324] using wordTrace_append hprefix tailTrace_6482324
  have hstable : (prefixWord ++ tailWord_6482324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482324).length < 2 ^ (prefixWord ++ tailWord_6482324).sum := by decide
  have hdescent : baseEnd_6482324 < baseStart_6482324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482334 : List Nat := [4, 3, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_6482334 : Nat := 118140960795 + 6482334 * 2 ^ 59
def prefixEnd_6482334 : Nat := 4983230072969 + 3 ^ 40 * 6482334 * 2
def baseEnd_6482334 : Nat := 1109517701660782024037765

theorem tailTrace_6482334 : CollatzResearch.WordTrace tailWord_6482334 prefixEnd_6482334 1109517701660782024037765 := by
  unfold tailWord_6482334
  simp only [CollatzResearch.WordTrace]
  refine ⟨29553768062202310919001757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157620096331745658234676037 29553768062202310919001757)
  ·
    refine ⟨11082663023325866594625659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29553768062202310919001757 11082663023325866594625659)
    ·
      refine ⟨16623994534988799891938489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11082663023325866594625659 16623994534988799891938489)
      ·
        refine ⟨12467995901241599918953867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16623994534988799891938489 12467995901241599918953867)
        ·
          refine ⟨18701993851862399878430801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12467995901241599918953867 18701993851862399878430801)
          ·
            refine ⟨14026495388896799908823101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18701993851862399878430801 14026495388896799908823101)
            ·
              refine ⟨5259935770836299965808663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14026495388896799908823101 5259935770836299965808663)
              ·
                refine ⟨7889903656254449948712995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5259935770836299965808663 7889903656254449948712995)
                ·
                  refine ⟨11834855484381674923069493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7889903656254449948712995 11834855484381674923069493)
                  ·
                    refine ⟨1109517701660782024037765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11834855484381674923069493 1109517701660782024037765)
                    ·
                      rfl

theorem cell23_6482334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_6482334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482334 prefixEnd_6482334 := by exact prefixLift 6482334
  have htrace : WordTrace (prefixWord ++ tailWord_6482334) baseStart_6482334 baseEnd_6482334 := by
    simpa [prefixWord, tailWord_6482334, baseEnd_6482334] using wordTrace_append hprefix tailTrace_6482334
  have hstable : (prefixWord ++ tailWord_6482334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482334).length < 2 ^ (prefixWord ++ tailWord_6482334).sum := by decide
  have hdescent : baseEnd_6482334 < baseStart_6482334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482340 : List Nat := [2, 3, 1, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_6482340 : Nat := 118140960795 + 6482340 * 2 ^ 59
def prefixEnd_6482340 : Nat := 4983230072969 + 3 ^ 40 * 6482340 * 2
def baseEnd_6482340 : Nat := 3328556185866273048638267

theorem tailTrace_6482340 : CollatzResearch.WordTrace tailWord_6482340 prefixEnd_6482340 3328556185866273048638267 := by
  unfold tailWord_6482340
  simp only [CollatzResearch.WordTrace]
  refine ⟨118215181667798375188366237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157620242223731166917821649 118215181667798375188366237)
  ·
    refine ⟨44330693125424390695637339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118215181667798375188366237 44330693125424390695637339)
    ·
      refine ⟨66496039688136586043456009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44330693125424390695637339 66496039688136586043456009)
      ·
        refine ⟨49872029766102439532592007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66496039688136586043456009 49872029766102439532592007)
        ·
          refine ⟨74808044649153659298888011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49872029766102439532592007 74808044649153659298888011)
          ·
            refine ⟨112212066973730488948332017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74808044649153659298888011 112212066973730488948332017)
            ·
              refine ⟨84159050230297866711249013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112212066973730488948332017 84159050230297866711249013)
              ·
                refine ⟨7889910959090425004179595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84159050230297866711249013 7889910959090425004179595)
                ·
                  refine ⟨11834866438635637506269393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7889910959090425004179595 11834866438635637506269393)
                  ·
                    refine ⟨8876149828976728129702045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11834866438635637506269393 8876149828976728129702045)
                    ·
                      refine ⟨3328556185866273048638267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8876149828976728129702045 3328556185866273048638267)
                      ·
                        rfl

theorem cell23_6482340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_6482340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482340 prefixEnd_6482340 := by exact prefixLift 6482340
  have htrace : WordTrace (prefixWord ++ tailWord_6482340) baseStart_6482340 baseEnd_6482340 := by
    simpa [prefixWord, tailWord_6482340, baseEnd_6482340] using wordTrace_append hprefix tailTrace_6482340
  have hstable : (prefixWord ++ tailWord_6482340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482340).length < 2 ^ (prefixWord ++ tailWord_6482340).sum := by decide
  have hdescent : baseEnd_6482340 < baseStart_6482340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482354 : List Nat := [3, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2]
def baseStart_6482354 : Nat := 118140960795 + 6482354 * 2 ^ 59
def prefixEnd_6482354 : Nat := 4983230072969 + 3 ^ 40 * 6482354 * 2
def baseEnd_6482354 : Nat := 3328563374595435993863203

theorem tailTrace_6482354 : CollatzResearch.WordTrace tailWord_6482354 prefixEnd_6482354 3328563374595435993863203 := by
  unfold tailWord_6482354
  simp only [CollatzResearch.WordTrace]
  refine ⟨59107718489386507691935529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157620582638364020511828077 59107718489386507691935529)
  ·
    refine ⟨44330788867039880768951647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59107718489386507691935529 44330788867039880768951647)
    ·
      refine ⟨66496183300559821153427471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44330788867039880768951647 66496183300559821153427471)
      ·
        refine ⟨99744274950839731730141207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66496183300559821153427471 99744274950839731730141207)
        ·
          refine ⟨149616412426259597595211811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99744274950839731730141207 149616412426259597595211811)
          ·
            refine ⟨224424618639389396392817717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149616412426259597595211811 224424618639389396392817717)
            ·
              refine ⟨21039807997442755911826661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224424618639389396392817717 21039807997442755911826661)
              ·
                refine ⟨3944963999520516733467499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21039807997442755911826661 3944963999520516733467499)
                ·
                  refine ⟨5917445999280775100201249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3944963999520516733467499 5917445999280775100201249)
                  ·
                    refine ⟨4438084499460581325150937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5917445999280775100201249 4438084499460581325150937)
                    ·
                      refine ⟨3328563374595435993863203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4438084499460581325150937 3328563374595435993863203)
                      ·
                        rfl

theorem cell23_6482354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_6482354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482354 prefixEnd_6482354 := by exact prefixLift 6482354
  have htrace : WordTrace (prefixWord ++ tailWord_6482354) baseStart_6482354 baseEnd_6482354 := by
    simpa [prefixWord, tailWord_6482354, baseEnd_6482354] using wordTrace_append hprefix tailTrace_6482354
  have hstable : (prefixWord ++ tailWord_6482354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482354).length < 2 ^ (prefixWord ++ tailWord_6482354).sum := by decide
  have hdescent : baseEnd_6482354 < baseStart_6482354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482421 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6482421 : Nat := 118140960795 + 6482421 * 2 ^ 59
def prefixEnd_6482421 : Nat := 4983230072969 + 3 ^ 40 * 6482421 * 2
def baseEnd_6482421 : Nat := 3328597777799287231725395

theorem tailTrace_6482421 : CollatzResearch.WordTrace tailWord_6482421 prefixEnd_6482421 3328597777799287231725395 := by
  unfold tailWord_6482421
  simp only [CollatzResearch.WordTrace]
  refine ⟨236433317648303301210431117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157622211765535534140287411 236433317648303301210431117)
  ·
    refine ⟨88662494118113737953911669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236433317648303301210431117 88662494118113737953911669)
    ·
      refine ⟨8312108823573162933179219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88662494118113737953911669 8312108823573162933179219)
      ·
        refine ⟨12468163235359744399768829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8312108823573162933179219 12468163235359744399768829)
        ·
          refine ⟨4675561213259904149913311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12468163235359744399768829 4675561213259904149913311)
          ·
            refine ⟨7013341819889856224869967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4675561213259904149913311 7013341819889856224869967)
            ·
              refine ⟨10520012729834784337304951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7013341819889856224869967 10520012729834784337304951)
              ·
                refine ⟨15780019094752176505957427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10520012729834784337304951 15780019094752176505957427)
                ·
                  refine ⟨23670028642128264758936141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15780019094752176505957427 23670028642128264758936141)
                  ·
                    refine ⟨8876260740798099284601053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23670028642128264758936141 8876260740798099284601053)
                    ·
                      refine ⟨3328597777799287231725395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8876260740798099284601053 3328597777799287231725395)
                      ·
                        rfl

theorem cell23_6482421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6482421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482421 prefixEnd_6482421 := by exact prefixLift 6482421
  have htrace : WordTrace (prefixWord ++ tailWord_6482421) baseStart_6482421 baseEnd_6482421 := by
    simpa [prefixWord, tailWord_6482421, baseEnd_6482421] using wordTrace_append hprefix tailTrace_6482421
  have hstable : (prefixWord ++ tailWord_6482421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482421).length < 2 ^ (prefixWord ++ tailWord_6482421).sum := by decide
  have hdescent : baseEnd_6482421 < baseStart_6482421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482497 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 2, 5]
def baseStart_6482497 : Nat := 118140960795 + 6482497 * 2 ^ 59
def prefixEnd_6482497 : Nat := 4983230072969 + 3 ^ 40 * 6482497 * 2
def baseEnd_6482497 : Nat := 1109545600776342978125015

theorem tailTrace_6482497 : CollatzResearch.WordTrace tailWord_6482497 prefixEnd_6482497 1109545600776342978125015 := by
  unfold tailWord_6482497
  simp only [CollatzResearch.WordTrace]
  refine ⟨236436089596027966190197745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157624059730685310793465163 236436089596027966190197745)
  ·
    refine ⟨177327067197020974642648309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236436089596027966190197745 177327067197020974642648309)
    ·
      refine ⟨16624412549720716372748279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177327067197020974642648309 16624412549720716372748279)
      ·
        refine ⟨24936618824581074559122419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16624412549720716372748279 24936618824581074559122419)
        ·
          refine ⟨37404928236871611838683629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24936618824581074559122419 37404928236871611838683629)
          ·
            refine ⟨14026848088826854439506361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37404928236871611838683629 14026848088826854439506361)
            ·
              refine ⟨10520136066620140829629771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14026848088826854439506361 10520136066620140829629771)
              ·
                refine ⟨15780204099930211244444657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10520136066620140829629771 15780204099930211244444657)
                ·
                  refine ⟨11835153074947658433333493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15780204099930211244444657 11835153074947658433333493)
                  ·
                    refine ⟨1109545600776342978125015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11835153074947658433333493 1109545600776342978125015)
                    ·
                      rfl

theorem cell23_6482497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_6482497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482497 prefixEnd_6482497 := by exact prefixLift 6482497
  have htrace : WordTrace (prefixWord ++ tailWord_6482497) baseStart_6482497 baseEnd_6482497 := by
    simpa [prefixWord, tailWord_6482497, baseEnd_6482497] using wordTrace_append hprefix tailTrace_6482497
  have hstable : (prefixWord ++ tailWord_6482497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482497).length < 2 ^ (prefixWord ++ tailWord_6482497).sum := by decide
  have hdescent : baseEnd_6482497 < baseStart_6482497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482540 : List Nat := [2, 2, 1, 1, 3, 1, 4, 3, 6]
def baseStart_6482540 : Nat := 118140960795 + 6482540 * 2 ^ 59
def prefixEnd_6482540 : Nat := 4983230072969 + 3 ^ 40 * 6482540 * 2
def baseEnd_6482540 : Nat := 369850986888574696237483

theorem tailTrace_6482540 : CollatzResearch.WordTrace tailWord_6482540 prefixEnd_6482540 369850986888574696237483 := by
  unfold tailWord_6482540
  simp only [CollatzResearch.WordTrace]
  refine ⟨118218828967436092267006537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157625105289914789689342049 118218828967436092267006537)
  ·
    refine ⟨88664121725577069200254903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118218828967436092267006537 88664121725577069200254903)
    ·
      refine ⟨132996182588365603800382355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88664121725577069200254903 132996182588365603800382355)
      ·
        refine ⟨199494273882548405700573533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132996182588365603800382355 199494273882548405700573533)
        ·
          refine ⟨74810352705955652137715075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199494273882548405700573533 74810352705955652137715075)
          ·
            refine ⟨112215529058933478206572613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74810352705955652137715075 112215529058933478206572613)
            ·
              refine ⟨21040411698550027163732365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112215529058933478206572613 21040411698550027163732365)
              ·
                refine ⟨7890154386956260186399637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21040411698550027163732365 7890154386956260186399637)
                ·
                  refine ⟨369850986888574696237483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7890154386956260186399637 369850986888574696237483)
                  ·
                    rfl

theorem cell23_6482540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_6482540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482540 prefixEnd_6482540 := by exact prefixLift 6482540
  have htrace : WordTrace (prefixWord ++ tailWord_6482540) baseStart_6482540 baseEnd_6482540 := by
    simpa [prefixWord, tailWord_6482540, baseEnd_6482540] using wordTrace_append hprefix tailTrace_6482540
  have hstable : (prefixWord ++ tailWord_6482540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482540).length < 2 ^ (prefixWord ++ tailWord_6482540).sum := by decide
  have hdescent : baseEnd_6482540 < baseStart_6482540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482567 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_6482567 : Nat := 118140960795 + 6482567 * 2 ^ 59
def prefixEnd_6482567 : Nat := 4983230072969 + 3 ^ 40 * 6482567 * 2
def baseEnd_6482567 : Nat := 3328672745974843660499723

theorem tailTrace_6482567 : CollatzResearch.WordTrace tailWord_6482567 prefixEnd_6482567 3328672745974843660499723 := by
  unfold tailWord_6482567
  simp only [CollatzResearch.WordTrace]
  refine ⟨236438642705774368145245955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157625761803849578763497303 236438642705774368145245955)
  ·
    refine ⟨354657964058661552217868933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236438642705774368145245955 354657964058661552217868933)
    ·
      refine ⟨66498368260999041040850425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354657964058661552217868933 66498368260999041040850425)
      ·
        refine ⟨49873776195749280780637819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66498368260999041040850425 49873776195749280780637819)
        ·
          refine ⟨74810664293623921170956729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49873776195749280780637819 74810664293623921170956729)
          ·
            refine ⟨56107998220217940878217547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74810664293623921170956729 56107998220217940878217547)
            ·
              refine ⟨84161997330326911317326321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56107998220217940878217547 84161997330326911317326321)
              ·
                refine ⟨63121497997745183487994741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84161997330326911317326321 63121497997745183487994741)
                ·
                  refine ⟨5917640437288610951999507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63121497997745183487994741 5917640437288610951999507)
                  ·
                    refine ⟨8876460655932916427999261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5917640437288610951999507 8876460655932916427999261)
                    ·
                      refine ⟨3328672745974843660499723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8876460655932916427999261 3328672745974843660499723)
                      ·
                        rfl

theorem cell23_6482567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_6482567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482567 prefixEnd_6482567 := by exact prefixLift 6482567
  have htrace : WordTrace (prefixWord ++ tailWord_6482567) baseStart_6482567 baseEnd_6482567 := by
    simpa [prefixWord, tailWord_6482567, baseEnd_6482567] using wordTrace_append hprefix tailTrace_6482567
  have hstable : (prefixWord ++ tailWord_6482567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482567).length < 2 ^ (prefixWord ++ tailWord_6482567).sum := by decide
  have hdescent : baseEnd_6482567 < baseStart_6482567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482584 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 3, 1, 3]
def baseStart_6482584 : Nat := 118140960795 + 6482584 * 2 ^ 59
def prefixEnd_6482584 : Nat := 4983230072969 + 3 ^ 40 * 6482584 * 2
def baseEnd_6482584 : Nat := 3328681475145970093987145

theorem tailTrace_6482584 : CollatzResearch.WordTrace tailWord_6482584 prefixEnd_6482584 3328681475145970093987145 := by
  unfold tailWord_6482584
  simp only [CollatzResearch.WordTrace]
  refine ⟨118219631373356390024307403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157626175164475186699076537 118219631373356390024307403)
  ·
    refine ⟨177329447060034585036461105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118219631373356390024307403 177329447060034585036461105)
    ·
      refine ⟨132997085295025938777345829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177329447060034585036461105 132997085295025938777345829)
      ·
        refine ⟨24936953492817363520752343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132997085295025938777345829 24936953492817363520752343)
        ·
          refine ⟨37405430239226045281128515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24936953492817363520752343 37405430239226045281128515)
          ·
            refine ⟨56108145358839067921692773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37405430239226045281128515 56108145358839067921692773)
            ·
              refine ⟨10520277254782325235317395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56108145358839067921692773 10520277254782325235317395)
              ·
                refine ⟨15780415882173487852976093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10520277254782325235317395 15780415882173487852976093)
                ·
                  refine ⟨5917655955815057944866035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15780415882173487852976093 5917655955815057944866035)
                  ·
                    refine ⟨8876483933722586917299053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5917655955815057944866035 8876483933722586917299053)
                    ·
                      refine ⟨3328681475145970093987145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8876483933722586917299053 3328681475145970093987145)
                      ·
                        rfl

theorem cell23_6482584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_6482584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482584 prefixEnd_6482584 := by exact prefixLift 6482584
  have htrace : WordTrace (prefixWord ++ tailWord_6482584) baseStart_6482584 baseEnd_6482584 := by
    simpa [prefixWord, tailWord_6482584, baseEnd_6482584] using wordTrace_append hprefix tailTrace_6482584
  have hstable : (prefixWord ++ tailWord_6482584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482584).length < 2 ^ (prefixWord ++ tailWord_6482584).sum := by decide
  have hdescent : baseEnd_6482584 < baseStart_6482584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482607 : List Nat := [1, 1, 2, 1, 2, 5, 1, 4, 1, 1, 4]
def baseStart_6482607 : Nat := 118140960795 + 6482607 * 2 ^ 59
def prefixEnd_6482607 : Nat := 4983230072969 + 3 ^ 40 * 6482607 * 2
def baseEnd_6482607 : Nat := 3328693285201023503999539

theorem tailTrace_6482607 : CollatzResearch.WordTrace tailWord_6482607 prefixEnd_6482607 3328693285201023503999539 := by
  unfold tailWord_6482607
  simp only [CollatzResearch.WordTrace]
  refine ⟨236440101625629454976702075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157626734417086303317801383 236440101625629454976702075)
  ·
    refine ⟨354660152438444182465053113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236440101625629454976702075 354660152438444182465053113)
    ·
      refine ⟨265995114328833136848789835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354660152438444182465053113 265995114328833136848789835)
      ·
        refine ⟨398992671493249705273184753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265995114328833136848789835 398992671493249705273184753)
        ·
          refine ⟨299244503619937278954888565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398992671493249705273184753 299244503619937278954888565)
          ·
            refine ⟨28054172214369119902020803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 299244503619937278954888565 28054172214369119902020803)
            ·
              refine ⟨42081258321553679853031205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28054172214369119902020803 42081258321553679853031205)
              ·
                refine ⟨7890235935291314972443351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42081258321553679853031205 7890235935291314972443351)
                ·
                  refine ⟨11835353902936972458665027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7890235935291314972443351 11835353902936972458665027)
                  ·
                    refine ⟨17753030854405458687997541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11835353902936972458665027 17753030854405458687997541)
                    ·
                      refine ⟨3328693285201023503999539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17753030854405458687997541 3328693285201023503999539)
                      ·
                        rfl

theorem cell23_6482607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 1, 4].length) (baseStart_6482607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482607 prefixEnd_6482607 := by exact prefixLift 6482607
  have htrace : WordTrace (prefixWord ++ tailWord_6482607) baseStart_6482607 baseEnd_6482607 := by
    simpa [prefixWord, tailWord_6482607, baseEnd_6482607] using wordTrace_append hprefix tailTrace_6482607
  have hstable : (prefixWord ++ tailWord_6482607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482607).length < 2 ^ (prefixWord ++ tailWord_6482607).sum := by decide
  have hdescent : baseEnd_6482607 < baseStart_6482607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482610 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_6482610 : Nat := 118140960795 + 6482610 * 2 ^ 59
def prefixEnd_6482610 : Nat := 4983230072969 + 3 ^ 40 * 6482610 * 2
def baseEnd_6482610 : Nat := 3328694825642986992262025

theorem tailTrace_6482610 : CollatzResearch.WordTrace tailWord_6482610 prefixEnd_6482610 3328694825642986992262025 := by
  unfold tailWord_6482610
  simp only [CollatzResearch.WordTrace]
  refine ⟨59110052761154646622265321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157626807363079057659374189 59110052761154646622265321)
  ·
    refine ⟨44332539570865984966698991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59110052761154646622265321 44332539570865984966698991)
    ·
      refine ⟨66498809356298977450048487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44332539570865984966698991 66498809356298977450048487)
      ·
        refine ⟨99748214034448466175072731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66498809356298977450048487 99748214034448466175072731)
        ·
          refine ⟨149622321051672699262609097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99748214034448466175072731 149622321051672699262609097)
          ·
            refine ⟨112216740788754524446956823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149622321051672699262609097 112216740788754524446956823)
            ·
              refine ⟨168325111183131786670435235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112216740788754524446956823 168325111183131786670435235)
              ·
                refine ⟨252487666774697680005652853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168325111183131786670435235 252487666774697680005652853)
                ·
                  refine ⟨23670718760127907500529955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252487666774697680005652853 23670718760127907500529955)
                  ·
                    refine ⟨35506078140191861250794933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23670718760127907500529955 35506078140191861250794933)
                    ·
                      refine ⟨3328694825642986992262025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35506078140191861250794933 3328694825642986992262025)
                      ·
                        rfl

theorem cell23_6482610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_6482610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482610 prefixEnd_6482610 := by exact prefixLift 6482610
  have htrace : WordTrace (prefixWord ++ tailWord_6482610) baseStart_6482610 baseEnd_6482610 := by
    simpa [prefixWord, tailWord_6482610, baseEnd_6482610] using wordTrace_append hprefix tailTrace_6482610
  have hstable : (prefixWord ++ tailWord_6482610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482610).length < 2 ^ (prefixWord ++ tailWord_6482610).sum := by decide
  have hdescent : baseEnd_6482610 < baseStart_6482610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482650 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_6482650 : Nat := 118140960795 + 6482650 * 2 ^ 59
def prefixEnd_6482650 : Nat := 4983230072969 + 3 ^ 40 * 6482650 * 2
def baseEnd_6482650 : Nat := 3328715364869166835761841

theorem tailTrace_6482650 : CollatzResearch.WordTrace tailWord_6482650 prefixEnd_6482650 3328715364869166835761841 := by
  unfold tailWord_6482650
  simp only [CollatzResearch.WordTrace]
  refine ⟨59110417491118418330129351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157627779976315782213678269 59110417491118418330129351)
  ·
    refine ⟨88665626236677627495194027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59110417491118418330129351 88665626236677627495194027)
    ·
      refine ⟨132998439355016441242791041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88665626236677627495194027 132998439355016441242791041)
      ·
        refine ⟨99748829516262330932093281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132998439355016441242791041 99748829516262330932093281)
        ·
          refine ⟨74811622137196748199069961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99748829516262330932093281 74811622137196748199069961)
          ·
            refine ⟨56108716602897561149302471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74811622137196748199069961 56108716602897561149302471)
            ·
              refine ⟨84163074904346341723953707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56108716602897561149302471 84163074904346341723953707)
              ·
                refine ⟨126244612356519512585930561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84163074904346341723953707 126244612356519512585930561)
                ·
                  refine ⟨94683459267389634439447921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126244612356519512585930561 94683459267389634439447921)
                  ·
                    refine ⟨71012594450542225829585941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94683459267389634439447921 71012594450542225829585941)
                    ·
                      refine ⟨3328715364869166835761841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71012594450542225829585941 3328715364869166835761841)
                      ·
                        rfl

theorem cell23_6482650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_6482650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482650 prefixEnd_6482650 := by exact prefixLift 6482650
  have htrace : WordTrace (prefixWord ++ tailWord_6482650) baseStart_6482650 baseEnd_6482650 := by
    simpa [prefixWord, tailWord_6482650, baseEnd_6482650] using wordTrace_append hprefix tailTrace_6482650
  have hstable : (prefixWord ++ tailWord_6482650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482650).length < 2 ^ (prefixWord ++ tailWord_6482650).sum := by decide
  have hdescent : baseEnd_6482650 < baseStart_6482650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6482661 : List Nat := [1, 3, 1, 4, 1, 4, 1, 2, 1, 2, 3]
def baseStart_6482661 : Nat := 118140960795 + 6482661 * 2 ^ 59
def prefixEnd_6482661 : Nat := 4983230072969 + 3 ^ 40 * 6482661 * 2
def baseEnd_6482661 : Nat := 3328721013156366292724291

theorem tailTrace_6482661 : CollatzResearch.WordTrace tailWord_6482661 prefixEnd_6482661 3328721013156366292724291 := by
  unfold tailWord_6482661
  simp only [CollatzResearch.WordTrace]
  refine ⟨236442071167433822199167837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157628047444955881466111891 236442071167433822199167837)
  ·
    refine ⟨88665776687787683324687939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236442071167433822199167837 88665776687787683324687939)
    ·
      refine ⟨132998665031681524987031909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88665776687787683324687939 132998665031681524987031909)
      ·
        refine ⟨24937249693440285935068483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132998665031681524987031909 24937249693440285935068483)
        ·
          refine ⟨37405874540160428902602725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24937249693440285935068483 37405874540160428902602725)
          ·
            refine ⟨7013601476280080419238011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37405874540160428902602725 7013601476280080419238011)
            ·
              refine ⟨10520402214420120628857017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7013601476280080419238011 10520402214420120628857017)
              ·
                refine ⟨7890301660815090471642763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10520402214420120628857017 7890301660815090471642763)
                ·
                  refine ⟨11835452491222635707464145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7890301660815090471642763 11835452491222635707464145)
                  ·
                    refine ⟨8876589368416976780598109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11835452491222635707464145 8876589368416976780598109)
                    ·
                      refine ⟨3328721013156366292724291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8876589368416976780598109 3328721013156366292724291)
                      ·
                        rfl

theorem cell23_6482661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_6482661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6482661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6482661 prefixEnd_6482661 := by exact prefixLift 6482661
  have htrace : WordTrace (prefixWord ++ tailWord_6482661) baseStart_6482661 baseEnd_6482661 := by
    simpa [prefixWord, tailWord_6482661, baseEnd_6482661] using wordTrace_append hprefix tailTrace_6482661
  have hstable : (prefixWord ++ tailWord_6482661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6482661).length < 2 ^ (prefixWord ++ tailWord_6482661).sum := by decide
  have hdescent : baseEnd_6482661 < baseStart_6482661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6482661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
