import V185TrunkScan23Chunk0128

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_763667 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 7]
def baseStart_763667 : Nat := 118140960795 + 763667 * 2 ^ 59
def prefixEnd_763667 : Nat := 4983230072969 + 3 ^ 40 * 763667 * 2
def baseEnd_763667 : Nat := 392128230977168883050465

theorem tailTrace_763667 : CollatzResearch.WordTrace tailWord_763667 prefixEnd_763667 392128230977168883050465 := by
  unfold tailWord_763667
  simp only [CollatzResearch.WordTrace]
  refine ⟨27853223724372357785129255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18568815816248238523419503 27853223724372357785129255)
  ·
    refine ⟨41779835586558536677693883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27853223724372357785129255 41779835586558536677693883)
    ·
      refine ⟨62669753379837805016540825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41779835586558536677693883 62669753379837805016540825)
      ·
        refine ⟨47002315034878353762405619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62669753379837805016540825 47002315034878353762405619)
        ·
          refine ⟨70503472552317530643608429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47002315034878353762405619 70503472552317530643608429)
          ·
            refine ⟨26438802207119073991353161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70503472552317530643608429 26438802207119073991353161)
            ·
              refine ⟨19829101655339305493514871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26438802207119073991353161 19829101655339305493514871)
              ·
                refine ⟨29743652483008958240272307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19829101655339305493514871 29743652483008958240272307)
                ·
                  refine ⟨44615478724513437360408461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29743652483008958240272307 44615478724513437360408461)
                  ·
                    refine ⟨16730804521692539010153173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44615478724513437360408461 16730804521692539010153173)
                    ·
                      refine ⟨392128230977168883050465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16730804521692539010153173 392128230977168883050465)
                      ·
                        rfl

theorem cell23_763667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_763667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763667 prefixEnd_763667 := by exact prefixLift 763667
  have htrace : WordTrace (prefixWord ++ tailWord_763667) baseStart_763667 baseEnd_763667 := by
    simpa [prefixWord, tailWord_763667, baseEnd_763667] using wordTrace_append hprefix tailTrace_763667
  have hstable : (prefixWord ++ tailWord_763667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763667).length < 2 ^ (prefixWord ++ tailWord_763667).sum := by decide
  have hdescent : baseEnd_763667 < baseStart_763667 := by decide
  rcases family_descends (prefixWord ++ tailWord_763667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763698 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2]
def baseStart_763698 : Nat := 118140960795 + 763698 * 2 ^ 59
def prefixEnd_763698 : Nat := 4983230072969 + 3 ^ 40 * 763698 * 2
def baseEnd_763698 : Nat := 392144148877458261762823

theorem tailTrace_763698 : CollatzResearch.WordTrace tailWord_763698 prefixEnd_763698 392144148877458261762823 := by
  unfold tailWord_763698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6963588596815012519876937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18569569591506700053005165 6963588596815012519876937)
  ·
    refine ⟨5222691447611259389907703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6963588596815012519876937 5222691447611259389907703)
    ·
      refine ⟨7834037171416889084861555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5222691447611259389907703 7834037171416889084861555)
      ·
        refine ⟨11751055757125333627292333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7834037171416889084861555 11751055757125333627292333)
        ·
          refine ⟨4406645908922000110234625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11751055757125333627292333 4406645908922000110234625)
          ·
            refine ⟨3304984431691500082675969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4406645908922000110234625 3304984431691500082675969)
            ·
              refine ⟨2478738323768625062006977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3304984431691500082675969 2478738323768625062006977)
              ·
                refine ⟨1859053742826468796505233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2478738323768625062006977 1859053742826468796505233)
                ·
                  refine ⟨1394290307119851597378925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1859053742826468796505233 1394290307119851597378925)
                  ·
                    refine ⟨522858865169944349017097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1394290307119851597378925 522858865169944349017097)
                    ·
                      refine ⟨392144148877458261762823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 522858865169944349017097 392144148877458261762823)
                      ·
                        rfl

theorem cell23_763698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_763698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763698 prefixEnd_763698 := by exact prefixLift 763698
  have htrace : WordTrace (prefixWord ++ tailWord_763698) baseStart_763698 baseEnd_763698 := by
    simpa [prefixWord, tailWord_763698, baseEnd_763698] using wordTrace_append hprefix tailTrace_763698
  have hstable : (prefixWord ++ tailWord_763698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763698).length < 2 ^ (prefixWord ++ tailWord_763698).sum := by decide
  have hdescent : baseEnd_763698 < baseStart_763698 := by decide
  rcases family_descends (prefixWord ++ tailWord_763698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763721 : List Nat := [1, 2, 1, 1, 2, 4, 1, 5, 2, 4]
def baseStart_763721 : Nat := 118140960795 + 763721 * 2 ^ 59
def prefixEnd_763721 : Nat := 4983230072969 + 3 ^ 40 * 763721 * 2
def baseEnd_763721 : Nat := 130718652977503890591739

theorem tailTrace_763721 : CollatzResearch.WordTrace tailWord_763721 prefixEnd_763721 130718652977503890591739 := by
  unfold tailWord_763721
  simp only [CollatzResearch.WordTrace]
  refine ⟨27855193266176725007595017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18570128844117816671730011 27855193266176725007595017)
  ·
    refine ⟨20891394949632543755696263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27855193266176725007595017 20891394949632543755696263)
    ·
      refine ⟨31337092424448815633544395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20891394949632543755696263 31337092424448815633544395)
      ·
        refine ⟨47005638636673223450316593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31337092424448815633544395 47005638636673223450316593)
        ·
          refine ⟨35254228977504917587737445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47005638636673223450316593 35254228977504917587737445)
          ·
            refine ⟨6610167933282172047700771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35254228977504917587737445 6610167933282172047700771)
            ·
              refine ⟨9915251899923258071551157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6610167933282172047700771 9915251899923258071551157)
              ·
                refine ⟨929554865617805444207921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9915251899923258071551157 929554865617805444207921)
                ·
                  refine ⟨697166149213354083155941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 929554865617805444207921 697166149213354083155941)
                  ·
                    refine ⟨130718652977503890591739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 697166149213354083155941 130718652977503890591739)
                    ·
                      rfl

theorem cell23_763721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 4].length) (baseStart_763721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763721 prefixEnd_763721 := by exact prefixLift 763721
  have htrace : WordTrace (prefixWord ++ tailWord_763721) baseStart_763721 baseEnd_763721 := by
    simpa [prefixWord, tailWord_763721, baseEnd_763721] using wordTrace_append hprefix tailTrace_763721
  have hstable : (prefixWord ++ tailWord_763721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763721).length < 2 ^ (prefixWord ++ tailWord_763721).sum := by decide
  have hdescent : baseEnd_763721 < baseStart_763721 := by decide
  rcases family_descends (prefixWord ++ tailWord_763721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763805 : List Nat := [1, 4, 2, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_763805 : Nat := 118140960795 + 763805 * 2 ^ 59
def prefixEnd_763805 : Nat := 4983230072969 + 3 ^ 40 * 763805 * 2
def baseEnd_763805 : Nat := 392199091307489343124831

theorem tailTrace_763805 : CollatzResearch.WordTrace tailWord_763805 prefixEnd_763805 392199091307489343124831 := by
  unfold tailWord_763805
  simp only [CollatzResearch.WordTrace]
  refine ⟨27858256997872407353652869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18572171331914938235768579 27858256997872407353652869)
  ·
    refine ⟨5223423187101076378809913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27858256997872407353652869 5223423187101076378809913)
    ·
      refine ⟨3917567390325807284107435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5223423187101076378809913 3917567390325807284107435)
      ·
        refine ⟨5876351085488710926161153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3917567390325807284107435 5876351085488710926161153)
        ·
          refine ⟨4407263314116533194620865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5876351085488710926161153 4407263314116533194620865)
          ·
            refine ⟨3305447485587399895965649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4407263314116533194620865 3305447485587399895965649)
            ·
              refine ⟨2479085614190549921974237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3305447485587399895965649 2479085614190549921974237)
              ·
                refine ⟨929657105321456220740339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2479085614190549921974237 929657105321456220740339)
                ·
                  refine ⟨1394485657982184331110509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929657105321456220740339 1394485657982184331110509)
                  ·
                    refine ⟨522932121743319124166441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1394485657982184331110509 522932121743319124166441)
                    ·
                      refine ⟨392199091307489343124831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 522932121743319124166441 392199091307489343124831)
                      ·
                        rfl

theorem cell23_763805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_763805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763805 prefixEnd_763805 := by exact prefixLift 763805
  have htrace : WordTrace (prefixWord ++ tailWord_763805) baseStart_763805 baseEnd_763805 := by
    simpa [prefixWord, tailWord_763805, baseEnd_763805] using wordTrace_append hprefix tailTrace_763805
  have hstable : (prefixWord ++ tailWord_763805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763805).length < 2 ^ (prefixWord ++ tailWord_763805).sum := by decide
  have hdescent : baseEnd_763805 < baseStart_763805 := by decide
  rcases family_descends (prefixWord ++ tailWord_763805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763869 : List Nat := [1, 4, 3, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_763869 : Nat := 118140960795 + 763869 * 2 ^ 59
def prefixEnd_763869 : Nat := 4983230072969 + 3 ^ 40 * 763869 * 2
def baseEnd_763869 : Nat := 392231954069377092724537

theorem tailTrace_763869 : CollatzResearch.WordTrace tailWord_763869 prefixEnd_763869 392231954069377092724537 := by
  unfold tailWord_763869
  simp only [CollatzResearch.WordTrace]
  refine ⟨27860591269640546283982661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18573727513093697522655107 27860591269640546283982661)
  ·
    refine ⟨5223860863057602428246749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27860591269640546283982661 5223860863057602428246749)
    ·
      refine ⟨1958947823646600910592531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5223860863057602428246749 1958947823646600910592531)
      ·
        refine ⟨2938421735469901365888797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1958947823646600910592531 2938421735469901365888797)
        ·
          refine ⟨1101908150801213012208299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2938421735469901365888797 1101908150801213012208299)
          ·
            refine ⟨1652862226201819518312449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101908150801213012208299 1652862226201819518312449)
            ·
              refine ⟨1239646669651364638734337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1652862226201819518312449 1239646669651364638734337)
              ·
                refine ⟨929735002238523479050753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239646669651364638734337 929735002238523479050753)
                ·
                  refine ⟨697301251678892609288065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 929735002238523479050753 697301251678892609288065)
                  ·
                    refine ⟨522975938759169456966049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 697301251678892609288065 522975938759169456966049)
                    ·
                      refine ⟨392231954069377092724537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 522975938759169456966049 392231954069377092724537)
                      ·
                        rfl

theorem cell23_763869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_763869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763869 prefixEnd_763869 := by exact prefixLift 763869
  have htrace : WordTrace (prefixWord ++ tailWord_763869) baseStart_763869 baseEnd_763869 := by
    simpa [prefixWord, tailWord_763869, baseEnd_763869] using wordTrace_append hprefix tailTrace_763869
  have hstable : (prefixWord ++ tailWord_763869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763869).length < 2 ^ (prefixWord ++ tailWord_763869).sum := by decide
  have hdescent : baseEnd_763869 < baseStart_763869 := by decide
  rcases family_descends (prefixWord ++ tailWord_763869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763875 : List Nat := [1, 1, 1, 6, 1, 2, 4, 2, 5]
def baseStart_763875 : Nat := 118140960795 + 763875 * 2 ^ 59
def prefixEnd_763875 : Nat := 4983230072969 + 3 ^ 40 * 763875 * 2
def baseEnd_763875 : Nat := 43581670550367118805501

theorem tailTrace_763875 : CollatzResearch.WordTrace tailWord_763875 prefixEnd_763875 43581670550367118805501 := by
  unfold tailWord_763875
  simp only [CollatzResearch.WordTrace]
  refine ⟨27860810107618809308701079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18573873405079206205800719 27860810107618809308701079)
  ·
    refine ⟨41791215161428213963051619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27860810107618809308701079 41791215161428213963051619)
    ·
      refine ⟨62686822742142320944577429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41791215161428213963051619 62686822742142320944577429)
      ·
        refine ⟨2938444816037921294277067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62686822742142320944577429 2938444816037921294277067)
        ·
          refine ⟨4407667224056881941415601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2938444816037921294277067 4407667224056881941415601)
          ·
            refine ⟨3305750418042661456061701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4407667224056881941415601 3305750418042661456061701)
            ·
              refine ⟨619828203382999023011569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3305750418042661456061701 619828203382999023011569)
              ·
                refine ⟨464871152537249267258677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619828203382999023011569 464871152537249267258677)
                ·
                  refine ⟨43581670550367118805501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 464871152537249267258677 43581670550367118805501)
                  ·
                    rfl

theorem cell23_763875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 5].length) (baseStart_763875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763875 prefixEnd_763875 := by exact prefixLift 763875
  have htrace : WordTrace (prefixWord ++ tailWord_763875) baseStart_763875 baseEnd_763875 := by
    simpa [prefixWord, tailWord_763875, baseEnd_763875] using wordTrace_append hprefix tailTrace_763875
  have hstable : (prefixWord ++ tailWord_763875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763875).length < 2 ^ (prefixWord ++ tailWord_763875).sum := by decide
  have hdescent : baseEnd_763875 < baseStart_763875 := by decide
  rcases family_descends (prefixWord ++ tailWord_763875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763891 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 4]
def baseStart_763891 : Nat := 118140960795 + 763891 * 2 ^ 59
def prefixEnd_763891 : Nat := 4983230072969 + 3 ^ 40 * 763891 * 2
def baseEnd_763891 : Nat := 392243250643776006649435

theorem tailTrace_763891 : CollatzResearch.WordTrace tailWord_763891 prefixEnd_763891 392243250643776006649435 := by
  unfold tailWord_763891
  simp only [CollatzResearch.WordTrace]
  refine ⟨27861393675560844041283527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18574262450373896027522351 27861393675560844041283527)
  ·
    refine ⟨41792090513341266061925291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27861393675560844041283527 41792090513341266061925291)
    ·
      refine ⟨62688135770011899092887937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41792090513341266061925291 62688135770011899092887937)
      ·
        refine ⟨47016101827508924319665953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62688135770011899092887937 47016101827508924319665953)
        ·
          refine ⟨35262076370631693239749465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47016101827508924319665953 35262076370631693239749465)
          ·
            refine ⟨26446557277973769929812099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35262076370631693239749465 26446557277973769929812099)
            ·
              refine ⟨39669835916960654894718149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26446557277973769929812099 39669835916960654894718149)
              ·
                refine ⟨7438094234430122792759653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39669835916960654894718149 7438094234430122792759653)
                ·
                  refine ⟨1394642668955648023642435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7438094234430122792759653 1394642668955648023642435)
                  ·
                    refine ⟨2091964003433472035463653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1394642668955648023642435 2091964003433472035463653)
                    ·
                      refine ⟨392243250643776006649435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2091964003433472035463653 392243250643776006649435)
                      ·
                        rfl

theorem cell23_763891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_763891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763891 prefixEnd_763891 := by exact prefixLift 763891
  have htrace : WordTrace (prefixWord ++ tailWord_763891) baseStart_763891 baseEnd_763891 := by
    simpa [prefixWord, tailWord_763891, baseEnd_763891] using wordTrace_append hprefix tailTrace_763891
  have hstable : (prefixWord ++ tailWord_763891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763891).length < 2 ^ (prefixWord ++ tailWord_763891).sum := by decide
  have hdescent : baseEnd_763891 < baseStart_763891 := by decide
  rcases family_descends (prefixWord ++ tailWord_763891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763918 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_763918 : Nat := 118140960795 + 763918 * 2 ^ 59
def prefixEnd_763918 : Nat := 4983230072969 + 3 ^ 40 * 763918 * 2
def baseEnd_763918 : Nat := 130752371540482467003937

theorem tailTrace_763918 : CollatzResearch.WordTrace tailWord_763918 prefixEnd_763918 130752371540482467003937 := by
  unfold tailWord_763918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3482797305807878456564551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18574918964308685101677605 3482797305807878456564551)
  ·
    refine ⟨5224195958711817684846827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3482797305807878456564551 5224195958711817684846827)
    ·
      refine ⟨7836293938067726527270241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5224195958711817684846827 7836293938067726527270241)
      ·
        refine ⟨5877220453550794895452681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7836293938067726527270241 5877220453550794895452681)
        ·
          refine ⟨4407915340163096171589511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5877220453550794895452681 4407915340163096171589511)
          ·
            refine ⟨6611873010244644257384267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4407915340163096171589511 6611873010244644257384267)
            ·
              refine ⟨9917809515366966386076401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6611873010244644257384267 9917809515366966386076401)
              ·
                refine ⟨7438357136525224789557301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9917809515366966386076401 7438357136525224789557301)
                ·
                  refine ⟨697345981549239824020997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7438357136525224789557301 697345981549239824020997)
                  ·
                    refine ⟨130752371540482467003937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 697345981549239824020997 130752371540482467003937)
                    ·
                      rfl

theorem cell23_763918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_763918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763918 prefixEnd_763918 := by exact prefixLift 763918
  have htrace : WordTrace (prefixWord ++ tailWord_763918) baseStart_763918 baseEnd_763918 := by
    simpa [prefixWord, tailWord_763918, baseEnd_763918] using wordTrace_append hprefix tailTrace_763918
  have hstable : (prefixWord ++ tailWord_763918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763918).length < 2 ^ (prefixWord ++ tailWord_763918).sum := by decide
  have hdescent : baseEnd_763918 < baseStart_763918 := by decide
  rcases family_descends (prefixWord ++ tailWord_763918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763928 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 4, 2, 3]
def baseStart_763928 : Nat := 118140960795 + 763928 * 2 ^ 59
def prefixEnd_763928 : Nat := 4983230072969 + 3 ^ 40 * 763928 * 2
def baseEnd_763928 : Nat := 392262249427992361886765

theorem tailTrace_763928 : CollatzResearch.WordTrace tailWord_763928 prefixEnd_763928 392262249427992361886765 := by
  unfold tailWord_763928
  simp only [CollatzResearch.WordTrace]
  refine ⟨13931371588213399680190219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18575162117617866240253625 13931371588213399680190219)
  ·
    refine ⟨20897057382320099520285329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13931371588213399680190219 20897057382320099520285329)
    ·
      refine ⟨15672793036740074640213997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20897057382320099520285329 15672793036740074640213997)
      ·
        refine ⟨5877297388777527990080249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15672793036740074640213997 5877297388777527990080249)
        ·
          refine ⟨4407973041583145992560187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5877297388777527990080249 4407973041583145992560187)
          ·
            refine ⟨6611959562374718988840281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4407973041583145992560187 6611959562374718988840281)
            ·
              refine ⟨4958969671781039241630211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6611959562374718988840281 4958969671781039241630211)
              ·
                refine ⟨7438454507671558862445317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958969671781039241630211 7438454507671558862445317)
                ·
                  refine ⟨1394710220188417286708497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7438454507671558862445317 1394710220188417286708497)
                  ·
                    refine ⟨1046032665141312965031373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1394710220188417286708497 1046032665141312965031373)
                    ·
                      refine ⟨392262249427992361886765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1046032665141312965031373 392262249427992361886765)
                      ·
                        rfl

theorem cell23_763928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_763928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763928 prefixEnd_763928 := by exact prefixLift 763928
  have htrace : WordTrace (prefixWord ++ tailWord_763928) baseStart_763928 baseEnd_763928 := by
    simpa [prefixWord, tailWord_763928, baseEnd_763928] using wordTrace_append hprefix tailTrace_763928
  have hstable : (prefixWord ++ tailWord_763928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763928).length < 2 ^ (prefixWord ++ tailWord_763928).sum := by decide
  have hdescent : baseEnd_763928 < baseStart_763928 := by decide
  rcases family_descends (prefixWord ++ tailWord_763928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763931 : List Nat := [1, 1, 1, 1, 1, 1, 3, 8, 6]
def baseStart_763931 : Nat := 118140960795 + 763931 * 2 ^ 59
def prefixEnd_763931 : Nat := 4983230072969 + 3 ^ 40 * 763931 * 2
def baseEnd_763931 : Nat := 43584865541106205572139

theorem tailTrace_763931 : CollatzResearch.WordTrace tailWord_763931 prefixEnd_763931 43584865541106205572139 := by
  unfold tailWord_763931
  simp only [CollatzResearch.WordTrace]
  refine ⟨27862852595415930872739647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18575235063610620581826431 27862852595415930872739647)
  ·
    refine ⟨41794278893123896309109471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27862852595415930872739647 41794278893123896309109471)
    ·
      refine ⟨62691418339685844463664207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41794278893123896309109471 62691418339685844463664207)
      ·
        refine ⟨94037127509528766695496311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62691418339685844463664207 94037127509528766695496311)
        ·
          refine ⟨141055691264293150043244467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94037127509528766695496311 141055691264293150043244467)
          ·
            refine ⟨211583536896439725064866701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141055691264293150043244467 211583536896439725064866701)
            ·
              refine ⟨79343826336164896899325013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211583536896439725064866701 79343826336164896899325013)
              ·
                refine ⟨929810464876932385538965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 79343826336164896899325013 929810464876932385538965)
                ·
                  refine ⟨43584865541106205572139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 929810464876932385538965 43584865541106205572139)
                  ·
                    rfl

theorem cell23_763931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 6].length) (baseStart_763931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763931 prefixEnd_763931 := by exact prefixLift 763931
  have htrace : WordTrace (prefixWord ++ tailWord_763931) baseStart_763931 baseEnd_763931 := by
    simpa [prefixWord, tailWord_763931, baseEnd_763931] using wordTrace_append hprefix tailTrace_763931
  have hstable : (prefixWord ++ tailWord_763931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763931).length < 2 ^ (prefixWord ++ tailWord_763931).sum := by decide
  have hdescent : baseEnd_763931 < baseStart_763931 := by decide
  rcases family_descends (prefixWord ++ tailWord_763931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763935 : List Nat := [1, 1, 2, 4, 1, 2, 1, 6, 1, 4]
def baseStart_763935 : Nat := 118140960795 + 763935 * 2 ^ 59
def prefixEnd_763935 : Nat := 4983230072969 + 3 ^ 40 * 763935 * 2
def baseEnd_763935 : Nat := 130755281264191278166411

theorem tailTrace_763935 : CollatzResearch.WordTrace tailWord_763935 prefixEnd_763935 130755281264191278166411 := by
  unfold tailWord_763935
  simp only [CollatzResearch.WordTrace]
  refine ⟨27862998487401439555885259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18575332324934293037256839 27862998487401439555885259)
  ·
    refine ⟨41794497731102159333827889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27862998487401439555885259 41794497731102159333827889)
    ·
      refine ⟨31345873298326619500370917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41794497731102159333827889 31345873298326619500370917)
      ·
        refine ⟨5877351243436241156319547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31345873298326619500370917 5877351243436241156319547)
        ·
          refine ⟨8816026865154361734479321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5877351243436241156319547 8816026865154361734479321)
          ·
            refine ⟨6612020148865771300859491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8816026865154361734479321 6612020148865771300859491)
            ·
              refine ⟨9918030223298656951289237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6612020148865771300859491 9918030223298656951289237)
              ·
                refine ⟨464907666717124544591683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9918030223298656951289237 464907666717124544591683)
                ·
                  refine ⟨697361500075686816887525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464907666717124544591683 697361500075686816887525)
                  ·
                    refine ⟨130755281264191278166411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 697361500075686816887525 130755281264191278166411)
                    ·
                      rfl

theorem cell23_763935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 1, 4].length) (baseStart_763935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763935 prefixEnd_763935 := by exact prefixLift 763935
  have htrace : WordTrace (prefixWord ++ tailWord_763935) baseStart_763935 baseEnd_763935 := by
    simpa [prefixWord, tailWord_763935, baseEnd_763935] using wordTrace_append hprefix tailTrace_763935
  have hstable : (prefixWord ++ tailWord_763935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763935).length < 2 ^ (prefixWord ++ tailWord_763935).sum := by decide
  have hdescent : baseEnd_763935 < baseStart_763935 := by decide
  rcases family_descends (prefixWord ++ tailWord_763935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763969 : List Nat := [1, 2, 5, 1, 2, 3, 1, 3, 1, 4]
def baseStart_763969 : Nat := 118140960795 + 763969 * 2 ^ 59
def prefixEnd_763969 : Nat := 4983230072969 + 3 ^ 40 * 763969 * 2
def baseEnd_763969 : Nat := 130761100711608900491359

theorem tailTrace_763969 : CollatzResearch.WordTrace tailWord_763969 prefixEnd_763969 130761100711608900491359 := by
  unfold tailWord_763969
  simp only [CollatzResearch.WordTrace]
  refine ⟨27864238569278263362622961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18576159046185508908415307 27864238569278263362622961)
  ·
    refine ⟨20898178926958697521967221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27864238569278263362622961 20898178926958697521967221)
    ·
      refine ⟨1959204274402377892684427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20898178926958697521967221 1959204274402377892684427)
      ·
        refine ⟨2938806411603566839026641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1959204274402377892684427 2938806411603566839026641)
        ·
          refine ⟨2204104808702675129269981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2938806411603566839026641 2204104808702675129269981)
          ·
            refine ⟨826539303263503173476243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2204104808702675129269981 826539303263503173476243)
            ·
              refine ⟨1239808954895254760214365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826539303263503173476243 1239808954895254760214365)
              ·
                refine ⟨464928358085720535080387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1239808954895254760214365 464928358085720535080387)
                ·
                  refine ⟨697392537128580802620581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464928358085720535080387 697392537128580802620581)
                  ·
                    refine ⟨130761100711608900491359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 697392537128580802620581 130761100711608900491359)
                    ·
                      rfl

theorem cell23_763969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_763969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763969 prefixEnd_763969 := by exact prefixLift 763969
  have htrace : WordTrace (prefixWord ++ tailWord_763969) baseStart_763969 baseEnd_763969 := by
    simpa [prefixWord, tailWord_763969, baseEnd_763969] using wordTrace_append hprefix tailTrace_763969
  have hstable : (prefixWord ++ tailWord_763969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763969).length < 2 ^ (prefixWord ++ tailWord_763969).sum := by decide
  have hdescent : baseEnd_763969 < baseStart_763969 := by decide
  rcases family_descends (prefixWord ++ tailWord_763969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_763992 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 3, 1, 3]
def baseStart_763992 : Nat := 118140960795 + 763992 * 2 ^ 59
def prefixEnd_763992 : Nat := 4983230072969 + 3 ^ 40 * 763992 * 2
def baseEnd_763992 : Nat := 392295112189880111486471

theorem tailTrace_763992 : CollatzResearch.WordTrace tailWord_763992 prefixEnd_763992 392295112189880111486471 := by
  unfold tailWord_763992
  simp only [CollatzResearch.WordTrace]
  refine ⟨13932538724097469145355115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18576718298796625527140153 13932538724097469145355115)
  ·
    refine ⟨20898808086146203718032673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13932538724097469145355115 20898808086146203718032673)
    ·
      refine ⟨15674106064609652788524505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20898808086146203718032673 15674106064609652788524505)
      ·
        refine ⟨11755579548457239591393379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15674106064609652788524505 11755579548457239591393379)
        ·
          refine ⟨17633369322685859387090069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11755579548457239591393379 17633369322685859387090069)
          ·
            refine ⟨826564187000899658769847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17633369322685859387090069 826564187000899658769847)
            ·
              refine ⟨1239846280501349488154771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826564187000899658769847 1239846280501349488154771)
              ·
                refine ⟨1859769420752024232232157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239846280501349488154771 1859769420752024232232157)
                ·
                  refine ⟨697413532782009087087059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1859769420752024232232157 697413532782009087087059)
                  ·
                    refine ⟨1046120299173013630630589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 697413532782009087087059 1046120299173013630630589)
                    ·
                      refine ⟨392295112189880111486471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1046120299173013630630589 392295112189880111486471)
                      ·
                        rfl

theorem cell23_763992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_763992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_763992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_763992 prefixEnd_763992 := by exact prefixLift 763992
  have htrace : WordTrace (prefixWord ++ tailWord_763992) baseStart_763992 baseEnd_763992 := by
    simpa [prefixWord, tailWord_763992, baseEnd_763992] using wordTrace_append hprefix tailTrace_763992
  have hstable : (prefixWord ++ tailWord_763992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_763992).length < 2 ^ (prefixWord ++ tailWord_763992).sum := by decide
  have hdescent : baseEnd_763992 < baseStart_763992 := by decide
  rcases family_descends (prefixWord ++ tailWord_763992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764015 : List Nat := [1, 1, 2, 1, 3, 4, 3, 2, 1, 1, 4]
def baseStart_764015 : Nat := 118140960795 + 764015 * 2 ^ 59
def prefixEnd_764015 : Nat := 4983230072969 + 3 ^ 40 * 764015 * 2
def baseEnd_764015 : Nat := 392306922244933521498865

theorem tailTrace_764015 : CollatzResearch.WordTrace tailWord_764015 prefixEnd_764015 392306922244933521498865 := by
  unfold tailWord_764015
  simp only [CollatzResearch.WordTrace]
  refine ⟨27865916327111613218797499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18577277551407742145864999 27865916327111613218797499)
  ·
    refine ⟨41798874490667419828196249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27865916327111613218797499 41798874490667419828196249)
    ·
      refine ⟨31349155868000564871147187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41798874490667419828196249 31349155868000564871147187)
      ·
        refine ⟨47023733802000847306720781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31349155868000564871147187 47023733802000847306720781)
        ·
          refine ⟨17633900175750317740020293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47023733802000847306720781 17633900175750317740020293)
          ·
            refine ⟨3306356282953184576253805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17633900175750317740020293 3306356282953184576253805)
            ·
              refine ⟨1239883606107444216095177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3306356282953184576253805 1239883606107444216095177)
              ·
                refine ⟨929912704580583162071383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239883606107444216095177 929912704580583162071383)
                ·
                  refine ⟨1394869056870874743107075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929912704580583162071383 1394869056870874743107075)
                  ·
                    refine ⟨2092303585306312114660613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1394869056870874743107075 2092303585306312114660613)
                    ·
                      refine ⟨392306922244933521498865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2092303585306312114660613 392306922244933521498865)
                      ·
                        rfl

theorem cell23_764015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 1, 4].length) (baseStart_764015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764015 prefixEnd_764015 := by exact prefixLift 764015
  have htrace : WordTrace (prefixWord ++ tailWord_764015) baseStart_764015 baseEnd_764015 := by
    simpa [prefixWord, tailWord_764015, baseEnd_764015] using wordTrace_append hprefix tailTrace_764015
  have hstable : (prefixWord ++ tailWord_764015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764015).length < 2 ^ (prefixWord ++ tailWord_764015).sum := by decide
  have hdescent : baseEnd_764015 < baseStart_764015 := by decide
  rcases family_descends (prefixWord ++ tailWord_764015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764028 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_764028 : Nat := 118140960795 + 764028 * 2 ^ 59
def prefixEnd_764028 : Nat := 4983230072969 + 3 ^ 40 * 764028 * 2
def baseEnd_764028 : Nat := 392313597493441970636305

theorem tailTrace_764028 : CollatzResearch.WordTrace tailWord_764028 prefixEnd_764028 392313597493441970636305 := by
  unfold tailWord_764028
  simp only [CollatzResearch.WordTrace]
  refine ⟨13933195238032258219510369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18577593650709677626013825 13933195238032258219510369)
  ·
    refine ⟨10449896428524193664632777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13933195238032258219510369 10449896428524193664632777)
    ·
      refine ⟨7837422321393145248474583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10449896428524193664632777 7837422321393145248474583)
      ·
        refine ⟨11756133482089717872711875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7837422321393145248474583 11756133482089717872711875)
        ·
          refine ⟨17634200223134576809067813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11756133482089717872711875 17634200223134576809067813)
          ·
            refine ⟨3306412541837733151700215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17634200223134576809067813 3306412541837733151700215)
            ·
              refine ⟨4959618812756599727550323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3306412541837733151700215 4959618812756599727550323)
              ·
                refine ⟨7439428219134899591325485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4959618812756599727550323 7439428219134899591325485)
                ·
                  refine ⟨2789785582175587346747057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7439428219134899591325485 2789785582175587346747057)
                  ·
                    refine ⟨2092339186631690510060293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2789785582175587346747057 2092339186631690510060293)
                    ·
                      refine ⟨392313597493441970636305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2092339186631690510060293 392313597493441970636305)
                      ·
                        rfl

theorem cell23_764028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_764028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764028 prefixEnd_764028 := by exact prefixLift 764028
  have htrace : WordTrace (prefixWord ++ tailWord_764028) baseStart_764028 baseEnd_764028 := by
    simpa [prefixWord, tailWord_764028, baseEnd_764028] using wordTrace_append hprefix tailTrace_764028
  have hstable : (prefixWord ++ tailWord_764028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764028).length < 2 ^ (prefixWord ++ tailWord_764028).sum := by decide
  have hdescent : baseEnd_764028 < baseStart_764028 := by decide
  rcases family_descends (prefixWord ++ tailWord_764028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764035 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 5]
def baseStart_764035 : Nat := 118140960795 + 764035 * 2 ^ 59
def prefixEnd_764035 : Nat := 4983230072969 + 3 ^ 40 * 764035 * 2
def baseEnd_764035 : Nat := 392317191858023443248773

theorem tailTrace_764035 : CollatzResearch.WordTrace tailWord_764035 prefixEnd_764035 392317191858023443248773 := by
  unfold tailWord_764035
  simp only [CollatzResearch.WordTrace]
  refine ⟨27866645787039156634525559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18577763858026104423017039 27866645787039156634525559)
  ·
    refine ⟨41799968680558734951788339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27866645787039156634525559 41799968680558734951788339)
    ·
      refine ⟨62699953020838102427682509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41799968680558734951788339 62699953020838102427682509)
      ·
        refine ⟨23512482382814288410380941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62699953020838102427682509 23512482382814288410380941)
        ·
          refine ⟨8817180893555358153892853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23512482382814288410380941 8817180893555358153892853)
          ·
            refine ⟨826610708770814826927455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8817180893555358153892853 826610708770814826927455)
            ·
              refine ⟨1239916063156222240391183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826610708770814826927455 1239916063156222240391183)
              ·
                refine ⟨1859874094734333360586775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239916063156222240391183 1859874094734333360586775)
                ·
                  refine ⟨2789811142101500040880163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859874094734333360586775 2789811142101500040880163)
                  ·
                    refine ⟨4184716713152250061320245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2789811142101500040880163 4184716713152250061320245)
                    ·
                      refine ⟨392317191858023443248773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4184716713152250061320245 392317191858023443248773)
                      ·
                        rfl

theorem cell23_764035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_764035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764035 prefixEnd_764035 := by exact prefixLift 764035
  have htrace : WordTrace (prefixWord ++ tailWord_764035) baseStart_764035 baseEnd_764035 := by
    simpa [prefixWord, tailWord_764035, baseEnd_764035] using wordTrace_append hprefix tailTrace_764035
  have hstable : (prefixWord ++ tailWord_764035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764035).length < 2 ^ (prefixWord ++ tailWord_764035).sum := by decide
  have hdescent : baseEnd_764035 < baseStart_764035 := by decide
  rcases family_descends (prefixWord ++ tailWord_764035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764042 : List Nat := [3, 1, 2, 3, 1, 3, 2, 2, 2, 4]
def baseStart_764042 : Nat := 118140960795 + 764042 * 2 ^ 59
def prefixEnd_764042 : Nat := 4983230072969 + 3 ^ 40 * 764042 * 2
def baseEnd_764042 : Nat := 130773595407534971953747

theorem tailTrace_764042 : CollatzResearch.WordTrace tailWord_764042 prefixEnd_764042 130773595407534971953747 := by
  unfold tailWord_764042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6966725274503449207507595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18577934065342531220020253 6966725274503449207507595)
  ·
    refine ⟨10450087911755173811261393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6966725274503449207507595 10450087911755173811261393)
    ·
      refine ⟨7837565933816380358446045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10450087911755173811261393 7837565933816380358446045)
      ·
        refine ⟨2939087225181142634417267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7837565933816380358446045 2939087225181142634417267)
        ·
          refine ⟨4408630837771713951625901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2939087225181142634417267 4408630837771713951625901)
          ·
            refine ⟨1653236564164392731859713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4408630837771713951625901 1653236564164392731859713)
            ·
              refine ⟨1239927423123294548894785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1653236564164392731859713 1239927423123294548894785)
              ·
                refine ⟨929945567342470911671089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239927423123294548894785 929945567342470911671089)
                ·
                  refine ⟨697459175506853183753317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 929945567342470911671089 697459175506853183753317)
                  ·
                    refine ⟨130773595407534971953747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 697459175506853183753317 130773595407534971953747)
                    ·
                      rfl

theorem cell23_764042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_764042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764042 prefixEnd_764042 := by exact prefixLift 764042
  have htrace : WordTrace (prefixWord ++ tailWord_764042) baseStart_764042 baseEnd_764042 := by
    simpa [prefixWord, tailWord_764042, baseEnd_764042] using wordTrace_append hprefix tailTrace_764042
  have hstable : (prefixWord ++ tailWord_764042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764042).length < 2 ^ (prefixWord ++ tailWord_764042).sum := by decide
  have hdescent : baseEnd_764042 < baseStart_764042 := by decide
  rcases family_descends (prefixWord ++ tailWord_764042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764048 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 3]
def baseStart_764048 : Nat := 118140960795 + 764048 * 2 ^ 59
def prefixEnd_764048 : Nat := 4983230072969 + 3 ^ 40 * 764048 * 2
def baseEnd_764048 : Nat := 392323867106531892386213

theorem tailTrace_764048 : CollatzResearch.WordTrace tailWord_764048 prefixEnd_764048 392323867106531892386213 := by
  unfold tailWord_764048
  simp only [CollatzResearch.WordTrace]
  refine ⟨13933559967996029927374399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18578079957328039903165865 13933559967996029927374399)
  ·
    refine ⟨20900339951994044891061599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13933559967996029927374399 20900339951994044891061599)
    ·
      refine ⟨31350509927991067336592399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20900339951994044891061599 31350509927991067336592399)
      ·
        refine ⟨47025764891986601004888599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31350509927991067336592399 47025764891986601004888599)
        ·
          refine ⟨70538647337979901507332899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47025764891986601004888599 70538647337979901507332899)
          ·
            refine ⟨105807971006969852260999349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70538647337979901507332899 105807971006969852260999349)
            ·
              refine ⟨9919497281903423649468689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105807971006969852260999349 9919497281903423649468689)
              ·
                refine ⟨7439622961427567737101517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9919497281903423649468689 7439622961427567737101517)
                ·
                  refine ⟨2789858610535337901413069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7439622961427567737101517 2789858610535337901413069)
                  ·
                    refine ⟨1046196978950751713029901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2789858610535337901413069 1046196978950751713029901)
                    ·
                      refine ⟨392323867106531892386213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1046196978950751713029901 392323867106531892386213)
                      ·
                        rfl

theorem cell23_764048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 3].length) (baseStart_764048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764048 prefixEnd_764048 := by exact prefixLift 764048
  have htrace : WordTrace (prefixWord ++ tailWord_764048) baseStart_764048 baseEnd_764048 := by
    simpa [prefixWord, tailWord_764048, baseEnd_764048] using wordTrace_append hprefix tailTrace_764048
  have hstable : (prefixWord ++ tailWord_764048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764048).length < 2 ^ (prefixWord ++ tailWord_764048).sum := by decide
  have hdescent : baseEnd_764048 < baseStart_764048 := by decide
  rcases family_descends (prefixWord ++ tailWord_764048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764055 : List Nat := [1, 1, 3, 3, 4, 2, 1, 8]
def baseStart_764055 : Nat := 118140960795 + 764055 * 2 ^ 59
def prefixEnd_764055 : Nat := 4983230072969 + 3 ^ 40 * 764055 * 2
def baseEnd_764055 : Nat := 14530646721152346851803

theorem tailTrace_764055 : CollatzResearch.WordTrace tailWord_764055 prefixEnd_764055 14530646721152346851803 := by
  unfold tailWord_764055
  simp only [CollatzResearch.WordTrace]
  refine ⟨27867375246966700050253619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18578250164644466700169079 27867375246966700050253619)
  ·
    refine ⟨41801062870450050075380429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27867375246966700050253619 41801062870450050075380429)
    ·
      refine ⟨15675398576418768778267661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41801062870450050075380429 15675398576418768778267661)
      ·
        refine ⟨5878274466157038291850373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15675398576418768778267661 5878274466157038291850373)
        ·
          refine ⟨1102176462404444679721945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5878274466157038291850373 1102176462404444679721945)
          ·
            refine ⟨826632346803333509791459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1102176462404444679721945 826632346803333509791459)
            ·
              refine ⟨1239948520205000264687189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826632346803333509791459 1239948520205000264687189)
              ·
                refine ⟨14530646721152346851803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1239948520205000264687189 14530646721152346851803)
                ·
                  rfl

theorem cell23_764055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 8].length) (baseStart_764055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764055 prefixEnd_764055 := by exact prefixLift 764055
  have htrace : WordTrace (prefixWord ++ tailWord_764055) baseStart_764055 baseEnd_764055 := by
    simpa [prefixWord, tailWord_764055, baseEnd_764055] using wordTrace_append hprefix tailTrace_764055
  have hstable : (prefixWord ++ tailWord_764055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764055).length < 2 ^ (prefixWord ++ tailWord_764055).sum := by decide
  have hdescent : baseEnd_764055 < baseStart_764055 := by decide
  rcases family_descends (prefixWord ++ tailWord_764055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764065 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_764065 : Nat := 118140960795 + 764065 * 2 ^ 59
def prefixEnd_764065 : Nat := 4983230072969 + 3 ^ 40 * 764065 * 2
def baseEnd_764065 : Nat := 392332596277658325873635

theorem tailTrace_764065 : CollatzResearch.WordTrace tailWord_764065 prefixEnd_764065 392332596277658325873635 := by
  unfold tailWord_764065
  simp only [CollatzResearch.WordTrace]
  refine ⟨27867739976930471758117649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18578493317953647838745099 27867739976930471758117649)
  ·
    refine ⟨20900804982697853818588237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27867739976930471758117649 20900804982697853818588237)
    ·
      refine ⟨7837801868511695181970589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20900804982697853818588237 7837801868511695181970589)
      ·
        refine ⟨2939175700691885693238971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7837801868511695181970589 2939175700691885693238971)
        ·
          refine ⟨4408763551037828539858457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2939175700691885693238971 4408763551037828539858457)
          ·
            refine ⟨3306572663278371404893843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4408763551037828539858457 3306572663278371404893843)
            ·
              refine ⟨4959858994917557107340765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3306572663278371404893843 4959858994917557107340765)
              ·
                refine ⟨1859947123094083915252787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4959858994917557107340765 1859947123094083915252787)
                ·
                  refine ⟨2789920684641125872879181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859947123094083915252787 2789920684641125872879181)
                  ·
                    refine ⟨1046220256740422202329693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2789920684641125872879181 1046220256740422202329693)
                    ·
                      refine ⟨392332596277658325873635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1046220256740422202329693 392332596277658325873635)
                      ·
                        rfl

theorem cell23_764065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_764065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764065 prefixEnd_764065 := by exact prefixLift 764065
  have htrace : WordTrace (prefixWord ++ tailWord_764065) baseStart_764065 baseEnd_764065 := by
    simpa [prefixWord, tailWord_764065, baseEnd_764065] using wordTrace_append hprefix tailTrace_764065
  have hstable : (prefixWord ++ tailWord_764065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764065).length < 2 ^ (prefixWord ++ tailWord_764065).sum := by decide
  have hdescent : baseEnd_764065 < baseStart_764065 := by decide
  rcases family_descends (prefixWord ++ tailWord_764065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764122 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2]
def baseStart_764122 : Nat := 118140960795 + 764122 * 2 ^ 59
def prefixEnd_764122 : Nat := 4983230072969 + 3 ^ 40 * 764122 * 2
def baseEnd_764122 : Nat := 392361864674964602860873

theorem tailTrace_764122 : CollatzResearch.WordTrace tailWord_764122 prefixEnd_764122 392361864674964602860873 := by
  unfold tailWord_764122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6967454734430992623235655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18579879291815980328628413 6967454734430992623235655)
  ·
    refine ⟨10451182101646488934853483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6967454734430992623235655 10451182101646488934853483)
    ·
      refine ⟨15676773152469733402280225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10451182101646488934853483 15676773152469733402280225)
      ·
        refine ⟨11757579864352300051710169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15676773152469733402280225 11757579864352300051710169)
        ·
          refine ⟨8818184898264225038782627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11757579864352300051710169 8818184898264225038782627)
          ·
            refine ⟨13227277347396337558173941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8818184898264225038782627 13227277347396337558173941)
            ·
              refine ⟨1240057251318406646078807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13227277347396337558173941 1240057251318406646078807)
              ·
                refine ⟨1860085876977609969118211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1240057251318406646078807 1860085876977609969118211)
                ·
                  refine ⟨2790128815466414953677317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1860085876977609969118211 2790128815466414953677317)
                  ·
                    refine ⟨523149152899952803814497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2790128815466414953677317 523149152899952803814497)
                    ·
                      refine ⟨392361864674964602860873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 523149152899952803814497 392361864674964602860873)
                      ·
                        rfl

theorem cell23_764122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_764122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764122 prefixEnd_764122 := by exact prefixLift 764122
  have htrace : WordTrace (prefixWord ++ tailWord_764122) baseStart_764122 baseEnd_764122 := by
    simpa [prefixWord, tailWord_764122, baseEnd_764122] using wordTrace_append hprefix tailTrace_764122
  have hstable : (prefixWord ++ tailWord_764122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764122).length < 2 ^ (prefixWord ++ tailWord_764122).sum := by decide
  have hdescent : baseEnd_764122 < baseStart_764122 := by decide
  rcases family_descends (prefixWord ++ tailWord_764122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764128 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 7]
def baseStart_764128 : Nat := 118140960795 + 764128 * 2 ^ 59
def prefixEnd_764128 : Nat := 4983230072969 + 3 ^ 40 * 764128 * 2
def baseEnd_764128 : Nat := 43596105062099064376205

theorem tailTrace_764128 : CollatzResearch.WordTrace tailWord_764128 prefixEnd_764128 43596105062099064376205 := by
  unfold tailWord_764128
  simp only [CollatzResearch.WordTrace]
  refine ⟨13935018887851116758830519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18580025183801489011774025 13935018887851116758830519)
  ·
    refine ⟨20902528331776675138245779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13935018887851116758830519 20902528331776675138245779)
    ·
      refine ⟨31353792497665012707368669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20902528331776675138245779 31353792497665012707368669)
      ·
        refine ⟨11757672186624379765263251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31353792497665012707368669 11757672186624379765263251)
        ·
          refine ⟨17636508279936569647894877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11757672186624379765263251 17636508279936569647894877)
          ·
            refine ⟨6613690604976213617960579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17636508279936569647894877 6613690604976213617960579)
            ·
              refine ⟨9920535907464320426940869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6613690604976213617960579 9920535907464320426940869)
              ·
                refine ⟨1860100482649560080051413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9920535907464320426940869 1860100482649560080051413)
                ·
                  refine ⟨43596105062099064376205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1860100482649560080051413 43596105062099064376205)
                  ·
                    rfl

theorem cell23_764128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 7].length) (baseStart_764128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764128 prefixEnd_764128 := by exact prefixLift 764128
  have htrace : WordTrace (prefixWord ++ tailWord_764128) baseStart_764128 baseEnd_764128 := by
    simpa [prefixWord, tailWord_764128, baseEnd_764128] using wordTrace_append hprefix tailTrace_764128
  have hstable : (prefixWord ++ tailWord_764128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764128).length < 2 ^ (prefixWord ++ tailWord_764128).sum := by decide
  have hdescent : baseEnd_764128 < baseStart_764128 := by decide
  rcases family_descends (prefixWord ++ tailWord_764128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764162 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 7]
def baseStart_764162 : Nat := 118140960795 + 764162 * 2 ^ 59
def prefixEnd_764162 : Nat := 4983230072969 + 3 ^ 40 * 764162 * 2
def baseEnd_764162 : Nat := 43598044877904938484521

theorem tailTrace_764162 : CollatzResearch.WordTrace tailWord_764162 prefixEnd_764162 43598044877904938484521 := by
  unfold tailWord_764162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6967819464394764331099685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18580851905052704882932493 6967819464394764331099685)
  ·
    refine ⟨1306466149574018312081191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6967819464394764331099685 1306466149574018312081191)
    ·
      refine ⟨1959699224361027468121787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1306466149574018312081191 1959699224361027468121787)
      ·
        refine ⟨2939548836541541202182681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1959699224361027468121787 2939548836541541202182681)
        ·
          refine ⟨2204661627406155901637011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2939548836541541202182681 2204661627406155901637011)
          ·
            refine ⟨3306992441109233852455517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204661627406155901637011 3306992441109233852455517)
            ·
              refine ⟨1240122165415962694670819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3306992441109233852455517 1240122165415962694670819)
              ·
                refine ⟨1860183248123944042006229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1240122165415962694670819 1860183248123944042006229)
                ·
                  refine ⟨43598044877904938484521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1860183248123944042006229 43598044877904938484521)
                  ·
                    rfl

theorem cell23_764162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_764162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764162 prefixEnd_764162 := by exact prefixLift 764162
  have htrace : WordTrace (prefixWord ++ tailWord_764162) baseStart_764162 baseEnd_764162 := by
    simpa [prefixWord, tailWord_764162, baseEnd_764162] using wordTrace_append hprefix tailTrace_764162
  have hstable : (prefixWord ++ tailWord_764162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764162).length < 2 ^ (prefixWord ++ tailWord_764162).sum := by decide
  have hdescent : baseEnd_764162 < baseStart_764162 := by decide
  rcases family_descends (prefixWord ++ tailWord_764162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764192 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 2, 5]
def baseStart_764192 : Nat := 118140960795 + 764192 * 2 ^ 59
def prefixEnd_764192 : Nat := 4983230072969 + 3 ^ 40 * 764192 * 2
def baseEnd_764192 : Nat := 130799269440259776328517

theorem tailTrace_764192 : CollatzResearch.WordTrace tailWord_764192 prefixEnd_764192 130799269440259776328517 := by
  unfold tailWord_764192
  simp only [CollatzResearch.WordTrace]
  refine ⟨13936186023735186223995415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18581581364980248298660553 13936186023735186223995415)
  ·
    refine ⟨20904279035602779335993123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13936186023735186223995415 20904279035602779335993123)
    ·
      refine ⟨31356418553404169003989685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20904279035602779335993123 31356418553404169003989685)
      ·
        refine ⟨2939664239381640844124033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31356418553404169003989685 2939664239381640844124033)
        ·
          refine ⟨2204748179536230633093025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2939664239381640844124033 2204748179536230633093025)
          ·
            refine ⟨1653561134652172974819769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2204748179536230633093025 1653561134652172974819769)
            ·
              refine ⟨1240170850989129731114827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1653561134652172974819769 1240170850989129731114827)
              ·
                refine ⟨1860256276483694596672241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1240170850989129731114827 1860256276483694596672241)
                ·
                  refine ⟨1395192207362770947504181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1860256276483694596672241 1395192207362770947504181)
                  ·
                    refine ⟨130799269440259776328517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1395192207362770947504181 130799269440259776328517)
                    ·
                      rfl

theorem cell23_764192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 2, 5].length) (baseStart_764192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764192 prefixEnd_764192 := by exact prefixLift 764192
  have htrace : WordTrace (prefixWord ++ tailWord_764192) baseStart_764192 baseEnd_764192 := by
    simpa [prefixWord, tailWord_764192, baseEnd_764192] using wordTrace_append hprefix tailTrace_764192
  have hstable : (prefixWord ++ tailWord_764192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764192).length < 2 ^ (prefixWord ++ tailWord_764192).sum := by decide
  have hdescent : baseEnd_764192 < baseStart_764192 := by decide
  rcases family_descends (prefixWord ++ tailWord_764192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764256 : List Nat := [2, 1, 1, 3, 5, 1, 2, 3, 1, 4]
def baseStart_764256 : Nat := 118140960795 + 764256 * 2 ^ 59
def prefixEnd_764256 : Nat := 4983230072969 + 3 ^ 40 * 764256 * 2
def baseEnd_764256 : Nat := 130810223694222359528419

theorem tailTrace_764256 : CollatzResearch.WordTrace tailWord_764256 prefixEnd_764256 130810223694222359528419 := by
  unfold tailWord_764256
  simp only [CollatzResearch.WordTrace]
  refine ⟨13937353159619255689160311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18583137546159007585547081 13937353159619255689160311)
  ·
    refine ⟨20906029739428883533740467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13937353159619255689160311 20906029739428883533740467)
    ·
      refine ⟨31359044609143325300610701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20906029739428883533740467 31359044609143325300610701)
      ·
        refine ⟨11759641728428746987729013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31359044609143325300610701 11759641728428746987729013)
        ·
          refine ⟨1102466412040195030099595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11759641728428746987729013 1102466412040195030099595)
          ·
            refine ⟨1653699618060292545149393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102466412040195030099595 1653699618060292545149393)
            ·
              refine ⟨1240274713545219408862045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1653699618060292545149393 1240274713545219408862045)
              ·
                refine ⟨465103017579457278323267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1240274713545219408862045 465103017579457278323267)
                ·
                  refine ⟨697654526369185917484901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465103017579457278323267 697654526369185917484901)
                  ·
                    refine ⟨130810223694222359528419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 697654526369185917484901 130810223694222359528419)
                    ·
                      rfl

theorem cell23_764256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 1, 4].length) (baseStart_764256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764256 prefixEnd_764256 := by exact prefixLift 764256
  have htrace : WordTrace (prefixWord ++ tailWord_764256) baseStart_764256 baseEnd_764256 := by
    simpa [prefixWord, tailWord_764256, baseEnd_764256] using wordTrace_append hprefix tailTrace_764256
  have hstable : (prefixWord ++ tailWord_764256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764256).length < 2 ^ (prefixWord ++ tailWord_764256).sum := by decide
  have hdescent : baseEnd_764256 < baseStart_764256 := by decide
  rcases family_descends (prefixWord ++ tailWord_764256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764289 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_764289 : Nat := 118140960795 + 764289 * 2 ^ 59
def prefixEnd_764289 : Nat := 4983230072969 + 3 ^ 40 * 764289 * 2
def baseEnd_764289 : Nat := 392447615944265449472605

theorem tailTrace_764289 : CollatzResearch.WordTrace tailWord_764289 prefixEnd_764289 392447615944265449472605 := by
  unfold tailWord_764289
  simp only [CollatzResearch.WordTrace]
  refine ⟨27875909928118958014271921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18583939952079305342847947 27875909928118958014271921)
  ·
    refine ⟨20906932446089218510703941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27875909928118958014271921 20906932446089218510703941)
    ·
      refine ⟨3920049833641728470756989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20906932446089218510703941 3920049833641728470756989)
      ·
        refine ⟨1470018687615648176533871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3920049833641728470756989 1470018687615648176533871)
        ·
          refine ⟨2205028031423472264800807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470018687615648176533871 2205028031423472264800807)
          ·
            refine ⟨3307542047135208397201211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205028031423472264800807 3307542047135208397201211)
            ·
              refine ⟨4961313070702812595801817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3307542047135208397201211 4961313070702812595801817)
              ·
                refine ⟨3720984803027109446851363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4961313070702812595801817 3720984803027109446851363)
                ·
                  refine ⟨5581477204540664170277045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3720984803027109446851363 5581477204540664170277045)
                  ·
                    refine ⟨523263487925687265963473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5581477204540664170277045 523263487925687265963473)
                    ·
                      refine ⟨392447615944265449472605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 523263487925687265963473 392447615944265449472605)
                      ·
                        rfl

theorem cell23_764289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_764289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764289 prefixEnd_764289 := by exact prefixLift 764289
  have htrace : WordTrace (prefixWord ++ tailWord_764289) baseStart_764289 baseEnd_764289 := by
    simpa [prefixWord, tailWord_764289, baseEnd_764289] using wordTrace_append hprefix tailTrace_764289
  have hstable : (prefixWord ++ tailWord_764289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764289).length < 2 ^ (prefixWord ++ tailWord_764289).sum := by decide
  have hdescent : baseEnd_764289 < baseStart_764289 := by decide
  rcases family_descends (prefixWord ++ tailWord_764289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764352 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 3]
def baseStart_764352 : Nat := 118140960795 + 764352 * 2 ^ 59
def prefixEnd_764352 : Nat := 4983230072969 + 3 ^ 40 * 764352 * 2
def baseEnd_764352 : Nat := 392479965225498702984815

theorem tailTrace_764352 : CollatzResearch.WordTrace tailWord_764352 prefixEnd_764352 392479965225498702984815 := by
  unfold tailWord_764352
  simp only [CollatzResearch.WordTrace]
  refine ⟨13939103863445359886907655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18585471817927146515876873 13939103863445359886907655)
  ·
    refine ⟨20908655795168039830361483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13939103863445359886907655 20908655795168039830361483)
    ·
      refine ⟨31362983692752059745542225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20908655795168039830361483 31362983692752059745542225)
      ·
        refine ⟨23522237769564044809156669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31362983692752059745542225 23522237769564044809156669)
        ·
          refine ⟨8820839163586516803433751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23522237769564044809156669 8820839163586516803433751)
          ·
            refine ⟨13231258745379775205150627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8820839163586516803433751 13231258745379775205150627)
            ·
              refine ⟨19846888118069662807725941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13231258745379775205150627 19846888118069662807725941)
              ·
                refine ⟨1860645761069030888224307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19846888118069662807725941 1860645761069030888224307)
                ·
                  refine ⟨2790968641603546332336461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1860645761069030888224307 2790968641603546332336461)
                  ·
                    refine ⟨1046613240601329874626173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2790968641603546332336461 1046613240601329874626173)
                    ·
                      refine ⟨392479965225498702984815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1046613240601329874626173 392479965225498702984815)
                      ·
                        rfl

theorem cell23_764352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_764352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764352 prefixEnd_764352 := by exact prefixLift 764352
  have htrace : WordTrace (prefixWord ++ tailWord_764352) baseStart_764352 baseEnd_764352 := by
    simpa [prefixWord, tailWord_764352, baseEnd_764352] using wordTrace_append hprefix tailTrace_764352
  have hstable : (prefixWord ++ tailWord_764352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764352).length < 2 ^ (prefixWord ++ tailWord_764352).sum := by decide
  have hdescent : baseEnd_764352 < baseStart_764352 := by decide
  rcases family_descends (prefixWord ++ tailWord_764352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764353 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_764353 : Nat := 118140960795 + 764353 * 2 ^ 59
def prefixEnd_764353 : Nat := 4983230072969 + 3 ^ 40 * 764353 * 2
def baseEnd_764353 : Nat := 392480478706153199072311

theorem tailTrace_764353 : CollatzResearch.WordTrace tailWord_764353 prefixEnd_764353 392480478706153199072311 := by
  unfold tailWord_764353
  simp only [CollatzResearch.WordTrace]
  refine ⟨27878244199887096944601713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18585496133258064629734475 27878244199887096944601713)
  ·
    refine ⟨20908683149915322708451285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27878244199887096944601713 20908683149915322708451285)
    ·
      refine ⟨490047261326140375979327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 20908683149915322708451285 490047261326140375979327)
      ·
        refine ⟨735070891989210563968991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490047261326140375979327 735070891989210563968991)
        ·
          refine ⟨1102606337983815845953487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735070891989210563968991 1102606337983815845953487)
          ·
            refine ⟨1653909506975723768930231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102606337983815845953487 1653909506975723768930231)
            ·
              refine ⟨2480864260463585653395347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653909506975723768930231 2480864260463585653395347)
              ·
                refine ⟨3721296390695378480093021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480864260463585653395347 3721296390695378480093021)
                ·
                  refine ⟨1395486146510766930034883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3721296390695378480093021 1395486146510766930034883)
                  ·
                    refine ⟨2093229219766150395052325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1395486146510766930034883 2093229219766150395052325)
                    ·
                      refine ⟨392480478706153199072311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2093229219766150395052325 392480478706153199072311)
                      ·
                        rfl

theorem cell23_764353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_764353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764353 prefixEnd_764353 := by exact prefixLift 764353
  have htrace : WordTrace (prefixWord ++ tailWord_764353) baseStart_764353 baseEnd_764353 := by
    simpa [prefixWord, tailWord_764353, baseEnd_764353] using wordTrace_append hprefix tailTrace_764353
  have hstable : (prefixWord ++ tailWord_764353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764353).length < 2 ^ (prefixWord ++ tailWord_764353).sum := by decide
  have hdescent : baseEnd_764353 < baseStart_764353 := by decide
  rcases family_descends (prefixWord ++ tailWord_764353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764356 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_764356 : Nat := 118140960795 + 764356 * 2 ^ 59
def prefixEnd_764356 : Nat := 4983230072969 + 3 ^ 40 * 764356 * 2
def baseEnd_764356 : Nat := 392482019148116687334797

theorem tailTrace_764356 : CollatzResearch.WordTrace tailWord_764356 prefixEnd_764356 392482019148116687334797 := by
  unfold tailWord_764356
  simp only [CollatzResearch.WordTrace]
  refine ⟨13939176809438114228480461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18585569079250818971307281 13939176809438114228480461)
  ·
    refine ⟨5227191303539292835680173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13939176809438114228480461 5227191303539292835680173)
    ·
      refine ⟨1960196738827234813380065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5227191303539292835680173 1960196738827234813380065)
      ·
        refine ⟨1470147554120426110035049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1960196738827234813380065 1470147554120426110035049)
        ·
          refine ⟨1102610665590319582526287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1470147554120426110035049 1102610665590319582526287)
          ·
            refine ⟨1653915998385479373789431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102610665590319582526287 1653915998385479373789431)
            ·
              refine ⟨2480873997578219060684147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653915998385479373789431 2480873997578219060684147)
              ·
                refine ⟨3721310996367328591026221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480873997578219060684147 3721310996367328591026221)
                ·
                  refine ⟨1395491623637748221634833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3721310996367328591026221 1395491623637748221634833)
                  ·
                    refine ⟨1046618717728311166226125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1395491623637748221634833 1046618717728311166226125)
                    ·
                      refine ⟨392482019148116687334797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1046618717728311166226125 392482019148116687334797)
                      ·
                        rfl

theorem cell23_764356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_764356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764356 prefixEnd_764356 := by exact prefixLift 764356
  have htrace : WordTrace (prefixWord ++ tailWord_764356) baseStart_764356 baseEnd_764356 := by
    simpa [prefixWord, tailWord_764356, baseEnd_764356] using wordTrace_append hprefix tailTrace_764356
  have hstable : (prefixWord ++ tailWord_764356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764356).length < 2 ^ (prefixWord ++ tailWord_764356).sum := by decide
  have hdescent : baseEnd_764356 < baseStart_764356 := by decide
  rcases family_descends (prefixWord ++ tailWord_764356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764387 : List Nat := [1, 1, 1, 6, 3, 2, 2, 2, 1, 2, 2]
def baseStart_764387 : Nat := 118140960795 + 764387 * 2 ^ 59
def prefixEnd_764387 : Nat := 4983230072969 + 3 ^ 40 * 764387 * 2
def baseEnd_764387 : Nat := 392497937048406066047155

theorem tailTrace_764387 : CollatzResearch.WordTrace tailWord_764387 prefixEnd_764387 392497937048406066047155 := by
  unfold tailWord_764387
  simp only [CollatzResearch.WordTrace]
  refine ⟨27879484281763920751339415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18586322854509280500892943 27879484281763920751339415)
  ·
    refine ⟨41819226422645881127009123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27879484281763920751339415 41819226422645881127009123)
    ·
      refine ⟨62728839633968821690513685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41819226422645881127009123 62728839633968821690513685)
      ·
        refine ⟨2940414357842288516742829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62728839633968821690513685 2940414357842288516742829)
        ·
          refine ⟨1102655384190858193778561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2940414357842288516742829 1102655384190858193778561)
          ·
            refine ⟨826991538143143645333921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1102655384190858193778561 826991538143143645333921)
            ·
              refine ⟨620243653607357734000441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826991538143143645333921 620243653607357734000441)
              ·
                refine ⟨465182740205518300500331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620243653607357734000441 465182740205518300500331)
                ·
                  refine ⟨697774110308277450750497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465182740205518300500331 697774110308277450750497)
                  ·
                    refine ⟨523330582731208088062873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 697774110308277450750497 523330582731208088062873)
                    ·
                      refine ⟨392497937048406066047155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 523330582731208088062873 392497937048406066047155)
                      ·
                        rfl

theorem cell23_764387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_764387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764387 prefixEnd_764387 := by exact prefixLift 764387
  have htrace : WordTrace (prefixWord ++ tailWord_764387) baseStart_764387 baseEnd_764387 := by
    simpa [prefixWord, tailWord_764387, baseEnd_764387] using wordTrace_append hprefix tailTrace_764387
  have hstable : (prefixWord ++ tailWord_764387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764387).length < 2 ^ (prefixWord ++ tailWord_764387).sum := by decide
  have hdescent : baseEnd_764387 < baseStart_764387 := by decide
  rcases family_descends (prefixWord ++ tailWord_764387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764392 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_764392 : Nat := 118140960795 + 764392 * 2 ^ 59
def prefixEnd_764392 : Nat := 4983230072969 + 3 ^ 40 * 764392 * 2
def baseEnd_764392 : Nat := 392500504451678546484631

theorem tailTrace_764392 : CollatzResearch.WordTrace tailWord_764392 prefixEnd_764392 392500504451678546484631 := by
  unfold tailWord_764392
  simp only [CollatzResearch.WordTrace]
  refine ⟨13939833323372903302635715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18586444431163871070180953 13939833323372903302635715)
  ·
    refine ⟨20909749985059354953953573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13939833323372903302635715 20909749985059354953953573)
    ·
      refine ⟨3920578122198629053866295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20909749985059354953953573 3920578122198629053866295)
      ·
        refine ⟨5880867183297943580799443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3920578122198629053866295 5880867183297943580799443)
        ·
          refine ⟨8821300774946915371199165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5880867183297943580799443 8821300774946915371199165)
          ·
            refine ⟨3307987790605093264199687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8821300774946915371199165 3307987790605093264199687)
            ·
              refine ⟨4961981685907639896299531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3307987790605093264199687 4961981685907639896299531)
              ·
                refine ⟨7442972528861459844449297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4961981685907639896299531 7442972528861459844449297)
                ·
                  refine ⟨5582229396646094883336973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7442972528861459844449297 5582229396646094883336973)
                  ·
                    refine ⟨2093336023742285581251365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5582229396646094883336973 2093336023742285581251365)
                    ·
                      refine ⟨392500504451678546484631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2093336023742285581251365 392500504451678546484631)
                      ·
                        rfl

theorem cell23_764392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_764392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764392 prefixEnd_764392 := by exact prefixLift 764392
  have htrace : WordTrace (prefixWord ++ tailWord_764392) baseStart_764392 baseEnd_764392 := by
    simpa [prefixWord, tailWord_764392, baseEnd_764392] using wordTrace_append hprefix tailTrace_764392
  have hstable : (prefixWord ++ tailWord_764392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764392).length < 2 ^ (prefixWord ++ tailWord_764392).sum := by decide
  have hdescent : baseEnd_764392 < baseStart_764392 := by decide
  rcases family_descends (prefixWord ++ tailWord_764392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764409 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 1, 4, 2]
def baseStart_764409 : Nat := 118140960795 + 764409 * 2 ^ 59
def prefixEnd_764409 : Nat := 4983230072969 + 3 ^ 40 * 764409 * 2
def baseEnd_764409 : Nat := 392509233622804979972053

theorem tailTrace_764409 : CollatzResearch.WordTrace tailWord_764409 prefixEnd_764409 392509233622804979972053 := by
  unfold tailWord_764409
  simp only [CollatzResearch.WordTrace]
  refine ⟨27880286687684218508640281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18586857791789479005760187 27880286687684218508640281)
  ·
    refine ⟨20910215015763163881480211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27880286687684218508640281 20910215015763163881480211)
    ·
      refine ⟨31365322523644745822220317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20910215015763163881480211 31365322523644745822220317)
      ·
        refine ⟨11761995946366779683332619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31365322523644745822220317 11761995946366779683332619)
        ·
          refine ⟨17642993919550169524998929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11761995946366779683332619 17642993919550169524998929)
          ·
            refine ⟨13232245439662627143749197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17642993919550169524998929 13232245439662627143749197)
            ·
              refine ⟨4962092039873485178905949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13232245439662627143749197 4962092039873485178905949)
              ·
                refine ⟨1860784514952556942089731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4962092039873485178905949 1860784514952556942089731)
                ·
                  refine ⟨2791176772428835413134597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1860784514952556942089731 2791176772428835413134597)
                  ·
                    refine ⟨523345644830406639962737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2791176772428835413134597 523345644830406639962737)
                    ·
                      refine ⟨392509233622804979972053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 523345644830406639962737 392509233622804979972053)
                      ·
                        rfl

theorem cell23_764409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_764409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764409 prefixEnd_764409 := by exact prefixLift 764409
  have htrace : WordTrace (prefixWord ++ tailWord_764409) baseStart_764409 baseEnd_764409 := by
    simpa [prefixWord, tailWord_764409, baseEnd_764409] using wordTrace_append hprefix tailTrace_764409
  have hstable : (prefixWord ++ tailWord_764409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764409).length < 2 ^ (prefixWord ++ tailWord_764409).sum := by decide
  have hdescent : baseEnd_764409 < baseStart_764409 := by decide
  rcases family_descends (prefixWord ++ tailWord_764409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764412 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_764412 : Nat := 118140960795 + 764412 * 2 ^ 59
def prefixEnd_764412 : Nat := 4983230072969 + 3 ^ 40 * 764412 * 2
def baseEnd_764412 : Nat := 392510774064768468234539

theorem tailTrace_764412 : CollatzResearch.WordTrace tailWord_764412 prefixEnd_764412 392510774064768468234539 := by
  unfold tailWord_764412
  simp only [CollatzResearch.WordTrace]
  refine ⟨13940198053336675010499745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18586930737782233347332993 13940198053336675010499745)
  ·
    refine ⟨10455148540002506257874809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13940198053336675010499745 10455148540002506257874809)
    ·
      refine ⟨7841361405001879693406107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10455148540002506257874809 7841361405001879693406107)
      ·
        refine ⟨11762042107502819540109161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7841361405001879693406107 11762042107502819540109161)
        ·
          refine ⟨8821531580627114655081871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11762042107502819540109161 8821531580627114655081871)
          ·
            refine ⟨13232297370940671982622807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8821531580627114655081871 13232297370940671982622807)
            ·
              refine ⟨19848446056411007973934211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13232297370940671982622807 19848446056411007973934211)
              ·
                refine ⟨29772669084616511960901317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19848446056411007973934211 29772669084616511960901317)
                ·
                  refine ⟨5582375453365595992668997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29772669084616511960901317 5582375453365595992668997)
                  ·
                    refine ⟨1046695397506049248625437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5582375453365595992668997 1046695397506049248625437)
                    ·
                      refine ⟨392510774064768468234539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1046695397506049248625437 392510774064768468234539)
                      ·
                        rfl

theorem cell23_764412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_764412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764412 prefixEnd_764412 := by exact prefixLift 764412
  have htrace : WordTrace (prefixWord ++ tailWord_764412) baseStart_764412 baseEnd_764412 := by
    simpa [prefixWord, tailWord_764412, baseEnd_764412] using wordTrace_append hprefix tailTrace_764412
  have hstable : (prefixWord ++ tailWord_764412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764412).length < 2 ^ (prefixWord ++ tailWord_764412).sum := by decide
  have hdescent : baseEnd_764412 < baseStart_764412 := by decide
  rcases family_descends (prefixWord ++ tailWord_764412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764426 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2]
def baseStart_764426 : Nat := 118140960795 + 764426 * 2 ^ 59
def prefixEnd_764426 : Nat := 4983230072969 + 3 ^ 40 * 764426 * 2
def baseEnd_764426 : Nat := 392517962793931413459475

theorem tailTrace_764426 : CollatzResearch.WordTrace tailWord_764426 prefixEnd_764426 392517962793931413459475 := by
  unfold tailWord_764426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6970226682155657603002283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18587271152415086941339421 6970226682155657603002283)
  ·
    refine ⟨10455340023233486404503425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6970226682155657603002283 10455340023233486404503425)
    ·
      refine ⟨7841505017425114803377569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10455340023233486404503425 7841505017425114803377569)
      ·
        refine ⟨5881128763068836102533177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7841505017425114803377569 5881128763068836102533177)
        ·
          refine ⟨4410846572301627076899883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5881128763068836102533177 4410846572301627076899883)
          ·
            refine ⟨6616269858452440615349825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410846572301627076899883 6616269858452440615349825)
            ·
              refine ⟨4962202393839330461512369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6616269858452440615349825 4962202393839330461512369)
              ·
                refine ⟨3721651795379497846134277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4962202393839330461512369 3721651795379497846134277)
                ·
                  refine ⟨697809711633655846150177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3721651795379497846134277 697809711633655846150177)
                  ·
                    refine ⟨523357283725241884612633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 697809711633655846150177 523357283725241884612633)
                    ·
                      refine ⟨392517962793931413459475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 523357283725241884612633 392517962793931413459475)
                      ·
                        rfl

theorem cell23_764426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_764426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764426 prefixEnd_764426 := by exact prefixLift 764426
  have htrace : WordTrace (prefixWord ++ tailWord_764426) baseStart_764426 baseEnd_764426 := by
    simpa [prefixWord, tailWord_764426, baseEnd_764426] using wordTrace_append hprefix tailTrace_764426
  have hstable : (prefixWord ++ tailWord_764426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764426).length < 2 ^ (prefixWord ++ tailWord_764426).sum := by decide
  have hdescent : baseEnd_764426 < baseStart_764426 := by decide
  rcases family_descends (prefixWord ++ tailWord_764426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764430 : List Nat := [4, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2]
def baseStart_764430 : Nat := 118140960795 + 764430 * 2 ^ 59
def prefixEnd_764430 : Nat := 4983230072969 + 3 ^ 40 * 764430 * 2
def baseEnd_764430 : Nat := 392520016716549397809457

theorem tailTrace_764430 : CollatzResearch.WordTrace tailWord_764430 prefixEnd_764430 392520016716549397809457 := by
  unfold tailWord_764430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3485131577576017386894343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18587368413738759396769829 3485131577576017386894343)
  ·
    refine ⟨5227697366364026080341515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3485131577576017386894343 5227697366364026080341515)
    ·
      refine ⟨7841546049546039120512273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5227697366364026080341515 7841546049546039120512273)
      ·
        refine ⟨5881159537159529340384205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7841546049546039120512273 5881159537159529340384205)
        ·
          refine ⟨2205434826434823502644077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5881159537159529340384205 2205434826434823502644077)
          ·
            refine ⟨827038059913058813491529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2205434826434823502644077 827038059913058813491529)
            ·
              refine ⟨620278544934794110118647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827038059913058813491529 620278544934794110118647)
              ·
                refine ⟨930417817402191165177971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620278544934794110118647 930417817402191165177971)
                ·
                  refine ⟨1395626726103286747766957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930417817402191165177971 1395626726103286747766957)
                  ·
                    refine ⟨523360022288732530412609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1395626726103286747766957 523360022288732530412609)
                    ·
                      refine ⟨392520016716549397809457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 523360022288732530412609 392520016716549397809457)
                      ·
                        rfl

theorem cell23_764430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_764430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764430 prefixEnd_764430 := by exact prefixLift 764430
  have htrace : WordTrace (prefixWord ++ tailWord_764430) baseStart_764430 baseEnd_764430 := by
    simpa [prefixWord, tailWord_764430, baseEnd_764430] using wordTrace_append hprefix tailTrace_764430
  have hstable : (prefixWord ++ tailWord_764430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764430).length < 2 ^ (prefixWord ++ tailWord_764430).sum := by decide
  have hdescent : baseEnd_764430 < baseStart_764430 := by decide
  rcases family_descends (prefixWord ++ tailWord_764430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764449 : List Nat := [1, 2, 3, 2, 2, 1, 1, 6, 5]
def baseStart_764449 : Nat := 118140960795 + 764449 * 2 ^ 59
def prefixEnd_764449 : Nat := 4983230072969 + 3 ^ 40 * 764449 * 2
def baseEnd_764449 : Nat := 43614419205442758163541

theorem tailTrace_764449 : CollatzResearch.WordTrace tailWord_764449 prefixEnd_764449 43614419205442758163541 := by
  unfold tailWord_764449
  simp only [CollatzResearch.WordTrace]
  refine ⟨27881745607539305340096401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18587830405026203560064267 27881745607539305340096401)
  ·
    refine ⟨20911309205654479005072301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27881745607539305340096401 20911309205654479005072301)
    ·
      refine ⟨7841740952120429626902113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20911309205654479005072301 7841740952120429626902113)
      ·
        refine ⟨5881305714090322220176585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7841740952120429626902113 5881305714090322220176585)
        ·
          refine ⟨4410979285567741665132439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5881305714090322220176585 4410979285567741665132439)
          ·
            refine ⟨6616468928351612497698659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410979285567741665132439 6616468928351612497698659)
            ·
              refine ⟨9924703392527418746547989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6616468928351612497698659 9924703392527418746547989)
              ·
                refine ⟨465220471524722753744437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9924703392527418746547989 465220471524722753744437)
                ·
                  refine ⟨43614419205442758163541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 465220471524722753744437 43614419205442758163541)
                  ·
                    rfl

theorem cell23_764449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 5].length) (baseStart_764449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764449 prefixEnd_764449 := by exact prefixLift 764449
  have htrace : WordTrace (prefixWord ++ tailWord_764449) baseStart_764449 baseEnd_764449 := by
    simpa [prefixWord, tailWord_764449, baseEnd_764449] using wordTrace_append hprefix tailTrace_764449
  have hstable : (prefixWord ++ tailWord_764449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764449).length < 2 ^ (prefixWord ++ tailWord_764449).sum := by decide
  have hdescent : baseEnd_764449 < baseStart_764449 := by decide
  rcases family_descends (prefixWord ++ tailWord_764449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764512 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 6]
def baseStart_764512 : Nat := 118140960795 + 764512 * 2 ^ 59
def prefixEnd_764512 : Nat := 4983230072969 + 3 ^ 40 * 764512 * 2
def baseEnd_764512 : Nat := 392562122130218076984079

theorem tailTrace_764512 : CollatzResearch.WordTrace tailWord_764512 prefixEnd_764512 392562122130218076984079 := by
  unfold tailWord_764512
  simp only [CollatzResearch.WordTrace]
  refine ⟨13942021703155533549819895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18589362270874044733093193 13942021703155533549819895)
  ·
    refine ⟨20913032554733300324729843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13942021703155533549819895 20913032554733300324729843)
    ·
      refine ⟨31369548832099950487094765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20913032554733300324729843 31369548832099950487094765)
      ·
        refine ⟨11763580812037481432660537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31369548832099950487094765 11763580812037481432660537)
        ·
          refine ⟨8822685609028111074495403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11763580812037481432660537 8822685609028111074495403)
          ·
            refine ⟨13234028413542166611743105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8822685609028111074495403 13234028413542166611743105)
            ·
              refine ⟨9925521310156624958807329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13234028413542166611743105 9925521310156624958807329)
              ·
                refine ⟨7444140982617468719105497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9925521310156624958807329 7444140982617468719105497)
                ·
                  refine ⟨5583105736963101539329123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7444140982617468719105497 5583105736963101539329123)
                  ·
                    refine ⟨8374658605444652308993685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5583105736963101539329123 8374658605444652308993685)
                    ·
                      refine ⟨392562122130218076984079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8374658605444652308993685 392562122130218076984079)
                      ·
                        rfl

theorem cell23_764512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_764512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764512 prefixEnd_764512 := by exact prefixLift 764512
  have htrace : WordTrace (prefixWord ++ tailWord_764512) baseStart_764512 baseEnd_764512 := by
    simpa [prefixWord, tailWord_764512, baseEnd_764512] using wordTrace_append hprefix tailTrace_764512
  have hstable : (prefixWord ++ tailWord_764512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764512).length < 2 ^ (prefixWord ++ tailWord_764512).sum := by decide
  have hdescent : baseEnd_764512 < baseStart_764512 := by decide
  rcases family_descends (prefixWord ++ tailWord_764512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764519 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_764519 : Nat := 118140960795 + 764519 * 2 ^ 59
def prefixEnd_764519 : Nat := 4983230072969 + 3 ^ 40 * 764519 * 2
def baseEnd_764519 : Nat := 392565716494799549596547

theorem tailTrace_764519 : CollatzResearch.WordTrace tailWord_764519 prefixEnd_764519 392565716494799549596547 := by
  unfold tailWord_764519
  simp only [CollatzResearch.WordTrace]
  refine ⟨27884298717285707295144611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18589532478190471530096407 27884298717285707295144611)
  ·
    refine ⟨41826448075928560942716917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27884298717285707295144611 41826448075928560942716917)
    ·
      refine ⟨3921229507118302588379711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41826448075928560942716917 3921229507118302588379711)
      ·
        refine ⟨5881844260677453882569567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3921229507118302588379711 5881844260677453882569567)
        ·
          refine ⟨8822766391016180823854351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5881844260677453882569567 8822766391016180823854351)
          ·
            refine ⟨13234149586524271235781527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8822766391016180823854351 13234149586524271235781527)
            ·
              refine ⟨19851224379786406853672291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13234149586524271235781527 19851224379786406853672291)
              ·
                refine ⟨29776836569679610280508437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19851224379786406853672291 29776836569679610280508437)
                ·
                  refine ⟨1395789214203731731898833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29776836569679610280508437 1395789214203731731898833)
                  ·
                    refine ⟨1046841910652798798924125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1395789214203731731898833 1046841910652798798924125)
                    ·
                      refine ⟨392565716494799549596547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1046841910652798798924125 392565716494799549596547)
                      ·
                        rfl

theorem cell23_764519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_764519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764519 prefixEnd_764519 := by exact prefixLift 764519
  have htrace : WordTrace (prefixWord ++ tailWord_764519) baseStart_764519 baseEnd_764519 := by
    simpa [prefixWord, tailWord_764519, baseEnd_764519] using wordTrace_append hprefix tailTrace_764519
  have hstable : (prefixWord ++ tailWord_764519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764519).length < 2 ^ (prefixWord ++ tailWord_764519).sum := by decide
  have hdescent : baseEnd_764519 < baseStart_764519 := by decide
  rcases family_descends (prefixWord ++ tailWord_764519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764533 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_764533 : Nat := 118140960795 + 764533 * 2 ^ 59
def prefixEnd_764533 : Nat := 4983230072969 + 3 ^ 40 * 764533 * 2
def baseEnd_764533 : Nat := 392572905223962494821483

theorem tailTrace_764533 : CollatzResearch.WordTrace tailWord_764533 prefixEnd_764533 392572905223962494821483 := by
  unfold tailWord_764533
  simp only [CollatzResearch.WordTrace]
  refine ⟨27884809339234987686154253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18589872892823325124102835 27884809339234987686154253)
  ·
    refine ⟨10456803502213120382307845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27884809339234987686154253 10456803502213120382307845)
    ·
      refine ⟨1960650656664960071682721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10456803502213120382307845 1960650656664960071682721)
      ·
        refine ⟨1470487992498720053762041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1960650656664960071682721 1470487992498720053762041)
        ·
          refine ⟨1102865994374040040321531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1470487992498720053762041 1102865994374040040321531)
          ·
            refine ⟨1654298991561060060482297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102865994374040040321531 1654298991561060060482297)
            ·
              refine ⟨1240724243670795045361723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1654298991561060060482297 1240724243670795045361723)
              ·
                refine ⟨1861086365506192568042585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1240724243670795045361723 1861086365506192568042585)
                ·
                  refine ⟨1395814774129644426031939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1861086365506192568042585 1395814774129644426031939)
                  ·
                    refine ⟨2093722161194466639047909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1395814774129644426031939 2093722161194466639047909)
                    ·
                      refine ⟨392572905223962494821483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2093722161194466639047909 392572905223962494821483)
                      ·
                        rfl

theorem cell23_764533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_764533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764533 prefixEnd_764533 := by exact prefixLift 764533
  have htrace : WordTrace (prefixWord ++ tailWord_764533) baseStart_764533 baseEnd_764533 := by
    simpa [prefixWord, tailWord_764533, baseEnd_764533] using wordTrace_append hprefix tailTrace_764533
  have hstable : (prefixWord ++ tailWord_764533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764533).length < 2 ^ (prefixWord ++ tailWord_764533).sum := by decide
  have hdescent : baseEnd_764533 < baseStart_764533 := by decide
  rcases family_descends (prefixWord ++ tailWord_764533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764616 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 4, 4]
def baseStart_764616 : Nat := 118140960795 + 764616 * 2 ^ 59
def prefixEnd_764616 : Nat := 4983230072969 + 3 ^ 40 * 764616 * 2
def baseEnd_764616 : Nat := 130871841372761890027867

theorem tailTrace_764616 : CollatzResearch.WordTrace tailWord_764616 prefixEnd_764616 130871841372761890027867 := by
  unfold tailWord_764616
  simp only [CollatzResearch.WordTrace]
  refine ⟨13943918298967146430712851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18591891065289528574283801 13943918298967146430712851)
  ·
    refine ⟨20915877448450719646069277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13943918298967146430712851 20915877448450719646069277)
    ·
      refine ⟨7843454043169019867275979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20915877448450719646069277 7843454043169019867275979)
      ·
        refine ⟨11765181064753529800913969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7843454043169019867275979 11765181064753529800913969)
        ·
          refine ⟨8823885798565147350685477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11765181064753529800913969 8823885798565147350685477)
          ·
            refine ⟨1654478587230965128253527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8823885798565147350685477 1654478587230965128253527)
            ·
              refine ⟨2481717880846447692380291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654478587230965128253527 2481717880846447692380291)
              ·
                refine ⟨3722576821269671538570437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481717880846447692380291 3722576821269671538570437)
                ·
                  refine ⟨697983153988063413481957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3722576821269671538570437 697983153988063413481957)
                  ·
                    refine ⟨130871841372761890027867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 697983153988063413481957 130871841372761890027867)
                    ·
                      rfl

theorem cell23_764616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_764616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764616 prefixEnd_764616 := by exact prefixLift 764616
  have htrace : WordTrace (prefixWord ++ tailWord_764616) baseStart_764616 baseEnd_764616 := by
    simpa [prefixWord, tailWord_764616, baseEnd_764616] using wordTrace_append hprefix tailTrace_764616
  have hstable : (prefixWord ++ tailWord_764616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764616).length < 2 ^ (prefixWord ++ tailWord_764616).sum := by decide
  have hdescent : baseEnd_764616 < baseStart_764616 := by decide
  rcases family_descends (prefixWord ++ tailWord_764616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764633 : List Nat := [1, 2, 1, 2, 3, 2, 5, 1, 2, 4]
def baseStart_764633 : Nat := 118140960795 + 764633 * 2 ^ 59
def prefixEnd_764633 : Nat := 4983230072969 + 3 ^ 40 * 764633 * 2
def baseEnd_764633 : Nat := 130874751096470701190341

theorem tailTrace_764633 : CollatzResearch.WordTrace tailWord_764633 prefixEnd_764633 130874751096470701190341 := by
  unfold tailWord_764633
  simp only [CollatzResearch.WordTrace]
  refine ⟨27888456638872704764794553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18592304425915136509863035 27888456638872704764794553)
  ·
    refine ⟨20916342479154528573595915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27888456638872704764794553 20916342479154528573595915)
    ·
      refine ⟨31374513718731792860393873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20916342479154528573595915 31374513718731792860393873)
      ·
        refine ⟨23530885289048844645295405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31374513718731792860393873 23530885289048844645295405)
        ·
          refine ⟨8824081983393316741985777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23530885289048844645295405 8824081983393316741985777)
          ·
            refine ⟨6618061487544987556489333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8824081983393316741985777 6618061487544987556489333)
            ·
              refine ⟨620443264457342583420875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6618061487544987556489333 620443264457342583420875)
              ·
                refine ⟨930664896686013875131313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620443264457342583420875 930664896686013875131313)
                ·
                  refine ⟨697998672514510406348485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 930664896686013875131313 697998672514510406348485)
                  ·
                    refine ⟨130874751096470701190341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 697998672514510406348485 130874751096470701190341)
                    ·
                      rfl

theorem cell23_764633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 2, 4].length) (baseStart_764633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764633 prefixEnd_764633 := by exact prefixLift 764633
  have htrace : WordTrace (prefixWord ++ tailWord_764633) baseStart_764633 baseEnd_764633 := by
    simpa [prefixWord, tailWord_764633, baseEnd_764633] using wordTrace_append hprefix tailTrace_764633
  have hstable : (prefixWord ++ tailWord_764633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764633).length < 2 ^ (prefixWord ++ tailWord_764633).sum := by decide
  have hdescent : baseEnd_764633 < baseStart_764633 := by decide
  rcases family_descends (prefixWord ++ tailWord_764633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764643 : List Nat := [1, 1, 1, 7, 1, 1, 1, 4, 1, 2, 3]
def baseStart_764643 : Nat := 118140960795 + 764643 * 2 ^ 59
def prefixEnd_764643 : Nat := 4983230072969 + 3 ^ 40 * 764643 * 2
def baseEnd_764643 : Nat := 392629388095957064445977

theorem tailTrace_764643 : CollatzResearch.WordTrace tailWord_764643 prefixEnd_764643 392629388095957064445977 := by
  unfold tailWord_764643
  simp only [CollatzResearch.WordTrace]
  refine ⟨27888821368836476472658583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18592547579224317648439055 27888821368836476472658583)
  ·
    refine ⟨41833232053254714708987875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27888821368836476472658583 41833232053254714708987875)
    ·
      refine ⟨62749848079882072063481813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41833232053254714708987875 62749848079882072063481813)
      ·
        refine ⟨1470699564372236063987855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 62749848079882072063481813 1470699564372236063987855)
        ·
          refine ⟨2206049346558354095981783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470699564372236063987855 2206049346558354095981783)
          ·
            refine ⟨3309074019837531143972675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206049346558354095981783 3309074019837531143972675)
            ·
              refine ⟨4963611029756296715959013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309074019837531143972675 4963611029756296715959013)
              ·
                refine ⟨930677068079305634242315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4963611029756296715959013 930677068079305634242315)
                ·
                  refine ⟨1396015602118958451363473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930677068079305634242315 1396015602118958451363473)
                  ·
                    refine ⟨1047011701589218838522605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1396015602118958451363473 1047011701589218838522605)
                    ·
                      refine ⟨392629388095957064445977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1047011701589218838522605 392629388095957064445977)
                      ·
                        rfl

theorem cell23_764643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_764643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764643 prefixEnd_764643 := by exact prefixLift 764643
  have htrace : WordTrace (prefixWord ++ tailWord_764643) baseStart_764643 baseEnd_764643 := by
    simpa [prefixWord, tailWord_764643, baseEnd_764643] using wordTrace_append hprefix tailTrace_764643
  have hstable : (prefixWord ++ tailWord_764643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764643).length < 2 ^ (prefixWord ++ tailWord_764643).sum := by decide
  have hdescent : baseEnd_764643 < baseStart_764643 := by decide
  rcases family_descends (prefixWord ++ tailWord_764643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764656 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 6, 1, 3]
def baseStart_764656 : Nat := 118140960795 + 764656 * 2 ^ 59
def prefixEnd_764656 : Nat := 4983230072969 + 3 ^ 40 * 764656 * 2
def baseEnd_764656 : Nat := 392636063344465513583417

theorem tailTrace_764656 : CollatzResearch.WordTrace tailWord_764656 prefixEnd_764656 392636063344465513583417 := by
  unfold tailWord_764656
  simp only [CollatzResearch.WordTrace]
  refine ⟨13944647758894689846440911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18592863678526253128587881 13944647758894689846440911)
  ·
    refine ⟨20916971638342034769661367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13944647758894689846440911 20916971638342034769661367)
    ·
      refine ⟨31375457457513052154492051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20916971638342034769661367 31375457457513052154492051)
      ·
        refine ⟨47063186186269578231738077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31375457457513052154492051 47063186186269578231738077)
        ·
          refine ⟨17648694819851091836901779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47063186186269578231738077 17648694819851091836901779)
          ·
            refine ⟨26473042229776637755352669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17648694819851091836901779 26473042229776637755352669)
            ·
              refine ⟨9927390836166239158257251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26473042229776637755352669 9927390836166239158257251)
              ·
                refine ⟨14891086254249358737385877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9927390836166239158257251 14891086254249358737385877)
                ·
                  refine ⟨698019668167938690814963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14891086254249358737385877 698019668167938690814963)
                  ·
                    refine ⟨1047029502251908036222445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 698019668167938690814963 1047029502251908036222445)
                    ·
                      refine ⟨392636063344465513583417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1047029502251908036222445 392636063344465513583417)
                      ·
                        rfl

theorem cell23_764656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 6, 1, 3].length) (baseStart_764656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764656 prefixEnd_764656 := by exact prefixLift 764656
  have htrace : WordTrace (prefixWord ++ tailWord_764656) baseStart_764656 baseEnd_764656 := by
    simpa [prefixWord, tailWord_764656, baseEnd_764656] using wordTrace_append hprefix tailTrace_764656
  have hstable : (prefixWord ++ tailWord_764656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764656).length < 2 ^ (prefixWord ++ tailWord_764656).sum := by decide
  have hdescent : baseEnd_764656 < baseStart_764656 := by decide
  rcases family_descends (prefixWord ++ tailWord_764656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764669 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_764669 : Nat := 118140960795 + 764669 * 2 ^ 59
def prefixEnd_764669 : Nat := 4983230072969 + 3 ^ 40 * 764669 * 2
def baseEnd_764669 : Nat := 392642738592973962720857

theorem tailTrace_764669 : CollatzResearch.WordTrace tailWord_764669 prefixEnd_764669 392642738592973962720857 := by
  unfold tailWord_764669
  simp only [CollatzResearch.WordTrace]
  refine ⟨27889769666742282913105061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18593179777828188608736707 27889769666742282913105061)
  ·
    refine ⟨5229331812514178046207199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27889769666742282913105061 5229331812514178046207199)
    ·
      refine ⟨7843997718771267069310799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5229331812514178046207199 7843997718771267069310799)
      ·
        refine ⟨11765996578156900603966199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7843997718771267069310799 11765996578156900603966199)
        ·
          refine ⟨17648994867235350905949299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11765996578156900603966199 17648994867235350905949299)
          ·
            refine ⟨26473492300853026358923949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17648994867235350905949299 26473492300853026358923949)
            ·
              refine ⟨9927559612819884884596481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26473492300853026358923949 9927559612819884884596481)
              ·
                refine ⟨7445669709614913663447361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9927559612819884884596481 7445669709614913663447361)
                ·
                  refine ⟨5584252282211185247585521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7445669709614913663447361 5584252282211185247585521)
                  ·
                    refine ⟨4188189211658388935689141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5584252282211185247585521 4188189211658388935689141)
                    ·
                      refine ⟨392642738592973962720857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4188189211658388935689141 392642738592973962720857)
                      ·
                        rfl

theorem cell23_764669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_764669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764669 prefixEnd_764669 := by exact prefixLift 764669
  have htrace : WordTrace (prefixWord ++ tailWord_764669) baseStart_764669 baseEnd_764669 := by
    simpa [prefixWord, tailWord_764669, baseEnd_764669] using wordTrace_append hprefix tailTrace_764669
  have hstable : (prefixWord ++ tailWord_764669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764669).length < 2 ^ (prefixWord ++ tailWord_764669).sum := by decide
  have hdescent : baseEnd_764669 < baseStart_764669 := by decide
  rcases family_descends (prefixWord ++ tailWord_764669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764673 : List Nat := [1, 2, 4, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_764673 : Nat := 118140960795 + 764673 * 2 ^ 59
def prefixEnd_764673 : Nat := 4983230072969 + 3 ^ 40 * 764673 * 2
def baseEnd_764673 : Nat := 392644792515591947070839

theorem tailTrace_764673 : CollatzResearch.WordTrace tailWord_764673 prefixEnd_764673 392644792515591947070839 := by
  unfold tailWord_764673
  simp only [CollatzResearch.WordTrace]
  refine ⟨27889915558727791596250673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18593277039151861064167115 27889915558727791596250673)
  ·
    refine ⟨20917436669045843697188005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27889915558727791596250673 20917436669045843697188005)
    ·
      refine ⟨3922019375446095693222751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20917436669045843697188005 3922019375446095693222751)
      ·
        refine ⟨5883029063169143539834127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3922019375446095693222751 5883029063169143539834127)
        ·
          refine ⟨8824543594753715309751191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5883029063169143539834127 8824543594753715309751191)
          ·
            refine ⟨13236815392130572964626787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8824543594753715309751191 13236815392130572964626787)
            ·
              refine ⟨19855223088195859446940181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13236815392130572964626787 19855223088195859446940181)
              ·
                refine ⟨930713582259180911575321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19855223088195859446940181 930713582259180911575321)
                ·
                  refine ⟨698035186694385683681491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 930713582259180911575321 698035186694385683681491)
                  ·
                    refine ⟨1047052780041578525522237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 698035186694385683681491 1047052780041578525522237)
                    ·
                      refine ⟨392644792515591947070839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1047052780041578525522237 392644792515591947070839)
                      ·
                        rfl

theorem cell23_764673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_764673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764673 prefixEnd_764673 := by exact prefixLift 764673
  have htrace : WordTrace (prefixWord ++ tailWord_764673) baseStart_764673 baseEnd_764673 := by
    simpa [prefixWord, tailWord_764673, baseEnd_764673] using wordTrace_append hprefix tailTrace_764673
  have hstable : (prefixWord ++ tailWord_764673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764673).length < 2 ^ (prefixWord ++ tailWord_764673).sum := by decide
  have hdescent : baseEnd_764673 < baseStart_764673 := by decide
  rcases family_descends (prefixWord ++ tailWord_764673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764689 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 2, 6]
def baseStart_764689 : Nat := 118140960795 + 764689 * 2 ^ 59
def prefixEnd_764689 : Nat := 4983230072969 + 3 ^ 40 * 764689 * 2
def baseEnd_764689 : Nat := 130884336068687961490255

theorem tailTrace_764689 : CollatzResearch.WordTrace tailWord_764689 prefixEnd_764689 130884336068687961490255 := by
  unfold tailWord_764689
  simp only [CollatzResearch.WordTrace]
  refine ⟨27890499126669826328833121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18593666084446550885888747 27890499126669826328833121)
  ·
    refine ⟨20917874345002369746624841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27890499126669826328833121 20917874345002369746624841)
    ·
      refine ⟨15688405758751777309968631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20917874345002369746624841 15688405758751777309968631)
      ·
        refine ⟨23532608638127665964952947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15688405758751777309968631 23532608638127665964952947)
        ·
          refine ⟨35298912957191498947429421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23532608638127665964952947 35298912957191498947429421)
          ·
            refine ⟨13237092358946812105286033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35298912957191498947429421 13237092358946812105286033)
            ·
              refine ⟨9927819269210109078964525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13237092358946812105286033 9927819269210109078964525)
              ·
                refine ⟨3722932225953790904611697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9927819269210109078964525 3722932225953790904611697)
                ·
                  refine ⟨2792199169465343178458773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3722932225953790904611697 2792199169465343178458773)
                  ·
                    refine ⟨130884336068687961490255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2792199169465343178458773 130884336068687961490255)
                    ·
                      rfl

theorem cell23_764689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_764689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764689 prefixEnd_764689 := by exact prefixLift 764689
  have htrace : WordTrace (prefixWord ++ tailWord_764689) baseStart_764689 baseEnd_764689 := by
    simpa [prefixWord, tailWord_764689, baseEnd_764689] using wordTrace_append hprefix tailTrace_764689
  have hstable : (prefixWord ++ tailWord_764689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764689).length < 2 ^ (prefixWord ++ tailWord_764689).sum := by decide
  have hdescent : baseEnd_764689 < baseStart_764689 := by decide
  rcases family_descends (prefixWord ++ tailWord_764689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764700 : List Nat := [2, 2, 3, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_764700 : Nat := 118140960795 + 764700 * 2 ^ 59
def prefixEnd_764700 : Nat := 4983230072969 + 3 ^ 40 * 764700 * 2
def baseEnd_764700 : Nat := 392658656493263341433215

theorem tailTrace_764700 : CollatzResearch.WordTrace tailWord_764700 prefixEnd_764700 392658656493263341433215 := by
  unfold tailWord_764700
  simp only [CollatzResearch.WordTrace]
  refine ⟨13945450164814987603741777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18593933553086650138322369 13945450164814987603741777)
  ·
    refine ⟨10459087623611240702806333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13945450164814987603741777 10459087623611240702806333)
    ·
      refine ⟨3922157858854215263552375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10459087623611240702806333 3922157858854215263552375)
      ·
        refine ⟨5883236788281322895328563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3922157858854215263552375 5883236788281322895328563)
        ·
          refine ⟨8824855182421984342992845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5883236788281322895328563 8824855182421984342992845)
          ·
            refine ⟨3309320693408244128622317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8824855182421984342992845 3309320693408244128622317)
            ·
              refine ⟨1240995260028091548233369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3309320693408244128622317 1240995260028091548233369)
              ·
                refine ⟨930746445021068661175027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1240995260028091548233369 930746445021068661175027)
                ·
                  refine ⟨1396119667531602991762541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930746445021068661175027 1396119667531602991762541)
                  ·
                    refine ⟨523544875324351121910953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1396119667531602991762541 523544875324351121910953)
                    ·
                      refine ⟨392658656493263341433215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 523544875324351121910953 392658656493263341433215)
                      ·
                        rfl

theorem cell23_764700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_764700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764700 prefixEnd_764700 := by exact prefixLift 764700
  have htrace : WordTrace (prefixWord ++ tailWord_764700) baseStart_764700 baseEnd_764700 := by
    simpa [prefixWord, tailWord_764700, baseEnd_764700] using wordTrace_append hprefix tailTrace_764700
  have hstable : (prefixWord ++ tailWord_764700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764700).length < 2 ^ (prefixWord ++ tailWord_764700).sum := by decide
  have hdescent : baseEnd_764700 < baseStart_764700 := by decide
  rcases family_descends (prefixWord ++ tailWord_764700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764740 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_764740 : Nat := 118140960795 + 764740 * 2 ^ 59
def prefixEnd_764740 : Nat := 4983230072969 + 3 ^ 40 * 764740 * 2
def baseEnd_764740 : Nat := 130893065239814394977677

theorem tailTrace_764740 : CollatzResearch.WordTrace tailWord_764740 prefixEnd_764740 130893065239814394977677 := by
  unfold tailWord_764740
  simp only [CollatzResearch.WordTrace]
  refine ⟨13946179624742531019469837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18594906166323374692626449 13946179624742531019469837)
  ·
    refine ⟨5229817359278449132301189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13946179624742531019469837 5229817359278449132301189)
    ·
      refine ⟨980590754864709212306473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5229817359278449132301189 980590754864709212306473)
      ·
        refine ⟨735443066148531909229855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 980590754864709212306473 735443066148531909229855)
        ·
          refine ⟨1103164599222797863844783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735443066148531909229855 1103164599222797863844783)
          ·
            refine ⟨1654746898834196795767175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103164599222797863844783 1654746898834196795767175)
            ·
              refine ⟨2482120348251295193650763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654746898834196795767175 2482120348251295193650763)
              ·
                refine ⟨3723180522376942790476145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2482120348251295193650763 3723180522376942790476145)
                ·
                  refine ⟨2792385391782707092857109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3723180522376942790476145 2792385391782707092857109)
                  ·
                    refine ⟨130893065239814394977677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2792385391782707092857109 130893065239814394977677)
                    ·
                      rfl

theorem cell23_764740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_764740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764740 prefixEnd_764740 := by exact prefixLift 764740
  have htrace : WordTrace (prefixWord ++ tailWord_764740) baseStart_764740 baseEnd_764740 := by
    simpa [prefixWord, tailWord_764740, baseEnd_764740] using wordTrace_append hprefix tailTrace_764740
  have hstable : (prefixWord ++ tailWord_764740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764740).length < 2 ^ (prefixWord ++ tailWord_764740).sum := by decide
  have hdescent : baseEnd_764740 < baseStart_764740 := by decide
  rcases family_descends (prefixWord ++ tailWord_764740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764803 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 2, 4, 2]
def baseStart_764803 : Nat := 118140960795 + 764803 * 2 ^ 59
def prefixEnd_764803 : Nat := 4983230072969 + 3 ^ 40 * 764803 * 2
def baseEnd_764803 : Nat := 392711545000676438445241

theorem tailTrace_764803 : CollatzResearch.WordTrace tailWord_764803 prefixEnd_764803 392711545000676438445241 := by
  unfold tailWord_764803
  simp only [CollatzResearch.WordTrace]
  refine ⟨27894657048256823798483063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18596438032171215865655375 27894657048256823798483063)
  ·
    refine ⟨41841985572385235697724595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27894657048256823798483063 41841985572385235697724595)
    ·
      refine ⟨62762978358577853546586893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41841985572385235697724595 62762978358577853546586893)
      ·
        refine ⟨23536116884466695079970085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62762978358577853546586893 23536116884466695079970085)
        ·
          refine ⟨4413021915837505327494391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23536116884466695079970085 4413021915837505327494391)
          ·
            refine ⟨6619532873756257991241587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4413021915837505327494391 6619532873756257991241587)
            ·
              refine ⟨9929299310634386986862381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6619532873756257991241587 9929299310634386986862381)
              ·
                refine ⟨3723487241487895120073393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9929299310634386986862381 3723487241487895120073393)
                ·
                  refine ⟨2792615431115921340055045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3723487241487895120073393 2792615431115921340055045)
                  ·
                    refine ⟨523615393334235251260321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2792615431115921340055045 523615393334235251260321)
                    ·
                      refine ⟨392711545000676438445241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 523615393334235251260321 392711545000676438445241)
                      ·
                        rfl

theorem cell23_764803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 4, 2].length) (baseStart_764803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764803 prefixEnd_764803 := by exact prefixLift 764803
  have htrace : WordTrace (prefixWord ++ tailWord_764803) baseStart_764803 baseEnd_764803 := by
    simpa [prefixWord, tailWord_764803, baseEnd_764803] using wordTrace_append hprefix tailTrace_764803
  have hstable : (prefixWord ++ tailWord_764803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764803).length < 2 ^ (prefixWord ++ tailWord_764803).sum := by decide
  have hdescent : baseEnd_764803 < baseStart_764803 := by decide
  rcases family_descends (prefixWord ++ tailWord_764803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764823 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 3]
def baseStart_764823 : Nat := 118140960795 + 764823 * 2 ^ 59
def prefixEnd_764823 : Nat := 4983230072969 + 3 ^ 40 * 764823 * 2
def baseEnd_764823 : Nat := 392721814613766360195149

theorem tailTrace_764823 : CollatzResearch.WordTrace tailWord_764823 prefixEnd_764823 392721814613766360195149 := by
  unfold tailWord_764823
  simp only [CollatzResearch.WordTrace]
  refine ⟨27895386508184367214211123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18596924338789578142807415 27895386508184367214211123)
  ·
    refine ⟨41843079762276550821316685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27895386508184367214211123 41843079762276550821316685)
    ·
      refine ⟨15691154910853706557993757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41843079762276550821316685 15691154910853706557993757)
      ·
        refine ⟨5884183091570139959247659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15691154910853706557993757 5884183091570139959247659)
        ·
          refine ⟨8826274637355209938871489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5884183091570139959247659 8826274637355209938871489)
          ·
            refine ⟨6619705978016407454153617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8826274637355209938871489 6619705978016407454153617)
            ·
              refine ⟨4964779483512305590615213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6619705978016407454153617 4964779483512305590615213)
              ·
                refine ⟨1861792306317114596480705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4964779483512305590615213 1861792306317114596480705)
                ·
                  refine ⟨1396344229737835947360529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1861792306317114596480705 1396344229737835947360529)
                  ·
                    refine ⟨1047258172303376960520397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1396344229737835947360529 1047258172303376960520397)
                    ·
                      refine ⟨392721814613766360195149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1047258172303376960520397 392721814613766360195149)
                      ·
                        rfl

theorem cell23_764823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_764823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764823 prefixEnd_764823 := by exact prefixLift 764823
  have htrace : WordTrace (prefixWord ++ tailWord_764823) baseStart_764823 baseEnd_764823 := by
    simpa [prefixWord, tailWord_764823, baseEnd_764823] using wordTrace_append hprefix tailTrace_764823
  have hstable : (prefixWord ++ tailWord_764823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764823).length < 2 ^ (prefixWord ++ tailWord_764823).sum := by decide
  have hdescent : baseEnd_764823 < baseStart_764823 := by decide
  rcases family_descends (prefixWord ++ tailWord_764823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764863 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 1, 5, 2]
def baseStart_764863 : Nat := 118140960795 + 764863 * 2 ^ 59
def prefixEnd_764863 : Nat := 4983230072969 + 3 ^ 40 * 764863 * 2
def baseEnd_764863 : Nat := 392742353839946203694965

theorem tailTrace_764863 : CollatzResearch.WordTrace tailWord_764863 prefixEnd_764863 392742353839946203694965 := by
  unfold tailWord_764863
  simp only [CollatzResearch.WordTrace]
  refine ⟨27896845428039454045667243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18597896952026302697111495 27896845428039454045667243)
  ·
    refine ⟨41845268142059181068500865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27896845428039454045667243 41845268142059181068500865)
    ·
      refine ⟨31383951106544385801375649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41845268142059181068500865 31383951106544385801375649)
      ·
        refine ⟨23537963329908289351031737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31383951106544385801375649 23537963329908289351031737)
        ·
          refine ⟨17653472497431217013273803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23537963329908289351031737 17653472497431217013273803)
          ·
            refine ⟨26480208746146825519910705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17653472497431217013273803 26480208746146825519910705)
            ·
              refine ⟨19860156559610119139933029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26480208746146825519910705 19860156559610119139933029)
              ·
                refine ⟨3723779354926897338737443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19860156559610119139933029 3723779354926897338737443)
                ·
                  refine ⟨5585669032390346008106165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723779354926897338737443 5585669032390346008106165)
                  ·
                    refine ⟨523656471786594938259953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5585669032390346008106165 523656471786594938259953)
                    ·
                      refine ⟨392742353839946203694965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 523656471786594938259953 392742353839946203694965)
                      ·
                        rfl

theorem cell23_764863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 5, 2].length) (baseStart_764863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764863 prefixEnd_764863 := by exact prefixLift 764863
  have htrace : WordTrace (prefixWord ++ tailWord_764863) baseStart_764863 baseEnd_764863 := by
    simpa [prefixWord, tailWord_764863, baseEnd_764863] using wordTrace_append hprefix tailTrace_764863
  have hstable : (prefixWord ++ tailWord_764863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764863).length < 2 ^ (prefixWord ++ tailWord_764863).sum := by decide
  have hdescent : baseEnd_764863 < baseStart_764863 := by decide
  rcases family_descends (prefixWord ++ tailWord_764863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764904 : List Nat := [2, 1, 4, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_764904 : Nat := 118140960795 + 764904 * 2 ^ 59
def prefixEnd_764904 : Nat := 4983230072969 + 3 ^ 40 * 764904 * 2
def baseEnd_764904 : Nat := 392763406546780543282277

theorem tailTrace_764904 : CollatzResearch.WordTrace tailWord_764904 prefixEnd_764904 392763406546780543282277 := by
  unfold tailWord_764904
  simp only [CollatzResearch.WordTrace]
  refine ⟨13949170410445459023954883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18598893880593945365273177 13949170410445459023954883)
  ·
    refine ⟨20923755615668188535932325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13949170410445459023954883 20923755615668188535932325)
    ·
      refine ⟨3923204177937785350487311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20923755615668188535932325 3923204177937785350487311)
      ·
        refine ⟨5884806266906678025730967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3923204177937785350487311 5884806266906678025730967)
        ·
          refine ⟨8827209400360017038596451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5884806266906678025730967 8827209400360017038596451)
          ·
            refine ⟨13240814100540025557894677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8827209400360017038596451 13240814100540025557894677)
            ·
              refine ⟨620663160962813698026313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13240814100540025557894677 620663160962813698026313)
              ·
                refine ⟨465497370722110273519735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620663160962813698026313 465497370722110273519735)
                ·
                  refine ⟨698246056083165410279603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465497370722110273519735 698246056083165410279603)
                  ·
                    refine ⟨1047369084124748115419405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 698246056083165410279603 1047369084124748115419405)
                    ·
                      refine ⟨392763406546780543282277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1047369084124748115419405 392763406546780543282277)
                      ·
                        rfl

theorem cell23_764904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_764904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764904 prefixEnd_764904 := by exact prefixLift 764904
  have htrace : WordTrace (prefixWord ++ tailWord_764904) baseStart_764904 baseEnd_764904 := by
    simpa [prefixWord, tailWord_764904, baseEnd_764904] using wordTrace_append hprefix tailTrace_764904
  have hstable : (prefixWord ++ tailWord_764904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764904).length < 2 ^ (prefixWord ++ tailWord_764904).sum := by decide
  have hdescent : baseEnd_764904 < baseStart_764904 := by decide
  rcases family_descends (prefixWord ++ tailWord_764904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764933 : List Nat := [1, 3, 1, 1, 2, 3, 5, 7]
def baseStart_764933 : Nat := 118140960795 + 764933 * 2 ^ 59
def prefixEnd_764933 : Nat := 4983230072969 + 3 ^ 40 * 764933 * 2
def baseEnd_764933 : Nat := 14547344351324478882209

theorem tailTrace_764933 : CollatzResearch.WordTrace tailWord_764933 prefixEnd_764933 14547344351324478882209 := by
  unfold tailWord_764933
  simp only [CollatzResearch.WordTrace]
  refine ⟨27899398537785856000715453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18599599025190570667143635 27899398537785856000715453)
  ·
    refine ⟨10462274451669696000268295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27899398537785856000715453 10462274451669696000268295)
    ·
      refine ⟨15693411677504544000402443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10462274451669696000268295 15693411677504544000402443)
      ·
        refine ⟨23540117516256816000603665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15693411677504544000402443 23540117516256816000603665)
        ·
          refine ⟨17655088137192612000452749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23540117516256816000603665 17655088137192612000452749)
          ·
            refine ⟨6620658051447229500169781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17655088137192612000452749 6620658051447229500169781)
            ·
              refine ⟨620686692323177765640917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6620658051447229500169781 620686692323177765640917)
              ·
                refine ⟨14547344351324478882209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 620686692323177765640917 14547344351324478882209)
                ·
                  rfl

theorem cell23_764933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 7].length) (baseStart_764933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764933 prefixEnd_764933 := by exact prefixLift 764933
  have htrace : WordTrace (prefixWord ++ tailWord_764933) baseStart_764933 baseEnd_764933 := by
    simpa [prefixWord, tailWord_764933, baseEnd_764933] using wordTrace_append hprefix tailTrace_764933
  have hstable : (prefixWord ++ tailWord_764933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764933).length < 2 ^ (prefixWord ++ tailWord_764933).sum := by decide
  have hdescent : baseEnd_764933 < baseStart_764933 := by decide
  rcases family_descends (prefixWord ++ tailWord_764933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_764990 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_764990 : Nat := 118140960795 + 764990 * 2 ^ 59
def prefixEnd_764990 : Nat := 4983230072969 + 3 ^ 40 * 764990 * 2
def baseEnd_764990 : Nat := 392807565883067206806881

theorem tailTrace_764990 : CollatzResearch.WordTrace tailWord_764990 prefixEnd_764990 392807565883067206806881 := by
  unfold tailWord_764990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3487684687322419341942553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18600984999052903157026949 3487684687322419341942553)
  ·
    refine ⟨2615763515491814506456915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3487684687322419341942553 2615763515491814506456915)
    ·
      refine ⟨3923645273237721759685373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2615763515491814506456915 3923645273237721759685373)
      ·
        refine ⟨1471366977464145659882015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3923645273237721759685373 1471366977464145659882015)
        ·
          refine ⟨2207050466196218489823023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471366977464145659882015 2207050466196218489823023)
          ·
            refine ⟨3310575699294327734734535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2207050466196218489823023 3310575699294327734734535)
            ·
              refine ⟨4965863548941491602101803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3310575699294327734734535 4965863548941491602101803)
              ·
                refine ⟨7448795323412237403152705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4965863548941491602101803 7448795323412237403152705)
                ·
                  refine ⟨5586596492559178052364529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7448795323412237403152705 5586596492559178052364529)
                  ·
                    refine ⟨4189947369419383539273397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5586596492559178052364529 4189947369419383539273397)
                    ·
                      refine ⟨392807565883067206806881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4189947369419383539273397 392807565883067206806881)
                      ·
                        rfl

theorem cell23_764990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_764990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_764990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_764990 prefixEnd_764990 := by exact prefixLift 764990
  have htrace : WordTrace (prefixWord ++ tailWord_764990) baseStart_764990 baseEnd_764990 := by
    simpa [prefixWord, tailWord_764990, baseEnd_764990] using wordTrace_append hprefix tailTrace_764990
  have hstable : (prefixWord ++ tailWord_764990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_764990).length < 2 ^ (prefixWord ++ tailWord_764990).sum := by decide
  have hdescent : baseEnd_764990 < baseStart_764990 := by decide
  rcases family_descends (prefixWord ++ tailWord_764990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765000 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 3, 4, 2]
def baseStart_765000 : Nat := 118140960795 + 765000 * 2 ^ 59
def prefixEnd_765000 : Nat := 4983230072969 + 3 ^ 40 * 765000 * 2
def baseEnd_765000 : Nat := 392812700689612167681835

theorem tailTrace_765000 : CollatzResearch.WordTrace tailWord_765000 prefixEnd_765000 392812700689612167681835 := by
  unfold tailWord_765000
  simp only [CollatzResearch.WordTrace]
  refine ⟨13950921114271563221702227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18601228152362084295602969 13950921114271563221702227)
  ·
    refine ⟨20926381671407344832553341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13950921114271563221702227 20926381671407344832553341)
    ·
      refine ⟨7847393126777754312207503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20926381671407344832553341 7847393126777754312207503)
      ·
        refine ⟨11771089690166631468311255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7847393126777754312207503 11771089690166631468311255)
        ·
          refine ⟨17656634535249947202466883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11771089690166631468311255 17656634535249947202466883)
          ·
            refine ⟨26484951802874920803700325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17656634535249947202466883 26484951802874920803700325)
            ·
              refine ⟨4965928463039047650693811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26484951802874920803700325 4965928463039047650693811)
              ·
                refine ⟨7448892694558571476040717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4965928463039047650693811 7448892694558571476040717)
                ·
                  refine ⟨2793334760459464303515269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7448892694558571476040717 2793334760459464303515269)
                  ·
                    refine ⟨523750267586149556909113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2793334760459464303515269 523750267586149556909113)
                    ·
                      refine ⟨392812700689612167681835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 523750267586149556909113 392812700689612167681835)
                      ·
                        rfl

theorem cell23_765000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_765000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765000 prefixEnd_765000 := by exact prefixLift 765000
  have htrace : WordTrace (prefixWord ++ tailWord_765000) baseStart_765000 baseEnd_765000 := by
    simpa [prefixWord, tailWord_765000, baseEnd_765000] using wordTrace_append hprefix tailTrace_765000
  have hstable : (prefixWord ++ tailWord_765000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765000).length < 2 ^ (prefixWord ++ tailWord_765000).sum := by decide
  have hdescent : baseEnd_765000 < baseStart_765000 := by decide
  rcases family_descends (prefixWord ++ tailWord_765000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765020 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_765020 : Nat := 118140960795 + 765020 * 2 ^ 59
def prefixEnd_765020 : Nat := 4983230072969 + 3 ^ 40 * 765020 * 2
def baseEnd_765020 : Nat := 392822970302702089431743

theorem tailTrace_765020 : CollatzResearch.WordTrace tailWord_765020 prefixEnd_765020 392822970302702089431743 := by
  unfold tailWord_765020
  simp only [CollatzResearch.WordTrace]
  refine ⟨13951285844235334929566257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18601714458980446572755009 13951285844235334929566257)
  ·
    refine ⟨10463464383176501197174693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13951285844235334929566257 10463464383176501197174693)
    ·
      refine ⟨1961899571845593974470255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10463464383176501197174693 1961899571845593974470255)
      ·
        refine ⟨2942849357768390961705383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1961899571845593974470255 2942849357768390961705383)
        ·
          refine ⟨4414274036652586442558075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2942849357768390961705383 4414274036652586442558075)
          ·
            refine ⟨6621411054978879663837113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4414274036652586442558075 6621411054978879663837113)
            ·
              refine ⟨4966058291234159747877835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6621411054978879663837113 4966058291234159747877835)
              ·
                refine ⟨7449087436851239621816753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4966058291234159747877835 7449087436851239621816753)
                ·
                  refine ⟨5586815577638429716362565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7449087436851239621816753 5586815577638429716362565)
                  ·
                    refine ⟨1047527920807205571817981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5586815577638429716362565 1047527920807205571817981)
                    ·
                      refine ⟨392822970302702089431743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1047527920807205571817981 392822970302702089431743)
                      ·
                        rfl

theorem cell23_765020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_765020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765020 prefixEnd_765020 := by exact prefixLift 765020
  have htrace : WordTrace (prefixWord ++ tailWord_765020) baseStart_765020 baseEnd_765020 := by
    simpa [prefixWord, tailWord_765020, baseEnd_765020] using wordTrace_append hprefix tailTrace_765020
  have hstable : (prefixWord ++ tailWord_765020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765020).length < 2 ^ (prefixWord ++ tailWord_765020).sum := by decide
  have hdescent : baseEnd_765020 < baseStart_765020 := by decide
  rcases family_descends (prefixWord ++ tailWord_765020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765074 : List Nat := [3, 2, 3, 1, 1, 2, 4, 2, 5]
def baseStart_765074 : Nat := 118140960795 + 765074 * 2 ^ 59
def prefixEnd_765074 : Nat := 4983230072969 + 3 ^ 40 * 765074 * 2
def baseEnd_765074 : Nat := 43650077584227208684055

theorem tailTrace_765074 : CollatzResearch.WordTrace tailWord_765074 prefixEnd_765074 43650077584227208684055 := by
  unfold tailWord_765074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6976135307568759270399569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18603027486850024721065517 6976135307568759270399569)
  ·
    refine ⟨5232101480676569452799677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6976135307568759270399569 5232101480676569452799677)
    ·
      refine ⟨1962038055253713544799879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5232101480676569452799677 1962038055253713544799879)
      ·
        refine ⟨2943057082880570317199819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1962038055253713544799879 2943057082880570317199819)
        ·
          refine ⟨4414585624320855475799729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2943057082880570317199819 4414585624320855475799729)
          ·
            refine ⟨3310939218240641606849797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4414585624320855475799729 3310939218240641606849797)
            ·
              refine ⟨620801103420120301284337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3310939218240641606849797 620801103420120301284337)
              ·
                refine ⟨465600827565090225963253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620801103420120301284337 465600827565090225963253)
                ·
                  refine ⟨43650077584227208684055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 465600827565090225963253 43650077584227208684055)
                  ·
                    rfl

theorem cell23_765074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_765074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765074 prefixEnd_765074 := by exact prefixLift 765074
  have htrace : WordTrace (prefixWord ++ tailWord_765074) baseStart_765074 baseEnd_765074 := by
    simpa [prefixWord, tailWord_765074, baseEnd_765074] using wordTrace_append hprefix tailTrace_765074
  have hstable : (prefixWord ++ tailWord_765074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765074).length < 2 ^ (prefixWord ++ tailWord_765074).sum := by decide
  have hdescent : baseEnd_765074 < baseStart_765074 := by decide
  rcases family_descends (prefixWord ++ tailWord_765074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765080 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_765080 : Nat := 118140960795 + 765080 * 2 ^ 59
def prefixEnd_765080 : Nat := 4983230072969 + 3 ^ 40 * 765080 * 2
def baseEnd_765080 : Nat := 392853779141971854681467

theorem tailTrace_765080 : CollatzResearch.WordTrace tailWord_765080 prefixEnd_765080 392853779141971854681467 := by
  unfold tailWord_765080
  simp only [CollatzResearch.WordTrace]
  refine ⟨13952380034126650053158347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18603173378835533404211129 13952380034126650053158347)
  ·
    refine ⟨20928570051189975079737521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13952380034126650053158347 20928570051189975079737521)
    ·
      refine ⟨15696427538392481309803141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20928570051189975079737521 15696427538392481309803141)
      ·
        refine ⟨2943080163448590245588089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15696427538392481309803141 2943080163448590245588089)
        ·
          refine ⟨2207310122586442684191067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2943080163448590245588089 2207310122586442684191067)
          ·
            refine ⟨3310965183879664026286601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2207310122586442684191067 3310965183879664026286601)
            ·
              refine ⟨2483223887909748019714951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3310965183879664026286601 2483223887909748019714951)
              ·
                refine ⟨3724835831864622029572427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2483223887909748019714951 3724835831864622029572427)
                ·
                  refine ⟨5587253747796933044358641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724835831864622029572427 5587253747796933044358641)
                  ·
                    refine ⟨4190440310847699783268981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5587253747796933044358641 4190440310847699783268981)
                    ·
                      refine ⟨392853779141971854681467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4190440310847699783268981 392853779141971854681467)
                      ·
                        rfl

theorem cell23_765080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_765080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765080 prefixEnd_765080 := by exact prefixLift 765080
  have htrace : WordTrace (prefixWord ++ tailWord_765080) baseStart_765080 baseEnd_765080 := by
    simpa [prefixWord, tailWord_765080, baseEnd_765080] using wordTrace_append hprefix tailTrace_765080
  have hstable : (prefixWord ++ tailWord_765080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765080).length < 2 ^ (prefixWord ++ tailWord_765080).sum := by decide
  have hdescent : baseEnd_765080 < baseStart_765080 := by decide
  rcases family_descends (prefixWord ++ tailWord_765080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765130 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 8]
def baseStart_765130 : Nat := 118140960795 + 765130 * 2 ^ 59
def prefixEnd_765130 : Nat := 4983230072969 + 3 ^ 40 * 765130 * 2
def baseEnd_765130 : Nat := 43653272574966295450693

theorem tailTrace_765130 : CollatzResearch.WordTrace tailWord_765130 prefixEnd_765130 43653272574966295450693 := by
  unfold tailWord_765130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6976645929518039661409211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18604389145381439097091229 6976645929518039661409211)
  ·
    refine ⟨10464968894277059492113817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6976645929518039661409211 10464968894277059492113817)
    ·
      refine ⟨7848726670707794619085363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10464968894277059492113817 7848726670707794619085363)
      ·
        refine ⟨11773090006061691928628045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7848726670707794619085363 11773090006061691928628045)
        ·
          refine ⟨4414908752273134473235517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11773090006061691928628045 4414908752273134473235517)
          ·
            refine ⟨1655590782102425427463319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4414908752273134473235517 1655590782102425427463319)
            ·
              refine ⟨2483386173153638141194979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655590782102425427463319 2483386173153638141194979)
              ·
                refine ⟨3725079259730457211792469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2483386173153638141194979 3725079259730457211792469)
                ·
                  refine ⟨43653272574966295450693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3725079259730457211792469 43653272574966295450693)
                  ·
                    rfl

theorem cell23_765130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_765130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765130 prefixEnd_765130 := by exact prefixLift 765130
  have htrace : WordTrace (prefixWord ++ tailWord_765130) baseStart_765130 baseEnd_765130 := by
    simpa [prefixWord, tailWord_765130, baseEnd_765130] using wordTrace_append hprefix tailTrace_765130
  have hstable : (prefixWord ++ tailWord_765130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765130).length < 2 ^ (prefixWord ++ tailWord_765130).sum := by decide
  have hdescent : baseEnd_765130 < baseStart_765130 := by decide
  rcases family_descends (prefixWord ++ tailWord_765130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765134 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_765134 : Nat := 118140960795 + 765134 * 2 ^ 59
def prefixEnd_765134 : Nat := 4983230072969 + 3 ^ 40 * 765134 * 2
def baseEnd_765134 : Nat := 130960502365771547802073

theorem tailTrace_765134 : CollatzResearch.WordTrace tailWord_765134 prefixEnd_765134 130960502365771547802073 := by
  unfold tailWord_765134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3488341201257208416097807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18604486406705111552521637 3488341201257208416097807)
  ·
    refine ⟨5232511801885812624146711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3488341201257208416097807 5232511801885812624146711)
    ·
      refine ⟨7848767702828718936220067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5232511801885812624146711 7848767702828718936220067)
      ·
        refine ⟨11773151554243078404330101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7848767702828718936220067 11773151554243078404330101)
        ·
          refine ⟨1103732958210288600405947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11773151554243078404330101 1103732958210288600405947)
          ·
            refine ⟨1655599437315432900608921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103732958210288600405947 1655599437315432900608921)
            ·
              refine ⟨1241699577986574675456691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1655599437315432900608921 1241699577986574675456691)
              ·
                refine ⟨1862549366979862013185037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1241699577986574675456691 1862549366979862013185037)
                ·
                  refine ⟨698456012617448254944389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1862549366979862013185037 698456012617448254944389)
                  ·
                    refine ⟨130960502365771547802073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 698456012617448254944389 130960502365771547802073)
                    ·
                      rfl

theorem cell23_765134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_765134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765134 prefixEnd_765134 := by exact prefixLift 765134
  have htrace : WordTrace (prefixWord ++ tailWord_765134) baseStart_765134 baseEnd_765134 := by
    simpa [prefixWord, tailWord_765134, baseEnd_765134] using wordTrace_append hprefix tailTrace_765134
  have hstable : (prefixWord ++ tailWord_765134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765134).length < 2 ^ (prefixWord ++ tailWord_765134).sum := by decide
  have hdescent : baseEnd_765134 < baseStart_765134 := by decide
  rcases family_descends (prefixWord ++ tailWord_765134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765220 : List Nat := [2, 3, 1, 3, 1, 1, 1, 11]
def baseStart_765220 : Nat := 118140960795 + 765220 * 2 ^ 59
def prefixEnd_765220 : Nat := 4983230072969 + 3 ^ 40 * 765220 * 2
def baseEnd_765220 : Nat := 14552802460503752108549

theorem tailTrace_765220 : CollatzResearch.WordTrace tailWord_765220 prefixEnd_765220 14552802460503752108549 := by
  unfold tailWord_765220
  simp only [CollatzResearch.WordTrace]
  refine ⟨13954933143873052008206557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18606577525164069344275409 13954933143873052008206557)
  ·
    refine ⟨5233099928952394503077459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13954933143873052008206557 5233099928952394503077459)
    ·
      refine ⟨7849649893428591754616189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5233099928952394503077459 7849649893428591754616189)
      ·
        refine ⟨2943618710035721907981071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7849649893428591754616189 2943618710035721907981071)
        ·
          refine ⟨4415428065053582861971607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2943618710035721907981071 4415428065053582861971607)
          ·
            refine ⟨6623142097580374292957411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4415428065053582861971607 6623142097580374292957411)
            ·
              refine ⟨9934713146370561439436117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6623142097580374292957411 9934713146370561439436117)
              ·
                refine ⟨14552802460503752108549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 9934713146370561439436117 14552802460503752108549)
                ·
                  rfl

theorem cell23_765220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 11].length) (baseStart_765220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765220 prefixEnd_765220 := by exact prefixLift 765220
  have htrace : WordTrace (prefixWord ++ tailWord_765220) baseStart_765220 baseEnd_765220 := by
    simpa [prefixWord, tailWord_765220, baseEnd_765220] using wordTrace_append hprefix tailTrace_765220
  have hstable : (prefixWord ++ tailWord_765220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765220).length < 2 ^ (prefixWord ++ tailWord_765220).sum := by decide
  have hdescent : baseEnd_765220 < baseStart_765220 := by decide
  rcases family_descends (prefixWord ++ tailWord_765220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765231 : List Nat := [1, 1, 2, 1, 2, 1, 3, 7, 1, 2, 2]
def baseStart_765231 : Nat := 118140960795 + 765231 * 2 ^ 59
def prefixEnd_765231 : Nat := 4983230072969 + 3 ^ 40 * 765231 * 2
def baseEnd_765231 : Nat := 392931314720800763893273

theorem tailTrace_765231 : CollatzResearch.WordTrace tailWord_765231 prefixEnd_765231 392931314720800763893273 := by
  unfold tailWord_765231
  simp only [CollatzResearch.WordTrace]
  refine ⟨27910267490706252895063547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18606844993804168596709031 27910267490706252895063547)
  ·
    refine ⟨41865401236059379342595321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27910267490706252895063547 41865401236059379342595321)
    ·
      refine ⟨31399050927044534506946491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41865401236059379342595321 31399050927044534506946491)
      ·
        refine ⟨47098576390566801760419737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31399050927044534506946491 47098576390566801760419737)
        ·
          refine ⟨35323932292925101320314803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47098576390566801760419737 35323932292925101320314803)
          ·
            refine ⟨52985898439387651980472205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35323932292925101320314803 52985898439387651980472205)
            ·
              refine ⟨19869711914770369492677077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52985898439387651980472205 19869711914770369492677077)
              ·
                refine ⟨465696373002430534984619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19869711914770369492677077 465696373002430534984619)
                ·
                  refine ⟨698544559503645802476929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465696373002430534984619 698544559503645802476929)
                  ·
                    refine ⟨523908419627734351857697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 698544559503645802476929 523908419627734351857697)
                    ·
                      refine ⟨392931314720800763893273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 523908419627734351857697 392931314720800763893273)
                      ·
                        rfl

theorem cell23_765231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 1, 2, 2].length) (baseStart_765231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765231 prefixEnd_765231 := by exact prefixLift 765231
  have htrace : WordTrace (prefixWord ++ tailWord_765231) baseStart_765231 baseEnd_765231 := by
    simpa [prefixWord, tailWord_765231, baseEnd_765231] using wordTrace_append hprefix tailTrace_765231
  have hstable : (prefixWord ++ tailWord_765231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765231).length < 2 ^ (prefixWord ++ tailWord_765231).sum := by decide
  have hdescent : baseEnd_765231 < baseStart_765231 := by decide
  rcases family_descends (prefixWord ++ tailWord_765231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765234 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_765234 : Nat := 118140960795 + 765234 * 2 ^ 59
def prefixEnd_765234 : Nat := 4983230072969 + 3 ^ 40 * 765234 * 2
def baseEnd_765234 : Nat := 392932855162764252155759

theorem tailTrace_765234 : CollatzResearch.WordTrace tailWord_765234 prefixEnd_765234 392932855162764252155759 := by
  unfold tailWord_765234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6977594227423846101855689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18606917939796922938281837 6977594227423846101855689)
  ·
    refine ⟨5233195670567884576391767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6977594227423846101855689 5233195670567884576391767)
    ·
      refine ⟨7849793505851826864587651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5233195670567884576391767 7849793505851826864587651)
      ·
        refine ⟨11774690258777740296881477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7849793505851826864587651 11774690258777740296881477)
        ·
          refine ⟨2207754423520826305665277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11774690258777740296881477 2207754423520826305665277)
          ·
            refine ⟨827907908820309864624479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2207754423520826305665277 827907908820309864624479)
            ·
              refine ⟨1241861863230464796936719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827907908820309864624479 1241861863230464796936719)
              ·
                refine ⟨1862792794845697195405079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1241861863230464796936719 1862792794845697195405079)
                ·
                  refine ⟨2794189192268545793107619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1862792794845697195405079 2794189192268545793107619)
                  ·
                    refine ⟨4191283788402818689661429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2794189192268545793107619 4191283788402818689661429)
                    ·
                      refine ⟨392932855162764252155759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4191283788402818689661429 392932855162764252155759)
                      ·
                        rfl

theorem cell23_765234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_765234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765234 prefixEnd_765234 := by exact prefixLift 765234
  have htrace : WordTrace (prefixWord ++ tailWord_765234) baseStart_765234 baseEnd_765234 := by
    simpa [prefixWord, tailWord_765234, baseEnd_765234] using wordTrace_append hprefix tailTrace_765234
  have hstable : (prefixWord ++ tailWord_765234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765234).length < 2 ^ (prefixWord ++ tailWord_765234).sum := by decide
  have hdescent : baseEnd_765234 < baseStart_765234 := by decide
  rcases family_descends (prefixWord ++ tailWord_765234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765241 : List Nat := [1, 2, 1, 6, 2, 1, 2, 2, 2, 4]
def baseStart_765241 : Nat := 118140960795 + 765241 * 2 ^ 59
def prefixEnd_765241 : Nat := 4983230072969 + 3 ^ 40 * 765241 * 2
def baseEnd_765241 : Nat := 130978816509115241589409

theorem tailTrace_765241 : CollatzResearch.WordTrace tailWord_765241 prefixEnd_765241 130978816509115241589409 := by
  unfold tailWord_765241
  simp only [CollatzResearch.WordTrace]
  refine ⟨27910632220670024602927577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18607088147113349735285051 27910632220670024602927577)
  ·
    refine ⟨20932974165502518452195683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27910632220670024602927577 20932974165502518452195683)
    ·
      refine ⟨31399461248253777678293525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20932974165502518452195683 31399461248253777678293525)
      ·
        refine ⟨1471849746011895828670009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31399461248253777678293525 1471849746011895828670009)
        ·
          refine ⟨1103887309508921871502507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1471849746011895828670009 1103887309508921871502507)
          ·
            refine ⟨1655830964263382807253761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103887309508921871502507 1655830964263382807253761)
            ·
              refine ⟨1241873223197537105440321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1655830964263382807253761 1241873223197537105440321)
              ·
                refine ⟨931404917398152829080241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241873223197537105440321 931404917398152829080241)
                ·
                  refine ⟨698553688048614621810181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 931404917398152829080241 698553688048614621810181)
                  ·
                    refine ⟨130978816509115241589409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 698553688048614621810181 130978816509115241589409)
                    ·
                      rfl

theorem cell23_765241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 4].length) (baseStart_765241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765241 prefixEnd_765241 := by exact prefixLift 765241
  have htrace : WordTrace (prefixWord ++ tailWord_765241) baseStart_765241 baseEnd_765241 := by
    simpa [prefixWord, tailWord_765241, baseEnd_765241] using wordTrace_append hprefix tailTrace_765241
  have hstable : (prefixWord ++ tailWord_765241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765241).length < 2 ^ (prefixWord ++ tailWord_765241).sum := by decide
  have hdescent : baseEnd_765241 < baseStart_765241 := by decide
  rcases family_descends (prefixWord ++ tailWord_765241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765264 : List Nat := [2, 1, 1, 1, 1, 5, 1, 5, 2, 1, 3]
def baseStart_765264 : Nat := 118140960795 + 765264 * 2 ^ 59
def prefixEnd_765264 : Nat := 4983230072969 + 3 ^ 40 * 765264 * 2
def baseEnd_765264 : Nat := 392948259582399134780621

theorem tailTrace_765264 : CollatzResearch.WordTrace tailWord_765264 prefixEnd_765264 392948259582399134780621 := by
  unfold tailWord_765264
  simp only [CollatzResearch.WordTrace]
  refine ⟨13955735549793349765507423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18607647399724466354009897 13955735549793349765507423)
  ·
    refine ⟨20933603324690024648261135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13955735549793349765507423 20933603324690024648261135)
    ·
      refine ⟨31400404987035036972391703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20933603324690024648261135 31400404987035036972391703)
      ·
        refine ⟨47100607480552555458587555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31400404987035036972391703 47100607480552555458587555)
        ·
          refine ⟨70650911220828833187881333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47100607480552555458587555 70650911220828833187881333)
          ·
            refine ⟨6623522926952703111363875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70650911220828833187881333 6623522926952703111363875)
            ·
              refine ⟨9935284390429054667045813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6623522926952703111363875 9935284390429054667045813)
              ·
                refine ⟨931432911602723875035545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9935284390429054667045813 931432911602723875035545)
                ·
                  refine ⟨698574683702042906276659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 931432911602723875035545 698574683702042906276659)
                  ·
                    refine ⟨1047862025553064359414989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 698574683702042906276659 1047862025553064359414989)
                    ·
                      refine ⟨392948259582399134780621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1047862025553064359414989 392948259582399134780621)
                      ·
                        rfl

theorem cell23_765264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 2, 1, 3].length) (baseStart_765264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765264 prefixEnd_765264 := by exact prefixLift 765264
  have htrace : WordTrace (prefixWord ++ tailWord_765264) baseStart_765264 baseEnd_765264 := by
    simpa [prefixWord, tailWord_765264, baseEnd_765264] using wordTrace_append hprefix tailTrace_765264
  have hstable : (prefixWord ++ tailWord_765264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765264).length < 2 ^ (prefixWord ++ tailWord_765264).sum := by decide
  have hdescent : baseEnd_765264 < baseStart_765264 := by decide
  rcases family_descends (prefixWord ++ tailWord_765264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765274 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2]
def baseStart_765274 : Nat := 118140960795 + 765274 * 2 ^ 59
def prefixEnd_765274 : Nat := 4983230072969 + 3 ^ 40 * 765274 * 2
def baseEnd_765274 : Nat := 392953394388944095655575

theorem tailTrace_765274 : CollatzResearch.WordTrace tailWord_765274 prefixEnd_765274 392953394388944095655575 := by
  unfold tailWord_765274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6977958957387617809719719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18607890553033647492585917 6977958957387617809719719)
  ·
    refine ⟨10466938436081426714579579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6977958957387617809719719 10466938436081426714579579)
    ·
      refine ⟨15700407654122140071869369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10466938436081426714579579 15700407654122140071869369)
      ·
        refine ⟨11775305740591605053902027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15700407654122140071869369 11775305740591605053902027)
        ·
          refine ⟨17662958610887407580853041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11775305740591605053902027 17662958610887407580853041)
          ·
            refine ⟨13247218958165555685639781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17662958610887407580853041 13247218958165555685639781)
            ·
              refine ⟨2483853554656041691057459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13247218958165555685639781 2483853554656041691057459)
              ·
                refine ⟨3725780331984062536586189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2483853554656041691057459 3725780331984062536586189)
                ·
                  refine ⟨1397167624494023451219821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3725780331984062536586189 1397167624494023451219821)
                  ·
                    refine ⟨523937859185258794207433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1397167624494023451219821 523937859185258794207433)
                    ·
                      refine ⟨392953394388944095655575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 523937859185258794207433 392953394388944095655575)
                      ·
                        rfl

theorem cell23_765274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_765274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765274 prefixEnd_765274 := by exact prefixLift 765274
  have htrace : WordTrace (prefixWord ++ tailWord_765274) baseStart_765274 baseEnd_765274 := by
    simpa [prefixWord, tailWord_765274, baseEnd_765274] using wordTrace_append hprefix tailTrace_765274
  have hstable : (prefixWord ++ tailWord_765274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765274).length < 2 ^ (prefixWord ++ tailWord_765274).sum := by decide
  have hdescent : baseEnd_765274 < baseStart_765274 := by decide
  rcases family_descends (prefixWord ++ tailWord_765274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765317 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_765317 : Nat := 118140960795 + 765317 * 2 ^ 59
def prefixEnd_765317 : Nat := 4983230072969 + 3 ^ 40 * 765317 * 2
def baseEnd_765317 : Nat := 392975474057087427417877

theorem tailTrace_765317 : CollatzResearch.WordTrace tailWord_765317 prefixEnd_765317 392975474057087427417877 := by
  unfold tailWord_765317
  simp only [CollatzResearch.WordTrace]
  refine ⟨27913404168394689582694205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18608936112263126388462803 27913404168394689582694205)
  ·
    refine ⟨10467526563148008593510327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27913404168394689582694205 10467526563148008593510327)
    ·
      refine ⟨15701289844722012890265491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10467526563148008593510327 15701289844722012890265491)
      ·
        refine ⟨23551934767083019335398237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15701289844722012890265491 23551934767083019335398237)
        ·
          refine ⟨8831975537656132250774339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23551934767083019335398237 8831975537656132250774339)
          ·
            refine ⟨13247963306484198376161509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8831975537656132250774339 13247963306484198376161509)
            ·
              refine ⟨2483993119965787195530283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13247963306484198376161509 2483993119965787195530283)
              ·
                refine ⟨3725989679948680793295425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2483993119965787195530283 3725989679948680793295425)
                ·
                  refine ⟨2794492259961510594971569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3725989679948680793295425 2794492259961510594971569)
                  ·
                    refine ⟨2095869194971132946228677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2794492259961510594971569 2095869194971132946228677)
                    ·
                      refine ⟨392975474057087427417877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2095869194971132946228677 392975474057087427417877)
                      ·
                        rfl

theorem cell23_765317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_765317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765317 prefixEnd_765317 := by exact prefixLift 765317
  have htrace : WordTrace (prefixWord ++ tailWord_765317) baseStart_765317 baseEnd_765317 := by
    simpa [prefixWord, tailWord_765317, baseEnd_765317] using wordTrace_append hprefix tailTrace_765317
  have hstable : (prefixWord ++ tailWord_765317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765317).length < 2 ^ (prefixWord ++ tailWord_765317).sum := by decide
  have hdescent : baseEnd_765317 < baseStart_765317 := by decide
  rcases family_descends (prefixWord ++ tailWord_765317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765361 : List Nat := [1, 2, 2, 4, 1, 1, 5, 2, 5]
def baseStart_765361 : Nat := 118140960795 + 765361 * 2 ^ 59
def prefixEnd_765361 : Nat := 4983230072969 + 3 ^ 40 * 765361 * 2
def baseEnd_765361 : Nat := 43666451911765028363075

theorem tailTrace_765361 : CollatzResearch.WordTrace tailWord_765361 prefixEnd_765361 43666451911765028363075 := by
  unfold tailWord_765361
  simp only [CollatzResearch.WordTrace]
  refine ⟨27915008980235285097295937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18610005986823523398197291 27915008980235285097295937)
  ·
    refine ⟨20936256735176463822971953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27915008980235285097295937 20936256735176463822971953)
    ·
      refine ⟨15702192551382347867228965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20936256735176463822971953 15702192551382347867228965)
      ·
        refine ⟨2944161103384190225105431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15702192551382347867228965 2944161103384190225105431)
        ·
          refine ⟨4416241655076285337658147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2944161103384190225105431 4416241655076285337658147)
          ·
            refine ⟨6624362482614428006487221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4416241655076285337658147 6624362482614428006487221)
            ·
              refine ⟨621033982745102625608177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6624362482614428006487221 621033982745102625608177)
              ·
                refine ⟨465775487058826969206133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621033982745102625608177 465775487058826969206133)
                ·
                  refine ⟨43666451911765028363075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 465775487058826969206133 43666451911765028363075)
                  ·
                    rfl

theorem cell23_765361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 5].length) (baseStart_765361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765361 prefixEnd_765361 := by exact prefixLift 765361
  have htrace : WordTrace (prefixWord ++ tailWord_765361) baseStart_765361 baseEnd_765361 := by
    simpa [prefixWord, tailWord_765361, baseEnd_765361] using wordTrace_append hprefix tailTrace_765361
  have hstable : (prefixWord ++ tailWord_765361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765361).length < 2 ^ (prefixWord ++ tailWord_765361).sum := by decide
  have hdescent : baseEnd_765361 < baseStart_765361 := by decide
  rcases family_descends (prefixWord ++ tailWord_765361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765367 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_765367 : Nat := 118140960795 + 765367 * 2 ^ 59
def prefixEnd_765367 : Nat := 4983230072969 + 3 ^ 40 * 765367 * 2
def baseEnd_765367 : Nat := 393001148089812231792647

theorem tailTrace_765367 : CollatzResearch.WordTrace tailWord_765367 prefixEnd_765367 393001148089812231792647 := by
  unfold tailWord_765367
  simp only [CollatzResearch.WordTrace]
  refine ⟨27915227818213548122014355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18610151878809032081342903 27915227818213548122014355)
  ·
    refine ⟨41872841727320322183021533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27915227818213548122014355 41872841727320322183021533)
    ·
      refine ⟨15702315647745120818633075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41872841727320322183021533 15702315647745120818633075)
      ·
        refine ⟨23553473471617681227949613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15702315647745120818633075 23553473471617681227949613)
        ·
          refine ⟨8832552551856630460481105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23553473471617681227949613 8832552551856630460481105)
          ·
            refine ⟨6624414413892472845360829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8832552551856630460481105 6624414413892472845360829)
            ·
              refine ⟨2484155405209677317010311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6624414413892472845360829 2484155405209677317010311)
              ·
                refine ⟨3726233107814515975515467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2484155405209677317010311 3726233107814515975515467)
                ·
                  refine ⟨5589349661721773963273201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3726233107814515975515467 5589349661721773963273201)
                  ·
                    refine ⟨4192012246291330472454901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5589349661721773963273201 4192012246291330472454901)
                    ·
                      refine ⟨393001148089812231792647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4192012246291330472454901 393001148089812231792647)
                      ·
                        rfl

theorem cell23_765367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_765367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765367 prefixEnd_765367 := by exact prefixLift 765367
  have htrace : WordTrace (prefixWord ++ tailWord_765367) baseStart_765367 baseEnd_765367 := by
    simpa [prefixWord, tailWord_765367, baseEnd_765367] using wordTrace_append hprefix tailTrace_765367
  have hstable : (prefixWord ++ tailWord_765367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765367).length < 2 ^ (prefixWord ++ tailWord_765367).sum := by decide
  have hdescent : baseEnd_765367 < baseStart_765367 := by decide
  rcases family_descends (prefixWord ++ tailWord_765367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765372 : List Nat := [2, 2, 2, 4, 2, 2, 2, 1, 2, 2, 2]
def baseStart_765372 : Nat := 118140960795 + 765372 * 2 ^ 59
def prefixEnd_765372 : Nat := 4983230072969 + 3 ^ 40 * 765372 * 2
def baseEnd_765372 : Nat := 393003715493084712230125

theorem tailTrace_765372 : CollatzResearch.WordTrace tailWord_765372 prefixEnd_765372 393003715493084712230125 := by
  unfold tailWord_765372
  simp only [CollatzResearch.WordTrace]
  refine ⟨13957705091597716987973185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18610273455463622650630913 13957705091597716987973185)
  ·
    refine ⟨10468278818698287740979889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13957705091597716987973185 10468278818698287740979889)
    ·
      refine ⟨7851209114023715805734917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10468278818698287740979889 7851209114023715805734917)
      ·
        refine ⟨1472101708879446713575297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7851209114023715805734917 1472101708879446713575297)
        ·
          refine ⟨1104076281659585035181473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1472101708879446713575297 1104076281659585035181473)
          ·
            refine ⟨828057211244688776386105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1104076281659585035181473 828057211244688776386105)
            ·
              refine ⟨621042908433516582289579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828057211244688776386105 621042908433516582289579)
              ·
                refine ⟨931564362650274873434369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621042908433516582289579 931564362650274873434369)
                ·
                  refine ⟨698673271987706155075777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 931564362650274873434369 698673271987706155075777)
                  ·
                    refine ⟨524004953990779616306833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 698673271987706155075777 524004953990779616306833)
                    ·
                      refine ⟨393003715493084712230125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 524004953990779616306833 393003715493084712230125)
                      ·
                        rfl

theorem cell23_765372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_765372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765372 prefixEnd_765372 := by exact prefixLift 765372
  have htrace : WordTrace (prefixWord ++ tailWord_765372) baseStart_765372 baseEnd_765372 := by
    simpa [prefixWord, tailWord_765372, baseEnd_765372] using wordTrace_append hprefix tailTrace_765372
  have hstable : (prefixWord ++ tailWord_765372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765372).length < 2 ^ (prefixWord ++ tailWord_765372).sum := by decide
  have hdescent : baseEnd_765372 < baseStart_765372 := by decide
  rcases family_descends (prefixWord ++ tailWord_765372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765407 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 6]
def baseStart_765407 : Nat := 118140960795 + 765407 * 2 ^ 59
def prefixEnd_765407 : Nat := 4983230072969 + 3 ^ 40 * 765407 * 2
def baseEnd_765407 : Nat := 393021687315992075292463

theorem tailTrace_765407 : CollatzResearch.WordTrace tailWord_765407 prefixEnd_765407 393021687315992075292463 := by
  unfold tailWord_765407
  simp only [CollatzResearch.WordTrace]
  refine ⟨27916686738068634953470475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18611124492045756635646983 27916686738068634953470475)
  ·
    refine ⟨41875030107102952430205713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27916686738068634953470475 41875030107102952430205713)
    ·
      refine ⟨31406272580327214322654285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41875030107102952430205713 31406272580327214322654285)
      ·
        refine ⟨11777352217622705370995357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31406272580327214322654285 11777352217622705370995357)
        ·
          refine ⟨4416507081608514514123259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11777352217622705370995357 4416507081608514514123259)
          ·
            refine ⟨6624760622412771771184889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4416507081608514514123259 6624760622412771771184889)
            ·
              refine ⟨4968570466809578828388667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6624760622412771771184889 4968570466809578828388667)
              ·
                refine ⟨7452855700214368242583001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4968570466809578828388667 7452855700214368242583001)
                ·
                  refine ⟨5589641775160776181937251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7452855700214368242583001 5589641775160776181937251)
                  ·
                    refine ⟨8384462662741164272905877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5589641775160776181937251 8384462662741164272905877)
                    ·
                      refine ⟨393021687315992075292463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8384462662741164272905877 393021687315992075292463)
                      ·
                        rfl

theorem cell23_765407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_765407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765407 prefixEnd_765407 := by exact prefixLift 765407
  have htrace : WordTrace (prefixWord ++ tailWord_765407) baseStart_765407 baseEnd_765407 := by
    simpa [prefixWord, tailWord_765407, baseEnd_765407] using wordTrace_append hprefix tailTrace_765407
  have hstable : (prefixWord ++ tailWord_765407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765407).length < 2 ^ (prefixWord ++ tailWord_765407).sum := by decide
  have hdescent : baseEnd_765407 < baseStart_765407 := by decide
  rcases family_descends (prefixWord ++ tailWord_765407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765471 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 2, 3, 2]
def baseStart_765471 : Nat := 118140960795 + 765471 * 2 ^ 59
def prefixEnd_765471 : Nat := 4983230072969 + 3 ^ 40 * 765471 * 2
def baseEnd_765471 : Nat := 393054550077879824892169

theorem tailTrace_765471 : CollatzResearch.WordTrace tailWord_765471 prefixEnd_765471 393054550077879824892169 := by
  unfold tailWord_765471
  simp only [CollatzResearch.WordTrace]
  refine ⟨27919021009836773883800267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18612680673224515922533511 27919021009836773883800267)
  ·
    refine ⟨41878531514755160825700401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27919021009836773883800267 41878531514755160825700401)
    ·
      refine ⟨31408898636066370619275301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41878531514755160825700401 31408898636066370619275301)
      ·
        refine ⟨5889168494262444491114119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31408898636066370619275301 5889168494262444491114119)
        ·
          refine ⟨8833752741393666736671179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5889168494262444491114119 8833752741393666736671179)
          ·
            refine ⟨13250629112090500105006769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8833752741393666736671179 13250629112090500105006769)
            ·
              refine ⟨9937971834067875078755077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13250629112090500105006769 9937971834067875078755077)
              ·
                refine ⟨1863369718887726577266577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9937971834067875078755077 1863369718887726577266577)
                ·
                  refine ⟨1397527289165794932949933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1863369718887726577266577 1397527289165794932949933)
                  ·
                    refine ⟨524072733437173099856225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1397527289165794932949933 524072733437173099856225)
                    ·
                      refine ⟨393054550077879824892169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 524072733437173099856225 393054550077879824892169)
                      ·
                        rfl

theorem cell23_765471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_765471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765471 prefixEnd_765471 := by exact prefixLift 765471
  have htrace : WordTrace (prefixWord ++ tailWord_765471) baseStart_765471 baseEnd_765471 := by
    simpa [prefixWord, tailWord_765471, baseEnd_765471] using wordTrace_append hprefix tailTrace_765471
  have hstable : (prefixWord ++ tailWord_765471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765471).length < 2 ^ (prefixWord ++ tailWord_765471).sum := by decide
  have hdescent : baseEnd_765471 < baseStart_765471 := by decide
  rcases family_descends (prefixWord ++ tailWord_765471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765514 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_765514 : Nat := 118140960795 + 765514 * 2 ^ 59
def prefixEnd_765514 : Nat := 4983230072969 + 3 ^ 40 * 765514 * 2
def baseEnd_765514 : Nat := 393076629746023156654471

theorem tailTrace_765514 : CollatzResearch.WordTrace tailWord_765514 prefixEnd_765514 393076629746023156654471 := by
  unfold tailWord_765514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6980147337170248056903899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18613726232453994818410397 6980147337170248056903899)
  ·
    refine ⟨10470221005755372085355849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6980147337170248056903899 10470221005755372085355849)
    ·
      refine ⟨7852665754316529064016887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10470221005755372085355849 7852665754316529064016887)
      ·
        refine ⟨11778998631474793596025331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7852665754316529064016887 11778998631474793596025331)
        ·
          refine ⟨17668497947212190394037997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11778998631474793596025331 17668497947212190394037997)
          ·
            refine ⟨6625686730204571397764249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17668497947212190394037997 6625686730204571397764249)
            ·
              refine ⟨4969265047653428548323187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6625686730204571397764249 4969265047653428548323187)
              ·
                refine ⟨7453897571480142822484781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4969265047653428548323187 7453897571480142822484781)
                ·
                  refine ⟨2795211589305053558431793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7453897571480142822484781 2795211589305053558431793)
                  ·
                    refine ⟨2096408691978790168823845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2795211589305053558431793 2096408691978790168823845)
                    ·
                      refine ⟨393076629746023156654471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2096408691978790168823845 393076629746023156654471)
                      ·
                        rfl

theorem cell23_765514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_765514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765514 prefixEnd_765514 := by exact prefixLift 765514
  have htrace : WordTrace (prefixWord ++ tailWord_765514) baseStart_765514 baseEnd_765514 := by
    simpa [prefixWord, tailWord_765514, baseEnd_765514] using wordTrace_append hprefix tailTrace_765514
  have hstable : (prefixWord ++ tailWord_765514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765514).length < 2 ^ (prefixWord ++ tailWord_765514).sum := by decide
  have hdescent : baseEnd_765514 < baseStart_765514 := by decide
  rcases family_descends (prefixWord ++ tailWord_765514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765521 : List Nat := [1, 2, 2, 1, 3, 2, 1, 5, 1, 2, 3]
def baseStart_765521 : Nat := 118140960795 + 765521 * 2 ^ 59
def prefixEnd_765521 : Nat := 4983230072969 + 3 ^ 40 * 765521 * 2
def baseEnd_765521 : Nat := 393080224110604629266939

theorem tailTrace_765521 : CollatzResearch.WordTrace tailWord_765521 prefixEnd_765521 393080224110604629266939 := by
  unfold tailWord_765521
  simp only [CollatzResearch.WordTrace]
  refine ⟨27920844659655632423120417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18613896439770421615413611 27920844659655632423120417)
  ·
    refine ⟨20940633494741724317340313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27920844659655632423120417 20940633494741724317340313)
    ·
      refine ⟨15705475121056293238005235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20940633494741724317340313 15705475121056293238005235)
      ·
        refine ⟨23558212681584439857007853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15705475121056293238005235 23558212681584439857007853)
        ·
          refine ⟨8834329755594164946377945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23558212681584439857007853 8834329755594164946377945)
          ·
            refine ⟨6625747316695623709783459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8834329755594164946377945 6625747316695623709783459)
            ·
              refine ⟨9938620975043435564675189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6625747316695623709783459 9938620975043435564675189)
              ·
                refine ⟨931745716410322084188299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9938620975043435564675189 931745716410322084188299)
                ·
                  refine ⟨1397618574615483126282449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931745716410322084188299 1397618574615483126282449)
                  ·
                    refine ⟨1048213930961612344711837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1397618574615483126282449 1048213930961612344711837)
                    ·
                      refine ⟨393080224110604629266939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1048213930961612344711837 393080224110604629266939)
                      ·
                        rfl

theorem cell23_765521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_765521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765521 prefixEnd_765521 := by exact prefixLift 765521
  have htrace : WordTrace (prefixWord ++ tailWord_765521) baseStart_765521 baseEnd_765521 := by
    simpa [prefixWord, tailWord_765521, baseEnd_765521] using wordTrace_append hprefix tailTrace_765521
  have hstable : (prefixWord ++ tailWord_765521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765521).length < 2 ^ (prefixWord ++ tailWord_765521).sum := by decide
  have hdescent : baseEnd_765521 < baseStart_765521 := by decide
  rcases family_descends (prefixWord ++ tailWord_765521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765586 : List Nat := [3, 2, 3, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_765586 : Nat := 118140960795 + 765586 * 2 ^ 59
def prefixEnd_765586 : Nat := 4983230072969 + 3 ^ 40 * 765586 * 2
def baseEnd_765586 : Nat := 393113600353146874954141

theorem tailTrace_765586 : CollatzResearch.WordTrace tailWord_765586 prefixEnd_765586 393113600353146874954141 := by
  unfold tailWord_765586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6980803851105037131059153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18615476936280099016157741 6980803851105037131059153)
  ·
    refine ⟨5235602888328777848294365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6980803851105037131059153 5235602888328777848294365)
    ·
      refine ⟨1963351083123291693110387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5235602888328777848294365 1963351083123291693110387)
      ·
        refine ⟨2945026624684937539665581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1963351083123291693110387 2945026624684937539665581)
        ·
          refine ⟨1104384984256851577374593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2945026624684937539665581 1104384984256851577374593)
          ·
            refine ⟨828288738192638683030945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1104384984256851577374593 828288738192638683030945)
            ·
              refine ⟨621216553644479012273209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828288738192638683030945 621216553644479012273209)
              ·
                refine ⟨465912415233359259204907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621216553644479012273209 465912415233359259204907)
                ·
                  refine ⟨698868622850038888807361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465912415233359259204907 698868622850038888807361)
                  ·
                    refine ⟨524151467137529166605521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 698868622850038888807361 524151467137529166605521)
                    ·
                      refine ⟨393113600353146874954141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 524151467137529166605521 393113600353146874954141)
                      ·
                        rfl

theorem cell23_765586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_765586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765586 prefixEnd_765586 := by exact prefixLift 765586
  have htrace : WordTrace (prefixWord ++ tailWord_765586) baseStart_765586 baseEnd_765586 := by
    simpa [prefixWord, tailWord_765586, baseEnd_765586] using wordTrace_append hprefix tailTrace_765586
  have hstable : (prefixWord ++ tailWord_765586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765586).length < 2 ^ (prefixWord ++ tailWord_765586).sum := by decide
  have hdescent : baseEnd_765586 < baseStart_765586 := by decide
  rcases family_descends (prefixWord ++ tailWord_765586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765601 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 2, 6]
def baseStart_765601 : Nat := 118140960795 + 765601 * 2 ^ 59
def prefixEnd_765601 : Nat := 4983230072969 + 3 ^ 40 * 765601 * 2
def baseEnd_765601 : Nat := 131040434187654772088857

theorem tailTrace_765601 : CollatzResearch.WordTrace tailWord_765601 prefixEnd_765601 131040434187654772088857 := by
  unfold tailWord_765601
  simp only [CollatzResearch.WordTrace]
  refine ⟨27923762499365806086032657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18615841666243870724021771 27923762499365806086032657)
  ·
    refine ⟨20942821874524354564524493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27923762499365806086032657 20942821874524354564524493)
    ·
      refine ⟨7853558202946632961696685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20942821874524354564524493 7853558202946632961696685)
      ·
        refine ⟨2945084326104987360636257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7853558202946632961696685 2945084326104987360636257)
        ·
          refine ⟨2208813244578740520477193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2945084326104987360636257 2208813244578740520477193)
          ·
            refine ⟨1656609933434055390357895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2208813244578740520477193 1656609933434055390357895)
            ·
              refine ⟨2484914900151083085536843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656609933434055390357895 2484914900151083085536843)
              ·
                refine ⟨3727372350226624628305265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2484914900151083085536843 3727372350226624628305265)
                ·
                  refine ⟨2795529262669968471228949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3727372350226624628305265 2795529262669968471228949)
                  ·
                    refine ⟨131040434187654772088857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2795529262669968471228949 131040434187654772088857)
                    ·
                      rfl

theorem cell23_765601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_765601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765601 prefixEnd_765601 := by exact prefixLift 765601
  have htrace : WordTrace (prefixWord ++ tailWord_765601) baseStart_765601 baseEnd_765601 := by
    simpa [prefixWord, tailWord_765601, baseEnd_765601] using wordTrace_append hprefix tailTrace_765601
  have hstable : (prefixWord ++ tailWord_765601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765601).length < 2 ^ (prefixWord ++ tailWord_765601).sum := by decide
  have hdescent : baseEnd_765601 < baseStart_765601 := by decide
  rcases family_descends (prefixWord ++ tailWord_765601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765651 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 6, 5, 2]
def baseStart_765651 : Nat := 118140960795 + 765651 * 2 ^ 59
def prefixEnd_765651 : Nat := 4983230072969 + 3 ^ 40 * 765651 * 2
def baseEnd_765651 : Nat := 393146976595689120641341

theorem tailTrace_765651 : CollatzResearch.WordTrace tailWord_765651 prefixEnd_765651 393146976595689120641341 := by
  unfold tailWord_765651
  simp only [CollatzResearch.WordTrace]
  refine ⟨27925586149184664625352807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18617057432789776416901871 27925586149184664625352807)
  ·
    refine ⟨41888379223776996938029211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27925586149184664625352807 41888379223776996938029211)
    ·
      refine ⟨62832568835665495407043817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41888379223776996938029211 62832568835665495407043817)
      ·
        refine ⟨47124426626749121555282863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62832568835665495407043817 47124426626749121555282863)
        ·
          refine ⟨70686639940123682332924295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47124426626749121555282863 70686639940123682332924295)
          ·
            refine ⟨106029959910185523499386443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70686639940123682332924295 106029959910185523499386443)
            ·
              refine ⟨159044939865278285249079665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106029959910185523499386443 159044939865278285249079665)
              ·
                refine ⟨119283704898958713936809749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159044939865278285249079665 119283704898958713936809749)
                ·
                  refine ⟨5591423667138689715787957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119283704898958713936809749 5591423667138689715787957)
                  ·
                    refine ⟨524195968794252160855121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5591423667138689715787957 524195968794252160855121)
                    ·
                      refine ⟨393146976595689120641341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 524195968794252160855121 393146976595689120641341)
                      ·
                        rfl

theorem cell23_765651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 5, 2].length) (baseStart_765651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765651 prefixEnd_765651 := by exact prefixLift 765651
  have htrace : WordTrace (prefixWord ++ tailWord_765651) baseStart_765651 baseEnd_765651 := by
    simpa [prefixWord, tailWord_765651, baseEnd_765651] using wordTrace_append hprefix tailTrace_765651
  have hstable : (prefixWord ++ tailWord_765651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765651).length < 2 ^ (prefixWord ++ tailWord_765651).sum := by decide
  have hdescent : baseEnd_765651 < baseStart_765651 := by decide
  rcases family_descends (prefixWord ++ tailWord_765651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765681 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_765681 : Nat := 118140960795 + 765681 * 2 ^ 59
def prefixEnd_765681 : Nat := 4983230072969 + 3 ^ 40 * 765681 * 2
def baseEnd_765681 : Nat := 393162381015324003266203

theorem tailTrace_765681 : CollatzResearch.WordTrace tailWord_765681 prefixEnd_765681 393162381015324003266203 := by
  unfold tailWord_765681
  simp only [CollatzResearch.WordTrace]
  refine ⟨27926680339075979748944897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18617786892717319832629931 27926680339075979748944897)
  ·
    refine ⟨20945010254306984811708673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27926680339075979748944897 20945010254306984811708673)
    ·
      refine ⟨15708757690730238608781505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20945010254306984811708673 15708757690730238608781505)
      ·
        refine ⟨11781568268047678956586129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15708757690730238608781505 11781568268047678956586129)
        ·
          refine ⟨8836176201035759217439597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11781568268047678956586129 8836176201035759217439597)
          ·
            refine ⟨3313566075388409706539849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8836176201035759217439597 3313566075388409706539849)
            ·
              refine ⟨2485174556541307279904887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3313566075388409706539849 2485174556541307279904887)
              ·
                refine ⟨3727761834811960919857331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2485174556541307279904887 3727761834811960919857331)
                ·
                  refine ⟨5591642752217941379785997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727761834811960919857331 5591642752217941379785997)
                  ·
                    refine ⟨2096866032081728017419749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5591642752217941379785997 2096866032081728017419749)
                    ·
                      refine ⟨393162381015324003266203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2096866032081728017419749 393162381015324003266203)
                      ·
                        rfl

theorem cell23_765681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_765681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765681 prefixEnd_765681 := by exact prefixLift 765681
  have htrace : WordTrace (prefixWord ++ tailWord_765681) baseStart_765681 baseEnd_765681 := by
    simpa [prefixWord, tailWord_765681, baseEnd_765681] using wordTrace_append hprefix tailTrace_765681
  have hstable : (prefixWord ++ tailWord_765681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765681).length < 2 ^ (prefixWord ++ tailWord_765681).sum := by decide
  have hdescent : baseEnd_765681 < baseStart_765681 := by decide
  rcases family_descends (prefixWord ++ tailWord_765681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765708 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 3, 4]
def baseStart_765708 : Nat := 118140960795 + 765708 * 2 ^ 59
def prefixEnd_765708 : Nat := 4983230072969 + 3 ^ 40 * 765708 * 2
def baseEnd_765708 : Nat := 131058748330998465876193

theorem tailTrace_765708 : CollatzResearch.WordTrace tailWord_765708 prefixEnd_765708 131058748330998465876193 := by
  unfold tailWord_765708
  simp only [CollatzResearch.WordTrace]
  refine ⟨13963832554989081680088889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18618443406652108906785185 13963832554989081680088889)
  ·
    refine ⟨10472874416241811260066667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13963832554989081680088889 10472874416241811260066667)
    ·
      refine ⟨15709311624362716890100001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10472874416241811260066667 15709311624362716890100001)
      ·
        refine ⟨11781983718272037667575001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15709311624362716890100001 11781983718272037667575001)
        ·
          refine ⟨8836487788704028250681251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11781983718272037667575001 8836487788704028250681251)
          ·
            refine ⟨13254731683056042376021877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836487788704028250681251 13254731683056042376021877)
            ·
              refine ⟨1242631095286503972752051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13254731683056042376021877 1242631095286503972752051)
              ·
                refine ⟨1863946642929755959128077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242631095286503972752051 1863946642929755959128077)
                ·
                  refine ⟨698979991098658484673029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1863946642929755959128077 698979991098658484673029)
                  ·
                    refine ⟨131058748330998465876193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 698979991098658484673029 131058748330998465876193)
                    ·
                      rfl

theorem cell23_765708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_765708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765708 prefixEnd_765708 := by exact prefixLift 765708
  have htrace : WordTrace (prefixWord ++ tailWord_765708) baseStart_765708 baseEnd_765708 := by
    simpa [prefixWord, tailWord_765708, baseEnd_765708] using wordTrace_append hprefix tailTrace_765708
  have hstable : (prefixWord ++ tailWord_765708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765708).length < 2 ^ (prefixWord ++ tailWord_765708).sum := by decide
  have hdescent : baseEnd_765708 < baseStart_765708 := by decide
  rcases family_descends (prefixWord ++ tailWord_765708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765731 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 3]
def baseStart_765731 : Nat := 118140960795 + 765731 * 2 ^ 59
def prefixEnd_765731 : Nat := 4983230072969 + 3 ^ 40 * 765731 * 2
def baseEnd_765731 : Nat := 393188055048048807640973

theorem tailTrace_765731 : CollatzResearch.WordTrace tailWord_765731 prefixEnd_765731 393188055048048807640973 := by
  unfold tailWord_765731
  simp only [CollatzResearch.WordTrace]
  refine ⟨27928503988894838288265047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18619002659263225525510031 27928503988894838288265047)
  ·
    refine ⟨41892755983342257432397571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27928503988894838288265047 41892755983342257432397571)
    ·
      refine ⟨62839133975013386148596357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41892755983342257432397571 62839133975013386148596357)
      ·
        refine ⟨11782337620315009902861817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62839133975013386148596357 11782337620315009902861817)
        ·
          refine ⟨8836753215236257427146363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11782337620315009902861817 8836753215236257427146363)
          ·
            refine ⟨13255129822854386140719545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836753215236257427146363 13255129822854386140719545)
            ·
              refine ⟨9941347367140789605539659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13255129822854386140719545 9941347367140789605539659)
              ·
                refine ⟨14912021050711184408309489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9941347367140789605539659 14912021050711184408309489)
                ·
                  refine ⟨11184015788033388306232117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14912021050711184408309489 11184015788033388306232117)
                  ·
                    refine ⟨1048501480128130153709261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11184015788033388306232117 1048501480128130153709261)
                    ·
                      refine ⟨393188055048048807640973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1048501480128130153709261 393188055048048807640973)
                      ·
                        rfl

theorem cell23_765731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_765731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765731 prefixEnd_765731 := by exact prefixLift 765731
  have htrace : WordTrace (prefixWord ++ tailWord_765731) baseStart_765731 baseEnd_765731 := by
    simpa [prefixWord, tailWord_765731, baseEnd_765731] using wordTrace_append hprefix tailTrace_765731
  have hstable : (prefixWord ++ tailWord_765731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765731).length < 2 ^ (prefixWord ++ tailWord_765731).sum := by decide
  have hdescent : baseEnd_765731 < baseStart_765731 := by decide
  rcases family_descends (prefixWord ++ tailWord_765731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765759 : List Nat := [1, 1, 2, 2, 6, 2, 2, 2, 1, 4]
def baseStart_765759 : Nat := 118140960795 + 765759 * 2 ^ 59
def prefixEnd_765759 : Nat := 4983230072969 + 3 ^ 40 * 765759 * 2
def baseEnd_765759 : Nat := 131067477502124899363615

theorem tailTrace_765759 : CollatzResearch.WordTrace tailWord_765759 prefixEnd_765759 131067477502124899363615 := by
  unfold tailWord_765759
  simp only [CollatzResearch.WordTrace]
  refine ⟨27929525232793399070284331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18619683488528932713522887 27929525232793399070284331)
  ·
    refine ⟨41894287849190098605426497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27929525232793399070284331 41894287849190098605426497)
    ·
      refine ⟨31420715886892573954069873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41894287849190098605426497 31420715886892573954069873)
      ·
        refine ⟨23565536915169430465552405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31420715886892573954069873 23565536915169430465552405)
        ·
          refine ⟨1104634542898567053072769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23565536915169430465552405 1104634542898567053072769)
          ·
            refine ⟨828475907173925289804577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1104634542898567053072769 828475907173925289804577)
            ·
              refine ⟨621356930380443967353433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828475907173925289804577 621356930380443967353433)
              ·
                refine ⟨466017697785332975515075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621356930380443967353433 466017697785332975515075)
                ·
                  refine ⟨699026546677999463272613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466017697785332975515075 699026546677999463272613)
                  ·
                    refine ⟨131067477502124899363615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 699026546677999463272613 131067477502124899363615)
                    ·
                      rfl

theorem cell23_765759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 1, 4].length) (baseStart_765759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765759 prefixEnd_765759 := by exact prefixLift 765759
  have htrace : WordTrace (prefixWord ++ tailWord_765759) baseStart_765759 baseEnd_765759 := by
    simpa [prefixWord, tailWord_765759, baseEnd_765759] using wordTrace_append hprefix tailTrace_765759
  have hstable : (prefixWord ++ tailWord_765759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765759).length < 2 ^ (prefixWord ++ tailWord_765759).sum := by decide
  have hdescent : baseEnd_765759 < baseStart_765759 := by decide
  rcases family_descends (prefixWord ++ tailWord_765759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765792 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 2, 3, 2]
def baseStart_765792 : Nat := 118140960795 + 765792 * 2 ^ 59
def prefixEnd_765792 : Nat := 4983230072969 + 3 ^ 40 * 765792 * 2
def baseEnd_765792 : Nat := 393219377367973068978193

theorem tailTrace_765792 : CollatzResearch.WordTrace tailWord_765792 prefixEnd_765792 393219377367973068978193 := by
  unfold tailWord_765792
  simp only [CollatzResearch.WordTrace]
  refine ⟨13965364420836922853117815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18620485894449230470823753 13965364420836922853117815)
  ·
    refine ⟨20948046631255384279676723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13965364420836922853117815 20948046631255384279676723)
    ·
      refine ⟨31422069946883076419515085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20948046631255384279676723 31422069946883076419515085)
      ·
        refine ⟨11783276230081153657318157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31422069946883076419515085 11783276230081153657318157)
        ·
          refine ⟨4418728586280432621494309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11783276230081153657318157 4418728586280432621494309)
          ·
            refine ⟨828511609927581116530183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4418728586280432621494309 828511609927581116530183)
            ·
              refine ⟨1242767414891371674795275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828511609927581116530183 1242767414891371674795275)
              ·
                refine ⟨1864151122337057512192913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242767414891371674795275 1864151122337057512192913)
                ·
                  refine ⟨1398113341752793134144685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1864151122337057512192913 1398113341752793134144685)
                  ·
                    refine ⟨524292503157297425304257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398113341752793134144685 524292503157297425304257)
                    ·
                      refine ⟨393219377367973068978193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 524292503157297425304257 393219377367973068978193)
                      ·
                        rfl

theorem cell23_765792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_765792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765792 prefixEnd_765792 := by exact prefixLift 765792
  have htrace : WordTrace (prefixWord ++ tailWord_765792) baseStart_765792 baseEnd_765792 := by
    simpa [prefixWord, tailWord_765792, baseEnd_765792] using wordTrace_append hprefix tailTrace_765792
  have hstable : (prefixWord ++ tailWord_765792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765792).length < 2 ^ (prefixWord ++ tailWord_765792).sum := by decide
  have hdescent : baseEnd_765792 < baseStart_765792 := by decide
  rcases family_descends (prefixWord ++ tailWord_765792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765802 : List Nat := [3, 1, 3, 4, 1, 1, 1, 3, 1, 5]
def baseStart_765802 : Nat := 118140960795 + 765802 * 2 ^ 59
def prefixEnd_765802 : Nat := 4983230072969 + 3 ^ 40 * 765802 * 2
def baseEnd_765802 : Nat := 131074837391506009951049

theorem tailTrace_765802 : CollatzResearch.WordTrace tailWord_765802 prefixEnd_765802 131074837391506009951049 := by
  unfold tailWord_765802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6982773392909404353524915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18620729047758411609399773 6982773392909404353524915)
  ·
    refine ⟨10474160089364106530287373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6982773392909404353524915 10474160089364106530287373)
    ·
      refine ⟨3927810033511539948857765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10474160089364106530287373 3927810033511539948857765)
      ·
        refine ⟨736464381283413740410831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3927810033511539948857765 736464381283413740410831)
        ·
          refine ⟨1104696571925120610616247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736464381283413740410831 1104696571925120610616247)
          ·
            refine ⟨1657044857887680915924371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104696571925120610616247 1657044857887680915924371)
            ·
              refine ⟨2485567286831521373886557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657044857887680915924371 2485567286831521373886557)
              ·
                refine ⟨932087732561820515207459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2485567286831521373886557 932087732561820515207459)
                ·
                  refine ⟨1398131598842730772811189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932087732561820515207459 1398131598842730772811189)
                  ·
                    refine ⟨131074837391506009951049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1398131598842730772811189 131074837391506009951049)
                    ·
                      rfl

theorem cell23_765802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_765802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765802 prefixEnd_765802 := by exact prefixLift 765802
  have htrace : WordTrace (prefixWord ++ tailWord_765802) baseStart_765802 baseEnd_765802 := by
    simpa [prefixWord, tailWord_765802, baseEnd_765802] using wordTrace_append hprefix tailTrace_765802
  have hstable : (prefixWord ++ tailWord_765802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765802).length < 2 ^ (prefixWord ++ tailWord_765802).sum := by decide
  have hdescent : baseEnd_765802 < baseStart_765802 := by decide
  rcases family_descends (prefixWord ++ tailWord_765802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765821 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_765821 : Nat := 118140960795 + 765821 * 2 ^ 59
def prefixEnd_765821 : Nat := 4983230072969 + 3 ^ 40 * 765821 * 2
def baseEnd_765821 : Nat := 393234268306953455515559

theorem tailTrace_765821 : CollatzResearch.WordTrace tailWord_765821 prefixEnd_765821 393234268306953455515559 := by
  unfold tailWord_765821
  simp only [CollatzResearch.WordTrace]
  refine ⟨27931786558568783659041317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18621191039045855772694211 27931786558568783659041317)
  ·
    refine ⟨5237209979731646936070247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27931786558568783659041317 5237209979731646936070247)
    ·
      refine ⟨7855814969597470404105371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5237209979731646936070247 7855814969597470404105371)
      ·
        refine ⟨11783722454396205606158057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7855814969597470404105371 11783722454396205606158057)
        ·
          refine ⟨8837791840797154204618543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11783722454396205606158057 8837791840797154204618543)
          ·
            refine ⟨13256687761195731306927815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8837791840797154204618543 13256687761195731306927815)
            ·
              refine ⟨19885031641793596960391723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13256687761195731306927815 19885031641793596960391723)
              ·
                refine ⟨29827547462690395440587585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19885031641793596960391723 29827547462690395440587585)
                ·
                  refine ⟨22370660597017796580440689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29827547462690395440587585 22370660597017796580440689)
                  ·
                    refine ⟨16777995447763347435330517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22370660597017796580440689 16777995447763347435330517)
                    ·
                      refine ⟨393234268306953455515559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16777995447763347435330517 393234268306953455515559)
                      ·
                        rfl

theorem cell23_765821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_765821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765821 prefixEnd_765821 := by exact prefixLift 765821
  have htrace : WordTrace (prefixWord ++ tailWord_765821) baseStart_765821 baseEnd_765821 := by
    simpa [prefixWord, tailWord_765821, baseEnd_765821] using wordTrace_append hprefix tailTrace_765821
  have hstable : (prefixWord ++ tailWord_765821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765821).length < 2 ^ (prefixWord ++ tailWord_765821).sum := by decide
  have hdescent : baseEnd_765821 < baseStart_765821 := by decide
  rcases family_descends (prefixWord ++ tailWord_765821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765832 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 1, 6]
def baseStart_765832 : Nat := 118140960795 + 765832 * 2 ^ 59
def prefixEnd_765832 : Nat := 4983230072969 + 3 ^ 40 * 765832 * 2
def baseEnd_765832 : Nat := 131079972198050970826003

theorem tailTrace_765832 : CollatzResearch.WordTrace tailWord_765832 prefixEnd_765832 131079972198050970826003 := by
  unfold tailWord_765832
  simp only [CollatzResearch.WordTrace]
  refine ⟨13966093880764466268845875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18621458507685955025127833 13966093880764466268845875)
  ·
    refine ⟨20949140821146699403268813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13966093880764466268845875 20949140821146699403268813)
    ·
      refine ⟨7855927807930012276225805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20949140821146699403268813 7855927807930012276225805)
      ·
        refine ⟨2945972927973754603584677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7855927807930012276225805 2945972927973754603584677)
        ·
          refine ⟨552369923995078988172127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2945972927973754603584677 552369923995078988172127)
          ·
            refine ⟨828554885992618482258191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552369923995078988172127 828554885992618482258191)
            ·
              refine ⟨1242832328988927723387287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828554885992618482258191 1242832328988927723387287)
              ·
                refine ⟨1864248493483391585080931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242832328988927723387287 1864248493483391585080931)
                ·
                  refine ⟨2796372740225087377621397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864248493483391585080931 2796372740225087377621397)
                  ·
                    refine ⟨131079972198050970826003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2796372740225087377621397 131079972198050970826003)
                    ·
                      rfl

theorem cell23_765832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_765832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765832 prefixEnd_765832 := by exact prefixLift 765832
  have htrace : WordTrace (prefixWord ++ tailWord_765832) baseStart_765832 baseEnd_765832 := by
    simpa [prefixWord, tailWord_765832, baseEnd_765832] using wordTrace_append hprefix tailTrace_765832
  have hstable : (prefixWord ++ tailWord_765832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765832).length < 2 ^ (prefixWord ++ tailWord_765832).sum := by decide
  have hdescent : baseEnd_765832 < baseStart_765832 := by decide
  rcases family_descends (prefixWord ++ tailWord_765832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765841 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 2, 7]
def baseStart_765841 : Nat := 118140960795 + 765841 * 2 ^ 59
def prefixEnd_765841 : Nat := 4983230072969 + 3 ^ 40 * 765841 * 2
def baseEnd_765841 : Nat := 131081512640014459088489

theorem tailTrace_765841 : CollatzResearch.WordTrace tailWord_765841 prefixEnd_765841 131081512640014459088489 := by
  unfold tailWord_765841
  simp only [CollatzResearch.WordTrace]
  refine ⟨27932516018496327074769377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18621677345664218049846251 27932516018496327074769377)
  ·
    refine ⟨20949387013872245306077033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27932516018496327074769377 20949387013872245306077033)
    ·
      refine ⟨15712040260404183979557775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20949387013872245306077033 15712040260404183979557775)
      ·
        refine ⟨23568060390606275969336663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15712040260404183979557775 23568060390606275969336663)
        ·
          refine ⟨35352090585909413954004995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23568060390606275969336663 35352090585909413954004995)
          ·
            refine ⟨53028135878864120931007493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35352090585909413954004995 53028135878864120931007493)
            ·
              refine ⟨9942775477287022674563905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53028135878864120931007493 9942775477287022674563905)
              ·
                refine ⟨7457081607965267005922929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9942775477287022674563905 7457081607965267005922929)
                ·
                  refine ⟨5592811205973950254442197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7457081607965267005922929 5592811205973950254442197)
                  ·
                    refine ⟨131081512640014459088489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5592811205973950254442197 131081512640014459088489)
                    ·
                      rfl

theorem cell23_765841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_765841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765841 prefixEnd_765841 := by exact prefixLift 765841
  have htrace : WordTrace (prefixWord ++ tailWord_765841) baseStart_765841 baseEnd_765841 := by
    simpa [prefixWord, tailWord_765841, baseEnd_765841] using wordTrace_append hprefix tailTrace_765841
  have hstable : (prefixWord ++ tailWord_765841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765841).length < 2 ^ (prefixWord ++ tailWord_765841).sum := by decide
  have hdescent : baseEnd_765841 < baseStart_765841 := by decide
  rcases family_descends (prefixWord ++ tailWord_765841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765842 : List Nat := [3, 2, 3, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_765842 : Nat := 118140960795 + 765842 * 2 ^ 59
def prefixEnd_765842 : Nat := 4983230072969 + 3 ^ 40 * 765842 * 2
def baseEnd_765842 : Nat := 393245051400697873352963

theorem tailTrace_765842 : CollatzResearch.WordTrace tailWord_765842 prefixEnd_765842 393245051400697873352963 := by
  unfold tailWord_765842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6983138122873176061388945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18621701660995136163703853 6983138122873176061388945)
  ·
    refine ⟨5237353592154882046041709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6983138122873176061388945 5237353592154882046041709)
    ·
      refine ⟨1964007597058080767265641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5237353592154882046041709 1964007597058080767265641)
      ·
        refine ⟨1473005697793560575449231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1964007597058080767265641 1473005697793560575449231)
        ·
          refine ⟨2209508546690340863173847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1473005697793560575449231 2209508546690340863173847)
          ·
            refine ⟨3314262820035511294760771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2209508546690340863173847 3314262820035511294760771)
            ·
              refine ⟨4971394230053266942141157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3314262820035511294760771 4971394230053266942141157)
              ·
                refine ⟨932136418134987551651467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4971394230053266942141157 932136418134987551651467)
                ·
                  refine ⟨1398204627202481327477201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932136418134987551651467 1398204627202481327477201)
                  ·
                    refine ⟨1048653470401860995607901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1398204627202481327477201 1048653470401860995607901)
                    ·
                      refine ⟨393245051400697873352963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1048653470401860995607901 393245051400697873352963)
                      ·
                        rfl

theorem cell23_765842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_765842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765842 prefixEnd_765842 := by exact prefixLift 765842
  have htrace : WordTrace (prefixWord ++ tailWord_765842) baseStart_765842 baseEnd_765842 := by
    simpa [prefixWord, tailWord_765842, baseEnd_765842] using wordTrace_append hprefix tailTrace_765842
  have hstable : (prefixWord ++ tailWord_765842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765842).length < 2 ^ (prefixWord ++ tailWord_765842).sum := by decide
  have hdescent : baseEnd_765842 < baseStart_765842 := by decide
  rcases family_descends (prefixWord ++ tailWord_765842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765861 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_765861 : Nat := 118140960795 + 765861 * 2 ^ 59
def prefixEnd_765861 : Nat := 4983230072969 + 3 ^ 40 * 765861 * 2
def baseEnd_765861 : Nat := 393254807533133299015375

theorem tailTrace_765861 : CollatzResearch.WordTrace tailWord_765861 prefixEnd_765861 393254807533133299015375 := by
  unfold tailWord_765861
  simp only [CollatzResearch.WordTrace]
  refine ⟨27933245478423870490497437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18622163652282580326998291 27933245478423870490497437)
  ·
    refine ⟨10474967054408951433936539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27933245478423870490497437 10474967054408951433936539)
    ·
      refine ⟨15712450581613427150904809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10474967054408951433936539 15712450581613427150904809)
      ·
        refine ⟨11784337936210070363178607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15712450581613427150904809 11784337936210070363178607)
        ·
          refine ⟨17676506904315105544767911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11784337936210070363178607 17676506904315105544767911)
          ·
            refine ⟨26514760356472658317151867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17676506904315105544767911 26514760356472658317151867)
            ·
              refine ⟨39772140534708987475727801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26514760356472658317151867 39772140534708987475727801)
              ·
                refine ⟨29829105401031740606795851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39772140534708987475727801 29829105401031740606795851)
                ·
                  refine ⟨44743658101547610910193777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29829105401031740606795851 44743658101547610910193777)
                  ·
                    refine ⟨33557743576160708182645333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44743658101547610910193777 33557743576160708182645333)
                    ·
                      refine ⟨393254807533133299015375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 33557743576160708182645333 393254807533133299015375)
                      ·
                        rfl

theorem cell23_765861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_765861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765861 prefixEnd_765861 := by exact prefixLift 765861
  have htrace : WordTrace (prefixWord ++ tailWord_765861) baseStart_765861 baseEnd_765861 := by
    simpa [prefixWord, tailWord_765861, baseEnd_765861] using wordTrace_append hprefix tailTrace_765861
  have hstable : (prefixWord ++ tailWord_765861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765861).length < 2 ^ (prefixWord ++ tailWord_765861).sum := by decide
  have hdescent : baseEnd_765861 < baseStart_765861 := by decide
  rcases family_descends (prefixWord ++ tailWord_765861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765895 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 1, 4, 2]
def baseStart_765895 : Nat := 118140960795 + 765895 * 2 ^ 59
def prefixEnd_765895 : Nat := 4983230072969 + 3 ^ 40 * 765895 * 2
def baseEnd_765895 : Nat := 393272265875386165990219

theorem tailTrace_765895 : CollatzResearch.WordTrace tailWord_765895 prefixEnd_765895 393272265875386165990219 := by
  unfold tailWord_765895
  simp only [CollatzResearch.WordTrace]
  refine ⟨27934485560300694297235139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18622990373533796198156759 27934485560300694297235139)
  ·
    refine ⟨41901728340451041445852709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27934485560300694297235139 41901728340451041445852709)
    ·
      refine ⟨7856574063834570271097383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41901728340451041445852709 7856574063834570271097383)
      ·
        refine ⟨11784861095751855406646075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7856574063834570271097383 11784861095751855406646075)
        ·
          refine ⟨17677291643627783109969113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11784861095751855406646075 17677291643627783109969113)
          ·
            refine ⟨13257968732720837332476835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17677291643627783109969113 13257968732720837332476835)
            ·
              refine ⟨19886953099081255998715253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13257968732720837332476835 19886953099081255998715253)
              ·
                refine ⟨1864401853038867749879555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19886953099081255998715253 1864401853038867749879555)
                ·
                  refine ⟨2796602779558301624819333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864401853038867749879555 2796602779558301624819333)
                  ·
                    refine ⟨524363021167181554653625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2796602779558301624819333 524363021167181554653625)
                    ·
                      refine ⟨393272265875386165990219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 524363021167181554653625 393272265875386165990219)
                      ·
                        rfl

theorem cell23_765895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_765895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765895 prefixEnd_765895 := by exact prefixLift 765895
  have htrace : WordTrace (prefixWord ++ tailWord_765895) baseStart_765895 baseEnd_765895 := by
    simpa [prefixWord, tailWord_765895, baseEnd_765895] using wordTrace_append hprefix tailTrace_765895
  have hstable : (prefixWord ++ tailWord_765895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765895).length < 2 ^ (prefixWord ++ tailWord_765895).sum := by decide
  have hdescent : baseEnd_765895 < baseStart_765895 := by decide
  rcases family_descends (prefixWord ++ tailWord_765895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765898 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_765898 : Nat := 118140960795 + 765898 * 2 ^ 59
def prefixEnd_765898 : Nat := 4983230072969 + 3 ^ 40 * 765898 * 2
def baseEnd_765898 : Nat := 393273806317349654252705

theorem tailTrace_765898 : CollatzResearch.WordTrace tailWord_765898 prefixEnd_765898 393273806317349654252705 := by
  unfold tailWord_765898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6983648744822456452398587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18623063319526550539729565 6983648744822456452398587)
  ·
    refine ⟨10475473117233684678597881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6983648744822456452398587 10475473117233684678597881)
    ·
      refine ⟨7856604837925263508948411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10475473117233684678597881 7856604837925263508948411)
      ·
        refine ⟨11784907256887895263422617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7856604837925263508948411 11784907256887895263422617)
        ·
          refine ⟨8838680442665921447566963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11784907256887895263422617 8838680442665921447566963)
          ·
            refine ⟨13258020663998882171350445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8838680442665921447566963 13258020663998882171350445)
            ·
              refine ⟨4971757748999580814256417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13258020663998882171350445 4971757748999580814256417)
              ·
                refine ⟨3728818311749685610692313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4971757748999580814256417 3728818311749685610692313)
                ·
                  refine ⟨2796613733812264208019235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3728818311749685610692313 2796613733812264208019235)
                  ·
                    refine ⟨4194920600718396312028853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2796613733812264208019235 4194920600718396312028853)
                    ·
                      refine ⟨393273806317349654252705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4194920600718396312028853 393273806317349654252705)
                      ·
                        rfl

theorem cell23_765898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_765898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765898 prefixEnd_765898 := by exact prefixLift 765898
  have htrace : WordTrace (prefixWord ++ tailWord_765898) baseStart_765898 baseEnd_765898 := by
    simpa [prefixWord, tailWord_765898, baseEnd_765898] using wordTrace_append hprefix tailTrace_765898
  have hstable : (prefixWord ++ tailWord_765898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765898).length < 2 ^ (prefixWord ++ tailWord_765898).sum := by decide
  have hdescent : baseEnd_765898 < baseStart_765898 := by decide
  rcases family_descends (prefixWord ++ tailWord_765898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765935 : List Nat := [1, 1, 2, 1, 4, 2, 3, 4, 5]
def baseStart_765935 : Nat := 118140960795 + 765935 * 2 ^ 59
def prefixEnd_765935 : Nat := 4983230072969 + 3 ^ 40 * 765935 * 2
def baseEnd_765935 : Nat := 43699200566840667721115

theorem tailTrace_765935 : CollatzResearch.WordTrace tailWord_765935 prefixEnd_765935 43699200566840667721115 := by
  unfold tailWord_765935
  simp only [CollatzResearch.WordTrace]
  refine ⟨27935944480155781128691259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18623962986770520752460839 27935944480155781128691259)
  ·
    refine ⟨41903916720233671693036889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27935944480155781128691259 41903916720233671693036889)
    ·
      refine ⟨31427937540175253769777667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41903916720233671693036889 31427937540175253769777667)
      ·
        refine ⟨47141906310262880654666501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31427937540175253769777667 47141906310262880654666501)
        ·
          refine ⟨8839107433174290122749969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47141906310262880654666501 8839107433174290122749969)
          ·
            refine ⟨6629330574880717592062477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8839107433174290122749969 6629330574880717592062477)
            ·
              refine ⟨2485998965580269097023429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6629330574880717592062477 2485998965580269097023429)
              ·
                refine ⟨466124806046300455691893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2485998965580269097023429 466124806046300455691893)
                ·
                  refine ⟨43699200566840667721115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 466124806046300455691893 43699200566840667721115)
                  ·
                    rfl

theorem cell23_765935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 5].length) (baseStart_765935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765935 prefixEnd_765935 := by exact prefixLift 765935
  have htrace : WordTrace (prefixWord ++ tailWord_765935) baseStart_765935 baseEnd_765935 := by
    simpa [prefixWord, tailWord_765935, baseEnd_765935] using wordTrace_append hprefix tailTrace_765935
  have hstable : (prefixWord ++ tailWord_765935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765935).length < 2 ^ (prefixWord ++ tailWord_765935).sum := by decide
  have hdescent : baseEnd_765935 < baseStart_765935 := by decide
  rcases family_descends (prefixWord ++ tailWord_765935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765942 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_765942 : Nat := 118140960795 + 765942 * 2 ^ 59
def prefixEnd_765942 : Nat := 4983230072969 + 3 ^ 40 * 765942 * 2
def baseEnd_765942 : Nat := 393296399466147482102503

theorem tailTrace_765942 : CollatzResearch.WordTrace tailWord_765942 prefixEnd_765942 393296399466147482102503 := by
  unfold tailWord_765942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1746012486945651332762255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18624133194086947549464053 1746012486945651332762255)
  ·
    refine ⟨2619018730418476999143383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1746012486945651332762255 2619018730418476999143383)
    ·
      refine ⟨3928528095627715498715075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2619018730418476999143383 3928528095627715498715075)
      ·
        refine ⟨5892792143441573248072613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3928528095627715498715075 5892792143441573248072613)
        ·
          refine ⟨1104898526895294984013615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5892792143441573248072613 1104898526895294984013615)
          ·
            refine ⟨1657347790342942476020423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104898526895294984013615 1657347790342942476020423)
            ·
              refine ⟨2486021685514413714030635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657347790342942476020423 2486021685514413714030635)
              ·
                refine ⟨3729032528271620571045953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486021685514413714030635 3729032528271620571045953)
                ·
                  refine ⟨2796774396203715428284465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3729032528271620571045953 2796774396203715428284465)
                  ·
                    refine ⟨2097580797152786571213349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2796774396203715428284465 2097580797152786571213349)
                    ·
                      refine ⟨393296399466147482102503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2097580797152786571213349 393296399466147482102503)
                      ·
                        rfl

theorem cell23_765942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_765942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765942 prefixEnd_765942 := by exact prefixLift 765942
  have htrace : WordTrace (prefixWord ++ tailWord_765942) baseStart_765942 baseEnd_765942 := by
    simpa [prefixWord, tailWord_765942, baseEnd_765942] using wordTrace_append hprefix tailTrace_765942
  have hstable : (prefixWord ++ tailWord_765942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765942).length < 2 ^ (prefixWord ++ tailWord_765942).sum := by decide
  have hdescent : baseEnd_765942 < baseStart_765942 := by decide
  rcases family_descends (prefixWord ++ tailWord_765942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765945 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 2, 3, 3]
def baseStart_765945 : Nat := 118140960795 + 765945 * 2 ^ 59
def prefixEnd_765945 : Nat := 4983230072969 + 3 ^ 40 * 765945 * 2
def baseEnd_765945 : Nat := 393297939908110970364989

theorem tailTrace_765945 : CollatzResearch.WordTrace tailWord_765945 prefixEnd_765945 393297939908110970364989 := by
  unfold tailWord_765945
  simp only [CollatzResearch.WordTrace]
  refine ⟨27936309210119552836555289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18624206140079701891036859 27936309210119552836555289)
  ·
    refine ⟨20952231907589664627416467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27936309210119552836555289 20952231907589664627416467)
    ·
      refine ⟨31428347861384496941124701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20952231907589664627416467 31428347861384496941124701)
      ·
        refine ⟨11785630448019186352921763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31428347861384496941124701 11785630448019186352921763)
        ·
          refine ⟨17678445672028779529382645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11785630448019186352921763 17678445672028779529382645)
          ·
            refine ⟨1657354281752698080879623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17678445672028779529382645 1657354281752698080879623)
            ·
              refine ⟨2486031422629047121319435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657354281752698080879623 2486031422629047121319435)
              ·
                refine ⟨3729047133943570681979153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486031422629047121319435 3729047133943570681979153)
                ·
                  refine ⟨2796785350457678011484365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3729047133943570681979153 2796785350457678011484365)
                  ·
                    refine ⟨1048794506421629254306637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2796785350457678011484365 1048794506421629254306637)
                    ·
                      refine ⟨393297939908110970364989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1048794506421629254306637 393297939908110970364989)
                      ·
                        rfl

theorem cell23_765945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_765945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765945 prefixEnd_765945 := by exact prefixLift 765945
  have htrace : WordTrace (prefixWord ++ tailWord_765945) baseStart_765945 baseEnd_765945 := by
    simpa [prefixWord, tailWord_765945, baseEnd_765945] using wordTrace_append hprefix tailTrace_765945
  have hstable : (prefixWord ++ tailWord_765945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765945).length < 2 ^ (prefixWord ++ tailWord_765945).sum := by decide
  have hdescent : baseEnd_765945 < baseStart_765945 := by decide
  rcases family_descends (prefixWord ++ tailWord_765945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765948 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 1, 7]
def baseStart_765948 : Nat := 118140960795 + 765948 * 2 ^ 59
def prefixEnd_765948 : Nat := 4983230072969 + 3 ^ 40 * 765948 * 2
def baseEnd_765948 : Nat := 131099826783358152875825

theorem tailTrace_765948 : CollatzResearch.WordTrace tailWord_765948 prefixEnd_765948 131099826783358152875825 := by
  unfold tailWord_765948
  simp only [CollatzResearch.WordTrace]
  refine ⟨13968209314554342174457249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18624279086072456232609665 13968209314554342174457249)
  ·
    refine ⟨10476156985915756630842937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13968209314554342174457249 10476156985915756630842937)
    ·
      refine ⟨7857117739436817473132203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10476156985915756630842937 7857117739436817473132203)
      ·
        refine ⟨11785676609155226209698305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7857117739436817473132203 11785676609155226209698305)
        ·
          refine ⟨8839257456866419657273729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11785676609155226209698305 8839257456866419657273729)
          ·
            refine ⟨6629443092649814742955297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8839257456866419657273729 6629443092649814742955297)
            ·
              refine ⟨4972082319487361057216473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6629443092649814742955297 4972082319487361057216473)
              ·
                refine ⟨3729061739615520792912355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4972082319487361057216473 3729061739615520792912355)
                ·
                  refine ⟨5593592609423281189368533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3729061739615520792912355 5593592609423281189368533)
                  ·
                    refine ⟨131099826783358152875825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5593592609423281189368533 131099826783358152875825)
                    ·
                      rfl

theorem cell23_765948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_765948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765948 prefixEnd_765948 := by exact prefixLift 765948
  have htrace : WordTrace (prefixWord ++ tailWord_765948) baseStart_765948 baseEnd_765948 := by
    simpa [prefixWord, tailWord_765948, baseEnd_765948] using wordTrace_append hprefix tailTrace_765948
  have hstable : (prefixWord ++ tailWord_765948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765948).length < 2 ^ (prefixWord ++ tailWord_765948).sum := by decide
  have hdescent : baseEnd_765948 < baseStart_765948 := by decide
  rcases family_descends (prefixWord ++ tailWord_765948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_765968 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 4]
def baseStart_765968 : Nat := 118140960795 + 765968 * 2 ^ 59
def prefixEnd_765968 : Nat := 4983230072969 + 3 ^ 40 * 765968 * 2
def baseEnd_765968 : Nat := 393309749963164380377383

theorem tailTrace_765968 : CollatzResearch.WordTrace tailWord_765968 prefixEnd_765968 393309749963164380377383 := by
  unfold tailWord_765968
  simp only [CollatzResearch.WordTrace]
  refine ⟨13968574044518113882321279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18624765392690818509761705 13968574044518113882321279)
  ·
    refine ⟨20952861066777170823481919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13968574044518113882321279 20952861066777170823481919)
    ·
      refine ⟨31429291600165756235222879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20952861066777170823481919 31429291600165756235222879)
      ·
        refine ⟨47143937400248634352834319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31429291600165756235222879 47143937400248634352834319)
        ·
          refine ⟨70715906100372951529251479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47143937400248634352834319 70715906100372951529251479)
          ·
            refine ⟨106073859150559427293877219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70715906100372951529251479 106073859150559427293877219)
            ·
              refine ⟨159110788725839140940815829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106073859150559427293877219 159110788725839140940815829)
              ·
                refine ⟨3729159110761854865800371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 159110788725839140940815829 3729159110761854865800371)
                ·
                  refine ⟨5593738666142782298700557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3729159110761854865800371 5593738666142782298700557)
                  ·
                    refine ⟨2097651999803543362012709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5593738666142782298700557 2097651999803543362012709)
                    ·
                      refine ⟨393309749963164380377383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2097651999803543362012709 393309749963164380377383)
                      ·
                        rfl

theorem cell23_765968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_765968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_765968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_765968 prefixEnd_765968 := by exact prefixLift 765968
  have htrace : WordTrace (prefixWord ++ tailWord_765968) baseStart_765968 baseEnd_765968 := by
    simpa [prefixWord, tailWord_765968, baseEnd_765968] using wordTrace_append hprefix tailTrace_765968
  have hstable : (prefixWord ++ tailWord_765968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_765968).length < 2 ^ (prefixWord ++ tailWord_765968).sum := by decide
  have hdescent : baseEnd_765968 < baseStart_765968 := by decide
  rcases family_descends (prefixWord ++ tailWord_765968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766002 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2]
def baseStart_766002 : Nat := 118140960795 + 766002 * 2 ^ 59
def prefixEnd_766002 : Nat := 4983230072969 + 3 ^ 40 * 766002 * 2
def baseEnd_766002 : Nat := 393327208305417247352227

theorem tailTrace_766002 : CollatzResearch.WordTrace tailWord_766002 prefixEnd_766002 393327208305417247352227 := by
  unfold tailWord_766002
  simp only [CollatzResearch.WordTrace]
  refine ⟨6984597042728262892845065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18625592113942034380920173 6984597042728262892845065)
  ·
    refine ⟨5238447782046197169633799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6984597042728262892845065 5238447782046197169633799)
    ·
      refine ⟨7857671673069295754450699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5238447782046197169633799 7857671673069295754450699)
      ·
        refine ⟨11786507509603943631676049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7857671673069295754450699 11786507509603943631676049)
        ·
          refine ⟨8839880632202957723757037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11786507509603943631676049 8839880632202957723757037)
          ·
            refine ⟨3314955237076109146408889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8839880632202957723757037 3314955237076109146408889)
            ·
              refine ⟨2486216427807081859806667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3314955237076109146408889 2486216427807081859806667)
              ·
                refine ⟨3729324641710622789710001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486216427807081859806667 3729324641710622789710001)
                ·
                  refine ⟨2796993481282967092282501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3729324641710622789710001 2796993481282967092282501)
                  ·
                    refine ⟨524436277740556329802969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2796993481282967092282501 524436277740556329802969)
                    ·
                      refine ⟨393327208305417247352227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 524436277740556329802969 393327208305417247352227)
                      ·
                        rfl

theorem cell23_766002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_766002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766002 prefixEnd_766002 := by exact prefixLift 766002
  have htrace : WordTrace (prefixWord ++ tailWord_766002) baseStart_766002 baseEnd_766002 := by
    simpa [prefixWord, tailWord_766002, baseEnd_766002] using wordTrace_append hprefix tailTrace_766002
  have hstable : (prefixWord ++ tailWord_766002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766002).length < 2 ^ (prefixWord ++ tailWord_766002).sum := by decide
  have hdescent : baseEnd_766002 < baseStart_766002 := by decide
  rcases family_descends (prefixWord ++ tailWord_766002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766005 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_766005 : Nat := 118140960795 + 766005 * 2 ^ 59
def prefixEnd_766005 : Nat := 4983230072969 + 3 ^ 40 * 766005 * 2
def baseEnd_766005 : Nat := 393328748747380735614713

theorem tailTrace_766005 : CollatzResearch.WordTrace tailWord_766005 prefixEnd_766005 393328748747380735614713 := by
  unfold tailWord_766005
  simp only [CollatzResearch.WordTrace]
  refine ⟨27938497589902183083739469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18625665059934788722492979 27938497589902183083739469)
  ·
    refine ⟨10476936596213318656402301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27938497589902183083739469 10476936596213318656402301)
    ·
      refine ⟨3928851223579994496150863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10476936596213318656402301 3928851223579994496150863)
      ·
        refine ⟨5893276835369991744226295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3928851223579994496150863 5893276835369991744226295)
        ·
          refine ⟨8839915253054987616339443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5893276835369991744226295 8839915253054987616339443)
          ·
            refine ⟨13259872879582481424509165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8839915253054987616339443 13259872879582481424509165)
            ·
              refine ⟨4972452329843430534190937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13259872879582481424509165 4972452329843430534190937)
              ·
                refine ⟨3729339247382572900643203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4972452329843430534190937 3729339247382572900643203)
                ·
                  refine ⟨5594008871073859350964805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3729339247382572900643203 5594008871073859350964805)
                  ·
                    refine ⟨1048876663326348628305901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5594008871073859350964805 1048876663326348628305901)
                    ·
                      refine ⟨393328748747380735614713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1048876663326348628305901 393328748747380735614713)
                      ·
                        rfl

theorem cell23_766005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_766005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766005 prefixEnd_766005 := by exact prefixLift 766005
  have htrace : WordTrace (prefixWord ++ tailWord_766005) baseStart_766005 baseEnd_766005 := by
    simpa [prefixWord, tailWord_766005, baseEnd_766005] using wordTrace_append hprefix tailTrace_766005
  have hstable : (prefixWord ++ tailWord_766005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766005).length < 2 ^ (prefixWord ++ tailWord_766005).sum := by decide
  have hdescent : baseEnd_766005 < baseStart_766005 := by decide
  rcases family_descends (prefixWord ++ tailWord_766005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766055 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 3, 5]
def baseStart_766055 : Nat := 118140960795 + 766055 * 2 ^ 59
def prefixEnd_766055 : Nat := 4983230072969 + 3 ^ 40 * 766055 * 2
def baseEnd_766055 : Nat := 131118140926701846663161

theorem tailTrace_766055 : CollatzResearch.WordTrace tailWord_766055 prefixEnd_766055 131118140926701846663161 := by
  unfold tailWord_766055
  simp only [CollatzResearch.WordTrace]
  refine ⟨27940321239721041623059619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18626880826480694415373079 27940321239721041623059619)
  ·
    refine ⟨41910481859581562434589429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27940321239721041623059619 41910481859581562434589429)
    ·
      refine ⟨3929107674335771478242759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41910481859581562434589429 3929107674335771478242759)
      ·
        refine ⟨5893661511503657217364139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929107674335771478242759 5893661511503657217364139)
        ·
          refine ⟨8840492267255485826046209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5893661511503657217364139 8840492267255485826046209)
          ·
            refine ⟨6630369200441614369534657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8840492267255485826046209 6630369200441614369534657)
            ·
              refine ⟨4972776900331210777150993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6630369200441614369534657 4972776900331210777150993)
              ·
                refine ⟨3729582675248408082863245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4972776900331210777150993 3729582675248408082863245)
                ·
                  refine ⟨1398593503218153031073717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3729582675248408082863245 1398593503218153031073717)
                  ·
                    refine ⟨131118140926701846663161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1398593503218153031073717 131118140926701846663161)
                    ·
                      rfl

theorem cell23_766055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_766055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766055 prefixEnd_766055 := by exact prefixLift 766055
  have htrace : WordTrace (prefixWord ++ tailWord_766055) baseStart_766055 baseEnd_766055 := by
    simpa [prefixWord, tailWord_766055, baseEnd_766055] using wordTrace_append hprefix tailTrace_766055
  have hstable : (prefixWord ++ tailWord_766055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766055).length < 2 ^ (prefixWord ++ tailWord_766055).sum := by decide
  have hdescent : baseEnd_766055 < baseStart_766055 := by decide
  rcases family_descends (prefixWord ++ tailWord_766055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766085 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 3, 6]
def baseStart_766085 : Nat := 118140960795 + 766085 * 2 ^ 59
def prefixEnd_766085 : Nat := 4983230072969 + 3 ^ 40 * 766085 * 2
def baseEnd_766085 : Nat := 131123275733246807538115

theorem tailTrace_766085 : CollatzResearch.WordTrace tailWord_766085 prefixEnd_766085 131123275733246807538115 := by
  unfold tailWord_766085
  simp only [CollatzResearch.WordTrace]
  refine ⟨27941415429612356746651709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18627610286408237831101139 27941415429612356746651709)
  ·
    refine ⟨10478030786104633779994391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27941415429612356746651709 10478030786104633779994391)
    ·
      refine ⟨15717046179156950669991587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10478030786104633779994391 15717046179156950669991587)
      ·
        refine ⟨23575569268735426004987381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15717046179156950669991587 23575569268735426004987381)
        ·
          refine ⟨2210209618943946187967567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23575569268735426004987381 2210209618943946187967567)
          ·
            refine ⟨3315314428415919281951351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210209618943946187967567 3315314428415919281951351)
            ·
              refine ⟨4972971642623878922927027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315314428415919281951351 4972971642623878922927027)
              ·
                refine ⟨7459457463935818384390541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4972971642623878922927027 7459457463935818384390541)
                ·
                  refine ⟨2797296548975931894146453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7459457463935818384390541 2797296548975931894146453)
                  ·
                    refine ⟨131123275733246807538115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2797296548975931894146453 131123275733246807538115)
                    ·
                      rfl

theorem cell23_766085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_766085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766085 prefixEnd_766085 := by exact prefixLift 766085
  have htrace : WordTrace (prefixWord ++ tailWord_766085) baseStart_766085 baseEnd_766085 := by
    simpa [prefixWord, tailWord_766085, baseEnd_766085] using wordTrace_append hprefix tailTrace_766085
  have hstable : (prefixWord ++ tailWord_766085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766085).length < 2 ^ (prefixWord ++ tailWord_766085).sum := by decide
  have hdescent : baseEnd_766085 < baseStart_766085 := by decide
  rcases family_descends (prefixWord ++ tailWord_766085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766112 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 3]
def baseStart_766112 : Nat := 118140960795 + 766112 * 2 ^ 59
def prefixEnd_766112 : Nat := 4983230072969 + 3 ^ 40 * 766112 * 2
def baseEnd_766112 : Nat := 393383691177411816976721

theorem tailTrace_766112 : CollatzResearch.WordTrace tailWord_766112 prefixEnd_766112 393383691177411816976721 := by
  unfold tailWord_766112
  simp only [CollatzResearch.WordTrace]
  refine ⟨13971200100257270178942295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18628266800343026905256393 13971200100257270178942295)
  ·
    refine ⟨20956800150385905268413443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13971200100257270178942295 20956800150385905268413443)
    ·
      refine ⟨31435200225578857902620165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20956800150385905268413443 31435200225578857902620165)
      ·
        refine ⟨5894100042296035856741281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31435200225578857902620165 5894100042296035856741281)
        ·
          refine ⟨4420575031722026892555961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5894100042296035856741281 4420575031722026892555961)
          ·
            refine ⟨3315431273791520169416971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4420575031722026892555961 3315431273791520169416971)
            ·
              refine ⟨4973146910687280254125457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315431273791520169416971 4973146910687280254125457)
              ·
                refine ⟨3729860183015460190594093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4973146910687280254125457 3729860183015460190594093)
                ·
                  refine ⟨1398697568630797571472785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3729860183015460190594093 1398697568630797571472785)
                  ·
                    refine ⟨1049023176473098178604589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1398697568630797571472785 1049023176473098178604589)
                    ·
                      refine ⟨393383691177411816976721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1049023176473098178604589 393383691177411816976721)
                      ·
                        rfl

theorem cell23_766112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_766112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766112 prefixEnd_766112 := by exact prefixLift 766112
  have htrace : WordTrace (prefixWord ++ tailWord_766112) baseStart_766112 baseEnd_766112 := by
    simpa [prefixWord, tailWord_766112, baseEnd_766112] using wordTrace_append hprefix tailTrace_766112
  have hstable : (prefixWord ++ tailWord_766112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766112).length < 2 ^ (prefixWord ++ tailWord_766112).sum := by decide
  have hdescent : baseEnd_766112 < baseStart_766112 := by decide
  rcases family_descends (prefixWord ++ tailWord_766112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766119 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 1, 6]
def baseStart_766119 : Nat := 118140960795 + 766119 * 2 ^ 59
def prefixEnd_766119 : Nat := 4983230072969 + 3 ^ 40 * 766119 * 2
def baseEnd_766119 : Nat := 131129095180664429863063

theorem tailTrace_766119 : CollatzResearch.WordTrace tailWord_766119 prefixEnd_766119 131129095180664429863063 := by
  unfold tailWord_766119
  simp only [CollatzResearch.WordTrace]
  refine ⟨27942655511489180553389411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18628437007659453702259607 27942655511489180553389411)
  ·
    refine ⟨41913983267233770830084117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27942655511489180553389411 41913983267233770830084117)
    ·
      refine ⟨1964717965651583007660193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41913983267233770830084117 1964717965651583007660193)
      ·
        refine ⟨1473538474238687255745145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1964717965651583007660193 1473538474238687255745145)
        ·
          refine ⟨1105153855679015441808859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1473538474238687255745145 1105153855679015441808859)
          ·
            refine ⟨1657730783518523162713289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105153855679015441808859 1657730783518523162713289)
            ·
              refine ⟨1243298087638892372034967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1657730783518523162713289 1243298087638892372034967)
              ·
                refine ⟨1864947131458338558052451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243298087638892372034967 1864947131458338558052451)
                ·
                  refine ⟨2797420697187507837078677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864947131458338558052451 2797420697187507837078677)
                  ·
                    refine ⟨131129095180664429863063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2797420697187507837078677 131129095180664429863063)
                    ·
                      rfl

theorem cell23_766119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_766119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766119 prefixEnd_766119 := by exact prefixLift 766119
  have htrace : WordTrace (prefixWord ++ tailWord_766119) baseStart_766119 baseEnd_766119 := by
    simpa [prefixWord, tailWord_766119, baseEnd_766119] using wordTrace_append hprefix tailTrace_766119
  have hstable : (prefixWord ++ tailWord_766119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766119).length < 2 ^ (prefixWord ++ tailWord_766119).sum := by decide
  have hdescent : baseEnd_766119 < baseStart_766119 := by decide
  rcases family_descends (prefixWord ++ tailWord_766119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766176 : List Nat := [2, 1, 1, 3, 1, 3, 5, 1, 2, 1, 3]
def baseStart_766176 : Nat := 118140960795 + 766176 * 2 ^ 59
def prefixEnd_766176 : Nat := 4983230072969 + 3 ^ 40 * 766176 * 2
def baseEnd_766176 : Nat := 393416553939299566576427

theorem tailTrace_766176 : CollatzResearch.WordTrace tailWord_766176 prefixEnd_766176 393416553939299566576427 := by
  unfold tailWord_766176
  simp only [CollatzResearch.WordTrace]
  refine ⟨13972367236141339644107191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18629822981521786192142921 13972367236141339644107191)
  ·
    refine ⟨20958550854212009466160787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13972367236141339644107191 20958550854212009466160787)
    ·
      refine ⟨31437826281318014199241181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20958550854212009466160787 31437826281318014199241181)
      ·
        refine ⟨11789184855494255324715443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31437826281318014199241181 11789184855494255324715443)
        ·
          refine ⟨17683777283241382987073165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11789184855494255324715443 17683777283241382987073165)
          ·
            refine ⟨6631416481215518620152437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17683777283241382987073165 6631416481215518620152437)
            ·
              refine ⟨621695295113954870639291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6631416481215518620152437 621695295113954870639291)
              ·
                refine ⟨932542942670932305958937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621695295113954870639291 932542942670932305958937)
                ·
                  refine ⟨699407207003199229469203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 932542942670932305958937 699407207003199229469203)
                  ·
                    refine ⟨1049110810504798844203805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 699407207003199229469203 1049110810504798844203805)
                    ·
                      refine ⟨393416553939299566576427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1049110810504798844203805 393416553939299566576427)
                      ·
                        rfl

theorem cell23_766176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_766176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766176 prefixEnd_766176 := by exact prefixLift 766176
  have htrace : WordTrace (prefixWord ++ tailWord_766176) baseStart_766176 baseEnd_766176 := by
    simpa [prefixWord, tailWord_766176, baseEnd_766176] using wordTrace_append hprefix tailTrace_766176
  have hstable : (prefixWord ++ tailWord_766176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766176).length < 2 ^ (prefixWord ++ tailWord_766176).sum := by decide
  have hdescent : baseEnd_766176 < baseStart_766176 := by decide
  rcases family_descends (prefixWord ++ tailWord_766176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766185 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 5]
def baseStart_766185 : Nat := 118140960795 + 766185 * 2 ^ 59
def prefixEnd_766185 : Nat := 4983230072969 + 3 ^ 40 * 766185 * 2
def baseEnd_766185 : Nat := 393421175265190031363885

theorem tailTrace_766185 : CollatzResearch.WordTrace tailWord_766185 prefixEnd_766185 393421175265190031363885 := by
  unfold tailWord_766185
  simp only [CollatzResearch.WordTrace]
  refine ⟨27945062729250073825292009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18630041819500049216861339 27945062729250073825292009)
  ·
    refine ⟨20958797046937555368969007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27945062729250073825292009 20958797046937555368969007)
    ·
      refine ⟨31438195570406333053453511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20958797046937555368969007 31438195570406333053453511)
      ·
        refine ⟨47157293355609499580180267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31438195570406333053453511 47157293355609499580180267)
        ·
          refine ⟨70735940033414249370270401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47157293355609499580180267 70735940033414249370270401)
          ·
            refine ⟨53051955025060687027702801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70735940033414249370270401 53051955025060687027702801)
            ·
              refine ⟨39788966268795515270777101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53051955025060687027702801 39788966268795515270777101)
              ·
                refine ⟨14920862350798318226541413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39788966268795515270777101 14920862350798318226541413)
                ·
                  refine ⟨2797661690774684667476515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14920862350798318226541413 2797661690774684667476515)
                  ·
                    refine ⟨4196492536162027001214773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2797661690774684667476515 4196492536162027001214773)
                    ·
                      refine ⟨393421175265190031363885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4196492536162027001214773 393421175265190031363885)
                      ·
                        rfl

theorem cell23_766185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_766185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766185 prefixEnd_766185 := by exact prefixLift 766185
  have htrace : WordTrace (prefixWord ++ tailWord_766185) baseStart_766185 baseEnd_766185 := by
    simpa [prefixWord, tailWord_766185, baseEnd_766185] using wordTrace_append hprefix tailTrace_766185
  have hstable : (prefixWord ++ tailWord_766185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766185).length < 2 ^ (prefixWord ++ tailWord_766185).sum := by decide
  have hdescent : baseEnd_766185 < baseStart_766185 := by decide
  rcases family_descends (prefixWord ++ tailWord_766185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766186 : List Nat := [3, 1, 3, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_766186 : Nat := 118140960795 + 766186 * 2 ^ 59
def prefixEnd_766186 : Nat := 4983230072969 + 3 ^ 40 * 766186 * 2
def baseEnd_766186 : Nat := 393421688745844527451381

theorem tailTrace_766186 : CollatzResearch.WordTrace tailWord_766186 prefixEnd_766186 393421688745844527451381 := by
  unfold tailWord_766186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6986274800561612749019603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18630066134830967330718941 6986274800561612749019603)
  ·
    refine ⟨10479412200842419123529405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6986274800561612749019603 10479412200842419123529405)
    ·
      refine ⟨3929779575315907171323527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10479412200842419123529405 3929779575315907171323527)
      ·
        refine ⟨5894669362973860756985291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929779575315907171323527 5894669362973860756985291)
        ·
          refine ⟨8842004044460791135477937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5894669362973860756985291 8842004044460791135477937)
          ·
            refine ⟨6631503033345593351608453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8842004044460791135477937 6631503033345593351608453)
            ·
              refine ⟨1243406818752298753426585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6631503033345593351608453 1243406818752298753426585)
              ·
                refine ⟨932555114064224065069939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1243406818752298753426585 932555114064224065069939)
                ·
                  refine ⟨1398832671096336097604909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932555114064224065069939 1398832671096336097604909)
                  ·
                    refine ⟨524562251661126036601841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398832671096336097604909 524562251661126036601841)
                    ·
                      refine ⟨393421688745844527451381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 524562251661126036601841 393421688745844527451381)
                      ·
                        rfl

theorem cell23_766186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_766186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766186 prefixEnd_766186 := by exact prefixLift 766186
  have htrace : WordTrace (prefixWord ++ tailWord_766186) baseStart_766186 baseEnd_766186 := by
    simpa [prefixWord, tailWord_766186, baseEnd_766186] using wordTrace_append hprefix tailTrace_766186
  have hstable : (prefixWord ++ tailWord_766186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766186).length < 2 ^ (prefixWord ++ tailWord_766186).sum := by decide
  have hdescent : baseEnd_766186 < baseStart_766186 := by decide
  rcases family_descends (prefixWord ++ tailWord_766186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766202 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_766202 : Nat := 118140960795 + 766202 * 2 ^ 59
def prefixEnd_766202 : Nat := 4983230072969 + 3 ^ 40 * 766202 * 2
def baseEnd_766202 : Nat := 393429904436316464851307

theorem tailTrace_766202 : CollatzResearch.WordTrace tailWord_766202 prefixEnd_766202 393429904436316464851307 := by
  unfold tailWord_766202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6986420692547121432165215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18630455180125657152440573 6986420692547121432165215)
  ·
    refine ⟨10479631038820682148247823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6986420692547121432165215 10479631038820682148247823)
    ·
      refine ⟨15719446558231023222371735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10479631038820682148247823 15719446558231023222371735)
      ·
        refine ⟨23579169837346534833557603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15719446558231023222371735 23579169837346534833557603)
        ·
          refine ⟨35368754756019802250336405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23579169837346534833557603 35368754756019802250336405)
          ·
            refine ⟨1657910379188428230484519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35368754756019802250336405 1657910379188428230484519)
            ·
              refine ⟨2486865568782642345726779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657910379188428230484519 2486865568782642345726779)
              ·
                refine ⟨3730298353173963518590169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486865568782642345726779 3730298353173963518590169)
                ·
                  refine ⟨2797723764880472638942627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3730298353173963518590169 2797723764880472638942627)
                  ·
                    refine ⟨4196585647320708958413941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2797723764880472638942627 4196585647320708958413941)
                    ·
                      refine ⟨393429904436316464851307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4196585647320708958413941 393429904436316464851307)
                      ·
                        rfl

theorem cell23_766202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_766202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766202 prefixEnd_766202 := by exact prefixLift 766202
  have htrace : WordTrace (prefixWord ++ tailWord_766202) baseStart_766202 baseEnd_766202 := by
    simpa [prefixWord, tailWord_766202, baseEnd_766202] using wordTrace_append hprefix tailTrace_766202
  have hstable : (prefixWord ++ tailWord_766202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766202).length < 2 ^ (prefixWord ++ tailWord_766202).sum := by decide
  have hdescent : baseEnd_766202 < baseStart_766202 := by decide
  rcases family_descends (prefixWord ++ tailWord_766202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766205 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 9]
def baseStart_766205 : Nat := 118140960795 + 766205 * 2 ^ 59
def prefixEnd_766205 : Nat := 4983230072969 + 3 ^ 40 * 766205 * 2
def baseEnd_766205 : Nat := 43714604986475550345977

theorem tailTrace_766205 : CollatzResearch.WordTrace tailWord_766205 prefixEnd_766205 43714604986475550345977 := by
  unfold tailWord_766205
  simp only [CollatzResearch.WordTrace]
  refine ⟨27945792189177617241020069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18630528126118411494013379 27945792189177617241020069)
  ·
    refine ⟨5239836035470803232691263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27945792189177617241020069 5239836035470803232691263)
    ·
      refine ⟨7859754053206204849036895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5239836035470803232691263 7859754053206204849036895)
      ·
        refine ⟨11789631079809307273555343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7859754053206204849036895 11789631079809307273555343)
        ·
          refine ⟨17684446619713960910333015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11789631079809307273555343 17684446619713960910333015)
          ·
            refine ⟨26526669929570941365499523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17684446619713960910333015 26526669929570941365499523)
            ·
              refine ⟨39790004894356412048249285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26526669929570941365499523 39790004894356412048249285)
              ·
                refine ⟨7460625917691827259046741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39790004894356412048249285 7460625917691827259046741)
                ·
                  refine ⟨43714604986475550345977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7460625917691827259046741 43714604986475550345977)
                  ·
                    rfl

theorem cell23_766205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_766205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766205 prefixEnd_766205 := by exact prefixLift 766205
  have htrace : WordTrace (prefixWord ++ tailWord_766205) baseStart_766205 baseEnd_766205 := by
    simpa [prefixWord, tailWord_766205, baseEnd_766205] using wordTrace_append hprefix tailTrace_766205
  have hstable : (prefixWord ++ tailWord_766205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766205).length < 2 ^ (prefixWord ++ tailWord_766205).sum := by decide
  have hdescent : baseEnd_766205 < baseStart_766205 := by decide
  rcases family_descends (prefixWord ++ tailWord_766205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766216 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 4, 2, 2]
def baseStart_766216 : Nat := 118140960795 + 766216 * 2 ^ 59
def prefixEnd_766216 : Nat := 4983230072969 + 3 ^ 40 * 766216 * 2
def baseEnd_766216 : Nat := 393437093165479410076243

theorem tailTrace_766216 : CollatzResearch.WordTrace tailWord_766216 prefixEnd_766216 393437093165479410076243 := by
  unfold tailWord_766216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13973096696068883059835251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18630795594758510746447001 13973096696068883059835251)
  ·
    refine ⟨20959645044103324589752877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13973096696068883059835251 20959645044103324589752877)
    ·
      refine ⟨7859866891538746721157329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20959645044103324589752877 7859866891538746721157329)
      ·
        refine ⟨5894900168654060040867997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7859866891538746721157329 5894900168654060040867997)
        ·
          refine ⟨2210587563245272515325499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5894900168654060040867997 2210587563245272515325499)
          ·
            refine ⟨3315881344867908772988249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210587563245272515325499 3315881344867908772988249)
            ·
              refine ⟨2486911008650931579741187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3315881344867908772988249 2486911008650931579741187)
              ·
                refine ⟨3730366512976397369611781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486911008650931579741187 3730366512976397369611781)
                ·
                  refine ⟨699443721183074506802209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3730366512976397369611781 699443721183074506802209)
                  ·
                    refine ⟨524582790887305880101657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 699443721183074506802209 524582790887305880101657)
                    ·
                      refine ⟨393437093165479410076243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 524582790887305880101657 393437093165479410076243)
                      ·
                        rfl

theorem cell23_766216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_766216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766216 prefixEnd_766216 := by exact prefixLift 766216
  have htrace : WordTrace (prefixWord ++ tailWord_766216) baseStart_766216 baseEnd_766216 := by
    simpa [prefixWord, tailWord_766216, baseEnd_766216] using wordTrace_append hprefix tailTrace_766216
  have hstable : (prefixWord ++ tailWord_766216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766216).length < 2 ^ (prefixWord ++ tailWord_766216).sum := by decide
  have hdescent : baseEnd_766216 < baseStart_766216 := by decide
  rcases family_descends (prefixWord ++ tailWord_766216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766232 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 1, 5, 3]
def baseStart_766232 : Nat := 118140960795 + 766232 * 2 ^ 59
def prefixEnd_766232 : Nat := 4983230072969 + 3 ^ 40 * 766232 * 2
def baseEnd_766232 : Nat := 393445308855951347476169

theorem tailTrace_766232 : CollatzResearch.WordTrace tailWord_766232 prefixEnd_766232 393445308855951347476169 := by
  unfold tailWord_766232
  simp only [CollatzResearch.WordTrace]
  refine ⟨13973388480039900426126475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18631184640053200568168633 13973388480039900426126475)
  ·
    refine ⟨20960082720059850639189713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13973388480039900426126475 20960082720059850639189713)
    ·
      refine ⟨15720062040044887979392285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20960082720059850639189713 15720062040044887979392285)
      ·
        refine ⟨5895023265016832992272107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15720062040044887979392285 5895023265016832992272107)
        ·
          refine ⟨8842534897525249488408161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5895023265016832992272107 8842534897525249488408161)
          ·
            refine ⟨6631901173143937116306121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8842534897525249488408161 6631901173143937116306121)
            ·
              refine ⟨4973925879857952837229591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6631901173143937116306121 4973925879857952837229591)
              ·
                refine ⟨7460888819786929255844387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4973925879857952837229591 7460888819786929255844387)
                ·
                  refine ⟨11191333229680393883766581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7460888819786929255844387 11191333229680393883766581)
                  ·
                    refine ⟨1049187490282536926603117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11191333229680393883766581 1049187490282536926603117)
                    ·
                      refine ⟨393445308855951347476169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1049187490282536926603117 393445308855951347476169)
                      ·
                        rfl

theorem cell23_766232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_766232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766232 prefixEnd_766232 := by exact prefixLift 766232
  have htrace : WordTrace (prefixWord ++ tailWord_766232) baseStart_766232 baseEnd_766232 := by
    simpa [prefixWord, tailWord_766232, baseEnd_766232] using wordTrace_append hprefix tailTrace_766232
  have hstable : (prefixWord ++ tailWord_766232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766232).length < 2 ^ (prefixWord ++ tailWord_766232).sum := by decide
  have hdescent : baseEnd_766232 < baseStart_766232 := by decide
  rcases family_descends (prefixWord ++ tailWord_766232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766235 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 3, 7]
def baseStart_766235 : Nat := 118140960795 + 766235 * 2 ^ 59
def prefixEnd_766235 : Nat := 4983230072969 + 3 ^ 40 * 766235 * 2
def baseEnd_766235 : Nat := 131148949765971611912885

theorem tailTrace_766235 : CollatzResearch.WordTrace tailWord_766235 prefixEnd_766235 131148949765971611912885 := by
  unfold tailWord_766235
  simp only [CollatzResearch.WordTrace]
  refine ⟨27946886379068932364612159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18631257586045954909741439 27946886379068932364612159)
  ·
    refine ⟨41920329568603398546918239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27946886379068932364612159 41920329568603398546918239)
    ·
      refine ⟨62880494352905097820377359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41920329568603398546918239 62880494352905097820377359)
      ·
        refine ⟨94320741529357646730566039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62880494352905097820377359 94320741529357646730566039)
        ·
          refine ⟨141481112294036470095849059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94320741529357646730566039 141481112294036470095849059)
          ·
            refine ⟨212221668441054705143773589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141481112294036470095849059 212221668441054705143773589)
            ·
              refine ⟨9947890708174439303614387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212221668441054705143773589 9947890708174439303614387)
              ·
                refine ⟨14921836062261658955421581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9947890708174439303614387 14921836062261658955421581)
                ·
                  refine ⟨5595688523348122108283093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14921836062261658955421581 5595688523348122108283093)
                  ·
                    refine ⟨131148949765971611912885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5595688523348122108283093 131148949765971611912885)
                    ·
                      rfl

theorem cell23_766235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 7].length) (baseStart_766235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766235 prefixEnd_766235 := by exact prefixLift 766235
  have htrace : WordTrace (prefixWord ++ tailWord_766235) baseStart_766235 baseEnd_766235 := by
    simpa [prefixWord, tailWord_766235, baseEnd_766235] using wordTrace_append hprefix tailTrace_766235
  have hstable : (prefixWord ++ tailWord_766235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766235).length < 2 ^ (prefixWord ++ tailWord_766235).sum := by decide
  have hdescent : baseEnd_766235 < baseStart_766235 := by decide
  rcases family_descends (prefixWord ++ tailWord_766235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766252 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 2, 5]
def baseStart_766252 : Nat := 118140960795 + 766252 * 2 ^ 59
def prefixEnd_766252 : Nat := 4983230072969 + 3 ^ 40 * 766252 * 2
def baseEnd_766252 : Nat := 131151859489680423075359

theorem tailTrace_766252 : CollatzResearch.WordTrace tailWord_766252 prefixEnd_766252 131151859489680423075359 := by
  unfold tailWord_766252
  simp only [CollatzResearch.WordTrace]
  refine ⟨13973753210003672133990505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18631670946671562845320673 13973753210003672133990505)
  ·
    refine ⟨10480314907502754100492879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13973753210003672133990505 10480314907502754100492879)
    ·
      refine ⟨15720472361254131150739319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10480314907502754100492879 15720472361254131150739319)
      ·
        refine ⟨23580708541881196726108979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15720472361254131150739319 23580708541881196726108979)
        ·
          refine ⟨35371062812821795089163469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23580708541881196726108979 35371062812821795089163469)
          ·
            refine ⟨13264148554808173158436301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35371062812821795089163469 13264148554808173158436301)
            ·
              refine ⟨4974055708053064934413613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13264148554808173158436301 4974055708053064934413613)
              ·
                refine ⟨1865270890519899350405105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4974055708053064934413613 1865270890519899350405105)
                ·
                  refine ⟨1398953167889924512803829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1865270890519899350405105 1398953167889924512803829)
                  ·
                    refine ⟨131151859489680423075359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1398953167889924512803829 131151859489680423075359)
                    ·
                      rfl

theorem cell23_766252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_766252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766252 prefixEnd_766252 := by exact prefixLift 766252
  have htrace : WordTrace (prefixWord ++ tailWord_766252) baseStart_766252 baseEnd_766252 := by
    simpa [prefixWord, tailWord_766252, baseEnd_766252] using wordTrace_append hprefix tailTrace_766252
  have hstable : (prefixWord ++ tailWord_766252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766252).length < 2 ^ (prefixWord ++ tailWord_766252).sum := by decide
  have hdescent : baseEnd_766252 < baseStart_766252 := by decide
  rcases family_descends (prefixWord ++ tailWord_766252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766272 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 4]
def baseStart_766272 : Nat := 118140960795 + 766272 * 2 ^ 59
def prefixEnd_766272 : Nat := 4983230072969 + 3 ^ 40 * 766272 * 2
def baseEnd_766272 : Nat := 393465848082131190975985

theorem tailTrace_766272 : CollatzResearch.WordTrace tailWord_766272 prefixEnd_766272 393465848082131190975985 := by
  unfold tailWord_766272
  simp only [CollatzResearch.WordTrace]
  refine ⟨13974117939967443841854535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18632157253289925122472713 13974117939967443841854535)
  ·
    refine ⟨20961176909951165762781803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13974117939967443841854535 20961176909951165762781803)
    ·
      refine ⟨31441765364926748644172705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20961176909951165762781803 31441765364926748644172705)
      ·
        refine ⟨23581324023695061483129529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31441765364926748644172705 23581324023695061483129529)
        ·
          refine ⟨17685993017771296112347147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23581324023695061483129529 17685993017771296112347147)
          ·
            refine ⟨26528989526656944168520721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17685993017771296112347147 26528989526656944168520721)
            ·
              refine ⟨19896742144992708126390541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26528989526656944168520721 19896742144992708126390541)
              ·
                refine ⟨7461278304372265547396453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19896742144992708126390541 7461278304372265547396453)
                ·
                  refine ⟨1398989682069799790136835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7461278304372265547396453 1398989682069799790136835)
                  ·
                    refine ⟨2098484523104699685205253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1398989682069799790136835 2098484523104699685205253)
                    ·
                      refine ⟨393465848082131190975985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2098484523104699685205253 393465848082131190975985)
                      ·
                        rfl

theorem cell23_766272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_766272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766272 prefixEnd_766272 := by exact prefixLift 766272
  have htrace : WordTrace (prefixWord ++ tailWord_766272) baseStart_766272 baseEnd_766272 := by
    simpa [prefixWord, tailWord_766272, baseEnd_766272] using wordTrace_append hprefix tailTrace_766272
  have hstable : (prefixWord ++ tailWord_766272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766272).length < 2 ^ (prefixWord ++ tailWord_766272).sum := by decide
  have hdescent : baseEnd_766272 < baseStart_766272 := by decide
  rcases family_descends (prefixWord ++ tailWord_766272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766289 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 1, 6, 2]
def baseStart_766289 : Nat := 118140960795 + 766289 * 2 ^ 59
def prefixEnd_766289 : Nat := 4983230072969 + 3 ^ 40 * 766289 * 2
def baseEnd_766289 : Nat := 393474577253257624463407

theorem tailTrace_766289 : CollatzResearch.WordTrace tailWord_766289 prefixEnd_766289 393474577253257624463407 := by
  unfold tailWord_766289
  simp only [CollatzResearch.WordTrace]
  refine ⟨27948855920873299587077921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18632570613915533058051947 27948855920873299587077921)
  ·
    refine ⟨20961641940654974690308441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27948855920873299587077921 20961641940654974690308441)
    ·
      refine ⟨15721231455491231017731331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20961641940654974690308441 15721231455491231017731331)
      ·
        refine ⟨23581847183236846526596997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15721231455491231017731331 23581847183236846526596997)
        ·
          refine ⟨4421596346856908723736937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23581847183236846526596997 4421596346856908723736937)
          ·
            refine ⟨3316197260142681542802703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4421596346856908723736937 3316197260142681542802703)
            ·
              refine ⟨4974295890214022314204055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316197260142681542802703 4974295890214022314204055)
              ·
                refine ⟨7461443835321033471306083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4974295890214022314204055 7461443835321033471306083)
                ·
                  refine ⟨11192165752981550206959125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7461443835321033471306083 11192165752981550206959125)
                  ·
                    refine ⟨524632769671010165951209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11192165752981550206959125 524632769671010165951209)
                    ·
                      refine ⟨393474577253257624463407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 524632769671010165951209 393474577253257624463407)
                      ·
                        rfl

theorem cell23_766289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 6, 2].length) (baseStart_766289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766289 prefixEnd_766289 := by exact prefixLift 766289
  have htrace : WordTrace (prefixWord ++ tailWord_766289) baseStart_766289 baseEnd_766289 := by
    simpa [prefixWord, tailWord_766289, baseEnd_766289] using wordTrace_append hprefix tailTrace_766289
  have hstable : (prefixWord ++ tailWord_766289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766289).length < 2 ^ (prefixWord ++ tailWord_766289).sum := by decide
  have hdescent : baseEnd_766289 < baseStart_766289 := by decide
  rcases family_descends (prefixWord ++ tailWord_766289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766306 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_766306 : Nat := 118140960795 + 766306 * 2 ^ 59
def prefixEnd_766306 : Nat := 4983230072969 + 3 ^ 40 * 766306 * 2
def baseEnd_766306 : Nat := 393483306424384057950829

theorem tailTrace_766306 : CollatzResearch.WordTrace tailWord_766306 prefixEnd_766306 393483306424384057950829 := by
  unfold tailWord_766306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6987368990452927872611693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18632983974541140993631181 6987368990452927872611693)
  ·
    refine ⟨2620263371419847952229385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6987368990452927872611693 2620263371419847952229385)
    ·
      refine ⟨1965197528564885964172039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2620263371419847952229385 1965197528564885964172039)
      ·
        refine ⟨2947796292847328946258059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1965197528564885964172039 2947796292847328946258059)
        ·
          refine ⟨4421694439270993419387089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2947796292847328946258059 4421694439270993419387089)
          ·
            refine ⟨3316270829453245064540317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4421694439270993419387089 3316270829453245064540317)
            ·
              refine ⟨1243601561044966899202619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3316270829453245064540317 1243601561044966899202619)
              ·
                refine ⟨1865402341567450348803929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243601561044966899202619 1865402341567450348803929)
                ·
                  refine ⟨1399051756175587761602947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1865402341567450348803929 1399051756175587761602947)
                  ·
                    refine ⟨2098577634263381642404421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1399051756175587761602947 2098577634263381642404421)
                    ·
                      refine ⟨393483306424384057950829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2098577634263381642404421 393483306424384057950829)
                      ·
                        rfl

theorem cell23_766306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_766306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766306 prefixEnd_766306 := by exact prefixLift 766306
  have htrace : WordTrace (prefixWord ++ tailWord_766306) baseStart_766306 baseEnd_766306 := by
    simpa [prefixWord, tailWord_766306, baseEnd_766306] using wordTrace_append hprefix tailTrace_766306
  have hstable : (prefixWord ++ tailWord_766306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766306).length < 2 ^ (prefixWord ++ tailWord_766306).sum := by decide
  have hdescent : baseEnd_766306 < baseStart_766306 := by decide
  rcases family_descends (prefixWord ++ tailWord_766306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766309 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 1, 4, 3]
def baseStart_766309 : Nat := 118140960795 + 766309 * 2 ^ 59
def prefixEnd_766309 : Nat := 4983230072969 + 3 ^ 40 * 766309 * 2
def baseEnd_766309 : Nat := 393484846866347546213315

theorem tailTrace_766309 : CollatzResearch.WordTrace tailWord_766309 prefixEnd_766309 393484846866347546213315 := by
  unfold tailWord_766309
  simp only [CollatzResearch.WordTrace]
  refine ⟨27949585380800843002805981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18633056920533895335203987 27949585380800843002805981)
  ·
    refine ⟨10481094517800316126052243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27949585380800843002805981 10481094517800316126052243)
    ·
      refine ⟨15721641776700474189078365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10481094517800316126052243 15721641776700474189078365)
      ·
        refine ⟨5895615666262677820904387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15721641776700474189078365 5895615666262677820904387)
        ·
          refine ⟨8843423499394016731356581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5895615666262677820904387 8843423499394016731356581)
          ·
            refine ⟨1658141906136378137129359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8843423499394016731356581 1658141906136378137129359)
            ·
              refine ⟨2487212859204567205694039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658141906136378137129359 2487212859204567205694039)
              ·
                refine ⟨3730819288806850808541059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2487212859204567205694039 3730819288806850808541059)
                ·
                  refine ⟨5596228933210276212811589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3730819288806850808541059 5596228933210276212811589)
                  ·
                    refine ⟨1049292924976926789902173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5596228933210276212811589 1049292924976926789902173)
                    ·
                      refine ⟨393484846866347546213315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1049292924976926789902173 393484846866347546213315)
                      ·
                        rfl

theorem cell23_766309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_766309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766309 prefixEnd_766309 := by exact prefixLift 766309
  have htrace : WordTrace (prefixWord ++ tailWord_766309) baseStart_766309 baseEnd_766309 := by
    simpa [prefixWord, tailWord_766309, baseEnd_766309] using wordTrace_append hprefix tailTrace_766309
  have hstable : (prefixWord ++ tailWord_766309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766309).length < 2 ^ (prefixWord ++ tailWord_766309).sum := by decide
  have hdescent : baseEnd_766309 < baseStart_766309 := by decide
  rcases family_descends (prefixWord ++ tailWord_766309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766359 : List Nat := [1, 1, 3, 3, 1, 1, 3, 4, 1, 5]
def baseStart_766359 : Nat := 118140960795 + 766359 * 2 ^ 59
def prefixEnd_766359 : Nat := 4983230072969 + 3 ^ 40 * 766359 * 2
def baseEnd_766359 : Nat := 131170173633024116862695

theorem tailTrace_766359 : CollatzResearch.WordTrace tailWord_766359 prefixEnd_766359 131170173633024116862695 := by
  unfold tailWord_766359
  simp only [CollatzResearch.WordTrace]
  refine ⟨27951409030619701542126131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18634272687079801028084087 27951409030619701542126131)
  ·
    refine ⟨41927113545929552313189197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27951409030619701542126131 41927113545929552313189197)
    ·
      refine ⟨15722667579723582117445949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41927113545929552313189197 15722667579723582117445949)
      ·
        refine ⟨5896000342396343294042231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15722667579723582117445949 5896000342396343294042231)
        ·
          refine ⟨8844000513594514941063347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5896000342396343294042231 8844000513594514941063347)
          ·
            refine ⟨13266000770391772411595021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8844000513594514941063347 13266000770391772411595021)
            ·
              refine ⟨4974750288896914654348133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13266000770391772411595021 4974750288896914654348133)
              ·
                refine ⟨932765679168171497690275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4974750288896914654348133 932765679168171497690275)
                ·
                  refine ⟨1399148518752257246535413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932765679168171497690275 1399148518752257246535413)
                  ·
                    refine ⟨131170173633024116862695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1399148518752257246535413 131170173633024116862695)
                    ·
                      rfl

theorem cell23_766359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_766359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766359 prefixEnd_766359 := by exact prefixLift 766359
  have htrace : WordTrace (prefixWord ++ tailWord_766359) baseStart_766359 baseEnd_766359 := by
    simpa [prefixWord, tailWord_766359, baseEnd_766359] using wordTrace_append hprefix tailTrace_766359
  have hstable : (prefixWord ++ tailWord_766359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766359).length < 2 ^ (prefixWord ++ tailWord_766359).sum := by decide
  have hdescent : baseEnd_766359 < baseStart_766359 := by decide
  rcases family_descends (prefixWord ++ tailWord_766359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766433 : List Nat := [1, 2, 3, 1, 2, 2, 5, 1, 1, 2, 3]
def baseStart_766433 : Nat := 118140960795 + 766433 * 2 ^ 59
def prefixEnd_766433 : Nat := 4983230072969 + 3 ^ 40 * 766433 * 2
def baseEnd_766433 : Nat := 393548518467505061062745

theorem tailTrace_766433 : CollatzResearch.WordTrace tailWord_766433 prefixEnd_766433 393548518467505061062745 := by
  unfold tailWord_766433
  simp only [CollatzResearch.WordTrace]
  refine ⟨27954108032351612180319953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18636072021567741453546635 27954108032351612180319953)
  ·
    refine ⟨20965581024263709135239965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27954108032351612180319953 20965581024263709135239965)
    ·
      refine ⟨7862092884098890925714987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20965581024263709135239965 7862092884098890925714987)
      ·
        refine ⟨11793139326148336388572481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7862092884098890925714987 11793139326148336388572481)
        ·
          refine ⟨8844854494611252291429361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11793139326148336388572481 8844854494611252291429361)
          ·
            refine ⟨6633640870958439218572021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8844854494611252291429361 6633640870958439218572021)
            ·
              refine ⟨621903831652353676741127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6633640870958439218572021 621903831652353676741127)
              ·
                refine ⟨932855747478530515111691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621903831652353676741127 932855747478530515111691)
                ·
                  refine ⟨1399283621217795772667537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932855747478530515111691 1399283621217795772667537)
                  ·
                    refine ⟨1049462715913346829500653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1399283621217795772667537 1049462715913346829500653)
                    ·
                      refine ⟨393548518467505061062745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1049462715913346829500653 393548518467505061062745)
                      ·
                        rfl

theorem cell23_766433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_766433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766433 prefixEnd_766433 := by exact prefixLift 766433
  have htrace : WordTrace (prefixWord ++ tailWord_766433) baseStart_766433 baseEnd_766433 := by
    simpa [prefixWord, tailWord_766433, baseEnd_766433] using wordTrace_append hprefix tailTrace_766433
  have hstable : (prefixWord ++ tailWord_766433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766433).length < 2 ^ (prefixWord ++ tailWord_766433).sum := by decide
  have hdescent : baseEnd_766433 < baseStart_766433 := by decide
  rcases family_descends (prefixWord ++ tailWord_766433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766453 : List Nat := [1, 3, 5, 1, 2, 2, 1, 8]
def baseStart_766453 : Nat := 118140960795 + 766453 * 2 ^ 59
def prefixEnd_766453 : Nat := 4983230072969 + 3 ^ 40 * 766453 * 2
def baseEnd_766453 : Nat := 14576251410392406770839

theorem tailTrace_766453 : CollatzResearch.WordTrace tailWord_766453 prefixEnd_766453 14576251410392406770839 := by
  unfold tailWord_766453
  simp only [CollatzResearch.WordTrace]
  refine ⟨27954837492279155596048013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18636558328186103730698675 27954837492279155596048013)
  ·
    refine ⟨10483064059604683348518005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27954837492279155596048013 10483064059604683348518005)
    ·
      refine ⟨982787255587939063923563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10483064059604683348518005 982787255587939063923563)
      ·
        refine ⟨1474180883381908595885345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982787255587939063923563 1474180883381908595885345)
        ·
          refine ⟨1105635662536431446914009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1474180883381908595885345 1105635662536431446914009)
          ·
            refine ⟨829226746902323585185507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1105635662536431446914009 829226746902323585185507)
            ·
              refine ⟨1243840120353485377778261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829226746902323585185507 1243840120353485377778261)
              ·
                refine ⟨14576251410392406770839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1243840120353485377778261 14576251410392406770839)
                ·
                  rfl

theorem cell23_766453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 8].length) (baseStart_766453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766453 prefixEnd_766453 := by exact prefixLift 766453
  have htrace : WordTrace (prefixWord ++ tailWord_766453) baseStart_766453 baseEnd_766453 := by
    simpa [prefixWord, tailWord_766453, baseEnd_766453] using wordTrace_append hprefix tailTrace_766453
  have hstable : (prefixWord ++ tailWord_766453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766453).length < 2 ^ (prefixWord ++ tailWord_766453).sum := by decide
  have hdescent : baseEnd_766453 < baseStart_766453 := by decide
  rcases family_descends (prefixWord ++ tailWord_766453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766456 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 5, 3, 2]
def baseStart_766456 : Nat := 118140960795 + 766456 * 2 ^ 59
def prefixEnd_766456 : Nat := 4983230072969 + 3 ^ 40 * 766456 * 2
def baseEnd_766456 : Nat := 393560328522558471075139

theorem tailTrace_766456 : CollatzResearch.WordTrace tailWord_766456 prefixEnd_766456 393560328522558471075139 := by
  unfold tailWord_766456
  simp only [CollatzResearch.WordTrace]
  refine ⟨13977473455634143554203611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18636631274178858072271481 13977473455634143554203611)
  ·
    refine ⟨20966210183451215331305417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13977473455634143554203611 20966210183451215331305417)
    ·
      refine ⟨15724657637588411498479063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20966210183451215331305417 15724657637588411498479063)
      ·
        refine ⟨23586986456382617247718595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15724657637588411498479063 23586986456382617247718595)
        ·
          refine ⟨35380479684573925871577893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23586986456382617247718595 35380479684573925871577893)
          ·
            refine ⟨6633839940857611100920855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35380479684573925871577893 6633839940857611100920855)
            ·
              refine ⟨9950759911286416651381283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6633839940857611100920855 9950759911286416651381283)
              ·
                refine ⟨14926139866929624977071925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9950759911286416651381283 14926139866929624977071925)
                ·
                  refine ⟨1399325612524652341600493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14926139866929624977071925 1399325612524652341600493)
                  ·
                    refine ⟨524747104696744628100185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1399325612524652341600493 524747104696744628100185)
                    ·
                      refine ⟨393560328522558471075139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 524747104696744628100185 393560328522558471075139)
                      ·
                        rfl

theorem cell23_766456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5, 3, 2].length) (baseStart_766456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766456 prefixEnd_766456 := by exact prefixLift 766456
  have htrace : WordTrace (prefixWord ++ tailWord_766456) baseStart_766456 baseEnd_766456 := by
    simpa [prefixWord, tailWord_766456, baseEnd_766456] using wordTrace_append hprefix tailTrace_766456
  have hstable : (prefixWord ++ tailWord_766456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766456).length < 2 ^ (prefixWord ++ tailWord_766456).sum := by decide
  have hdescent : baseEnd_766456 < baseStart_766456 := by decide
  rcases family_descends (prefixWord ++ tailWord_766456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766489 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 4, 4, 3]
def baseStart_766489 : Nat := 118140960795 + 766489 * 2 ^ 59
def prefixEnd_766489 : Nat := 4983230072969 + 3 ^ 40 * 766489 * 2
def baseEnd_766489 : Nat := 393577273384156841962487

theorem tailTrace_766489 : CollatzResearch.WordTrace tailWord_766489 prefixEnd_766489 393577273384156841962487 := by
  unfold tailWord_766489
  simp only [CollatzResearch.WordTrace]
  refine ⟨27956150520148733744358521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18637433680099155829572347 27956150520148733744358521)
  ·
    refine ⟨20967112890111550308268891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27956150520148733744358521 20967112890111550308268891)
    ·
      refine ⟨31450669335167325462403337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20967112890111550308268891 31450669335167325462403337)
      ·
        refine ⟨23588002001375494096802503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31450669335167325462403337 23588002001375494096802503)
        ·
          refine ⟨35382003002063241145203755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23588002001375494096802503 35382003002063241145203755)
          ·
            refine ⟨53073004503094861717805633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35382003002063241145203755 53073004503094861717805633)
            ·
              refine ⟨39804753377321146288354225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53073004503094861717805633 39804753377321146288354225)
              ·
                refine ⟨29853565032990859716265669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39804753377321146288354225 29853565032990859716265669)
                ·
                  refine ⟨5597543443685786196799813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29853565032990859716265669 5597543443685786196799813)
                  ·
                    refine ⟨1049539395691084911899965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5597543443685786196799813 1049539395691084911899965)
                    ·
                      refine ⟨393577273384156841962487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1049539395691084911899965 393577273384156841962487)
                      ·
                        rfl

theorem cell23_766489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_766489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766489 prefixEnd_766489 := by exact prefixLift 766489
  have htrace : WordTrace (prefixWord ++ tailWord_766489) baseStart_766489 baseEnd_766489 := by
    simpa [prefixWord, tailWord_766489, baseEnd_766489] using wordTrace_append hprefix tailTrace_766489
  have hstable : (prefixWord ++ tailWord_766489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766489).length < 2 ^ (prefixWord ++ tailWord_766489).sum := by decide
  have hdescent : baseEnd_766489 < baseStart_766489 := by decide
  rcases family_descends (prefixWord ++ tailWord_766489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766490 : List Nat := [3, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2]
def baseStart_766490 : Nat := 118140960795 + 766490 * 2 ^ 59
def prefixEnd_766490 : Nat := 4983230072969 + 3 ^ 40 * 766490 * 2
def baseEnd_766490 : Nat := 393577786864811338049983

theorem tailTrace_766490 : CollatzResearch.WordTrace tailWord_766490 prefixEnd_766490 393577786864811338049983 := by
  unfold tailWord_766490
  simp only [CollatzResearch.WordTrace]
  refine ⟨6989046748286277728786231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18637457995430073943429949 6989046748286277728786231)
  ·
    refine ⟨10483570122429416593179347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6989046748286277728786231 10483570122429416593179347)
    ·
      refine ⟨15725355183644124889769021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10483570122429416593179347 15725355183644124889769021)
      ·
        refine ⟨5897008193866546833663383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15725355183644124889769021 5897008193866546833663383)
        ·
          refine ⟨8845512290799820250495075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5897008193866546833663383 8845512290799820250495075)
          ·
            refine ⟨13268268436199730375742613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8845512290799820250495075 13268268436199730375742613)
            ·
              refine ⟨621950082946862361362935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13268268436199730375742613 621950082946862361362935)
              ·
                refine ⟨932925124420293542044403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621950082946862361362935 932925124420293542044403)
                ·
                  refine ⟨1399387686630440313066605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932925124420293542044403 1399387686630440313066605)
                  ·
                    refine ⟨524770382486415117399977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1399387686630440313066605 524770382486415117399977)
                    ·
                      refine ⟨393577786864811338049983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 524770382486415117399977 393577786864811338049983)
                      ·
                        rfl

theorem cell23_766490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_766490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766490 prefixEnd_766490 := by exact prefixLift 766490
  have htrace : WordTrace (prefixWord ++ tailWord_766490) baseStart_766490 baseEnd_766490 := by
    simpa [prefixWord, tailWord_766490, baseEnd_766490] using wordTrace_append hprefix tailTrace_766490
  have hstable : (prefixWord ++ tailWord_766490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766490).length < 2 ^ (prefixWord ++ tailWord_766490).sum := by decide
  have hdescent : baseEnd_766490 < baseStart_766490 := by decide
  rcases family_descends (prefixWord ++ tailWord_766490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766539 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 1, 7]
def baseStart_766539 : Nat := 118140960795 + 766539 * 2 ^ 59
def prefixEnd_766539 : Nat := 4983230072969 + 3 ^ 40 * 766539 * 2
def baseEnd_766539 : Nat := 131200982472293882112419

theorem tailTrace_766539 : CollatzResearch.WordTrace tailWord_766539 prefixEnd_766539 131200982472293882112419 := by
  unfold tailWord_766539
  simp only [CollatzResearch.WordTrace]
  refine ⟨27957974169967592283678671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18638649446645061522452447 27957974169967592283678671)
  ·
    refine ⟨41936961254951388425518007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27957974169967592283678671 41936961254951388425518007)
    ·
      refine ⟨62905441882427082638277011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41936961254951388425518007 62905441882427082638277011)
      ·
        refine ⟨94358162823640623957415517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62905441882427082638277011 94358162823640623957415517)
        ·
          refine ⟨35384311058865233984030819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94358162823640623957415517 35384311058865233984030819)
          ·
            refine ⟨53076466588297850976046229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35384311058865233984030819 53076466588297850976046229)
            ·
              refine ⟨2487959371326461764502167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53076466588297850976046229 2487959371326461764502167)
              ·
                refine ⟨3731939056989692646753251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2487959371326461764502167 3731939056989692646753251)
                ·
                  refine ⟨5597908585484538970129877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731939056989692646753251 5597908585484538970129877)
                  ·
                    refine ⟨131200982472293882112419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5597908585484538970129877 131200982472293882112419)
                    ·
                      rfl

theorem cell23_766539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 7].length) (baseStart_766539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766539 prefixEnd_766539 := by exact prefixLift 766539
  have htrace : WordTrace (prefixWord ++ tailWord_766539) baseStart_766539 baseEnd_766539 := by
    simpa [prefixWord, tailWord_766539, baseEnd_766539] using wordTrace_append hprefix tailTrace_766539
  have hstable : (prefixWord ++ tailWord_766539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766539).length < 2 ^ (prefixWord ++ tailWord_766539).sum := by decide
  have hdescent : baseEnd_766539 < baseStart_766539 := by decide
  rcases family_descends (prefixWord ++ tailWord_766539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766593 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_766593 : Nat := 118140960795 + 766593 * 2 ^ 59
def prefixEnd_766593 : Nat := 4983230072969 + 3 ^ 40 * 766593 * 2
def baseEnd_766593 : Nat := 393630675372224435062009

theorem tailTrace_766593 : CollatzResearch.WordTrace tailWord_766593 prefixEnd_766593 393630675372224435062009 := by
  unfold tailWord_766593
  simp only [CollatzResearch.WordTrace]
  refine ⟨27959943711771959506144433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18639962474514639670762955 27959943711771959506144433)
  ·
    refine ⟨20969957783828969629608325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27959943711771959506144433 20969957783828969629608325)
    ·
      refine ⟨3931867084467931805551561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20969957783828969629608325 3931867084467931805551561)
      ·
        refine ⟨2948900313350948854163671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3931867084467931805551561 2948900313350948854163671)
        ·
          refine ⟨4423350470026423281245507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2948900313350948854163671 4423350470026423281245507)
          ·
            refine ⟨6635025705039634921868261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423350470026423281245507 6635025705039634921868261)
            ·
              refine ⟨1244067319694931547850299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6635025705039634921868261 1244067319694931547850299)
              ·
                refine ⟨1866100979542397321775449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244067319694931547850299 1866100979542397321775449)
                ·
                  refine ⟨1399575734656797991331587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1866100979542397321775449 1399575734656797991331587)
                  ·
                    refine ⟨2099363601985196986997381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1399575734656797991331587 2099363601985196986997381)
                    ·
                      refine ⟨393630675372224435062009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2099363601985196986997381 393630675372224435062009)
                      ·
                        rfl

theorem cell23_766593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_766593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766593 prefixEnd_766593 := by exact prefixLift 766593
  have htrace : WordTrace (prefixWord ++ tailWord_766593) baseStart_766593 baseEnd_766593 := by
    simpa [prefixWord, tailWord_766593, baseEnd_766593] using wordTrace_append hprefix tailTrace_766593
  have hstable : (prefixWord ++ tailWord_766593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766593).length < 2 ^ (prefixWord ++ tailWord_766593).sum := by decide
  have hdescent : baseEnd_766593 < baseStart_766593 := by decide
  rcases family_descends (prefixWord ++ tailWord_766593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766606 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_766606 : Nat := 118140960795 + 766606 * 2 ^ 59
def prefixEnd_766606 : Nat := 4983230072969 + 3 ^ 40 * 766606 * 2
def baseEnd_766606 : Nat := 393637350620732884199449

theorem tailTrace_766606 : CollatzResearch.WordTrace tailWord_766606 prefixEnd_766606 393637350620732884199449 := by
  unfold tailWord_766606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495052232590607840795959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18640278573816575150911781 3495052232590607840795959)
  ·
    refine ⟨5242578348885911761193939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3495052232590607840795959 5242578348885911761193939)
    ·
      refine ⟨7863867523328867641790909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5242578348885911761193939 7863867523328867641790909)
      ·
        refine ⟨2948950321248325365671591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7863867523328867641790909 2948950321248325365671591)
        ·
          refine ⟨4423425481872488048507387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2948950321248325365671591 4423425481872488048507387)
          ·
            refine ⟨6635138222808732072761081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423425481872488048507387 6635138222808732072761081)
            ·
              refine ⟨4976353667106549054570811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6635138222808732072761081 4976353667106549054570811)
              ·
                refine ⟨7464530500659823581856217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4976353667106549054570811 7464530500659823581856217)
                ·
                  refine ⟨5598397875494867686392163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7464530500659823581856217 5598397875494867686392163)
                  ·
                    refine ⟨8397596813242301529588245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5598397875494867686392163 8397596813242301529588245)
                    ·
                      refine ⟨393637350620732884199449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8397596813242301529588245 393637350620732884199449)
                      ·
                        rfl

theorem cell23_766606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_766606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766606 prefixEnd_766606 := by exact prefixLift 766606
  have htrace : WordTrace (prefixWord ++ tailWord_766606) baseStart_766606 baseEnd_766606 := by
    simpa [prefixWord, tailWord_766606, baseEnd_766606] using wordTrace_append hprefix tailTrace_766606
  have hstable : (prefixWord ++ tailWord_766606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766606).length < 2 ^ (prefixWord ++ tailWord_766606).sum := by decide
  have hdescent : baseEnd_766606 < baseStart_766606 := by decide
  rcases family_descends (prefixWord ++ tailWord_766606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766619 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 6]
def baseStart_766619 : Nat := 118140960795 + 766619 * 2 ^ 59
def prefixEnd_766619 : Nat := 4983230072969 + 3 ^ 40 * 766619 * 2
def baseEnd_766619 : Nat := 393644025869241333336889

theorem tailTrace_766619 : CollatzResearch.WordTrace tailWord_766619 prefixEnd_766619 393644025869241333336889 := by
  unfold tailWord_766619
  simp only [CollatzResearch.WordTrace]
  refine ⟨27960892009677765946590911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18640594673118510631060607 27960892009677765946590911)
  ·
    refine ⟨41941338014516648919886367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27960892009677765946590911 41941338014516648919886367)
    ·
      refine ⟨62912007021774973379829551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41941338014516648919886367 62912007021774973379829551)
      ·
        refine ⟨94368010532662460069744327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62912007021774973379829551 94368010532662460069744327)
        ·
          refine ⟨141552015798993690104616491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94368010532662460069744327 141552015798993690104616491)
          ·
            refine ⟨212328023698490535156924737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141552015798993690104616491 212328023698490535156924737)
            ·
              refine ⟨159246017773867901367693553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212328023698490535156924737 159246017773867901367693553)
              ·
                refine ⟨119434513330400926025770165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159246017773867901367693553 119434513330400926025770165)
                ·
                  refine ⟨11196985624725086814915953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119434513330400926025770165 11196985624725086814915953)
                  ·
                    refine ⟨8397739218543815111186965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11196985624725086814915953 8397739218543815111186965)
                    ·
                      refine ⟨393644025869241333336889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8397739218543815111186965 393644025869241333336889)
                      ·
                        rfl

theorem cell23_766619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_766619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766619 prefixEnd_766619 := by exact prefixLift 766619
  have htrace : WordTrace (prefixWord ++ tailWord_766619) baseStart_766619 baseEnd_766619 := by
    simpa [prefixWord, tailWord_766619, baseEnd_766619] using wordTrace_append hprefix tailTrace_766619
  have hstable : (prefixWord ++ tailWord_766619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766619).length < 2 ^ (prefixWord ++ tailWord_766619).sum := by decide
  have hdescent : baseEnd_766619 < baseStart_766619 := by decide
  rcases family_descends (prefixWord ++ tailWord_766619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766643 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 5, 1, 3]
def baseStart_766643 : Nat := 118140960795 + 766643 * 2 ^ 59
def prefixEnd_766643 : Nat := 4983230072969 + 3 ^ 40 * 766643 * 2
def baseEnd_766643 : Nat := 393656349404949239436779

theorem tailTrace_766643 : CollatzResearch.WordTrace tailWord_766643 prefixEnd_766643 393656349404949239436779 := by
  unfold tailWord_766643
  simp only [CollatzResearch.WordTrace]
  refine ⟨27961767361590818045464583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18641178241060545363643055 27961767361590818045464583)
  ·
    refine ⟨41942651042386227068196875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27961767361590818045464583 41942651042386227068196875)
    ·
      refine ⟨62913976563579340602295313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41942651042386227068196875 62913976563579340602295313)
      ·
        refine ⟨47185482422684505451721485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62913976563579340602295313 47185482422684505451721485)
        ·
          refine ⟨17694555908506689544395557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47185482422684505451721485 17694555908506689544395557)
          ·
            refine ⟨3317729232845004289574167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17694555908506689544395557 3317729232845004289574167)
            ·
              refine ⟨4976593849267506434361251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317729232845004289574167 4976593849267506434361251)
              ·
                refine ⟨7464890773901259651541877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4976593849267506434361251 7464890773901259651541877)
                ·
                  refine ⟨699833510053243092332051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7464890773901259651541877 699833510053243092332051)
                  ·
                    refine ⟨1049750265079864638498077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 699833510053243092332051 1049750265079864638498077)
                    ·
                      refine ⟨393656349404949239436779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1049750265079864638498077 393656349404949239436779)
                      ·
                        rfl

theorem cell23_766643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 1, 3].length) (baseStart_766643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766643 prefixEnd_766643 := by exact prefixLift 766643
  have htrace : WordTrace (prefixWord ++ tailWord_766643) baseStart_766643 baseEnd_766643 := by
    simpa [prefixWord, tailWord_766643, baseEnd_766643] using wordTrace_append hprefix tailTrace_766643
  have hstable : (prefixWord ++ tailWord_766643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766643).length < 2 ^ (prefixWord ++ tailWord_766643).sum := by decide
  have hdescent : baseEnd_766643 < baseStart_766643 := by decide
  rcases family_descends (prefixWord ++ tailWord_766643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766647 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 2, 2, 3]
def baseStart_766647 : Nat := 118140960795 + 766647 * 2 ^ 59
def prefixEnd_766647 : Nat := 4983230072969 + 3 ^ 40 * 766647 * 2
def baseEnd_766647 : Nat := 393658403327567223786761

theorem tailTrace_766647 : CollatzResearch.WordTrace tailWord_766647 prefixEnd_766647 393658403327567223786761 := by
  unfold tailWord_766647
  simp only [CollatzResearch.WordTrace]
  refine ⟨27961913253576326728610195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18641275502384217819073463 27961913253576326728610195)
  ·
    refine ⟨41942869880364490092915293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27961913253576326728610195 41942869880364490092915293)
    ·
      refine ⟨15728576205136683784843235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41942869880364490092915293 15728576205136683784843235)
      ·
        refine ⟨23592864307705025677264853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15728576205136683784843235 23592864307705025677264853)
        ·
          refine ⟨552957757211836539310895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 23592864307705025677264853 552957757211836539310895)
          ·
            refine ⟨829436635817754808966343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552957757211836539310895 829436635817754808966343)
            ·
              refine ⟨1244154953726632213449515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829436635817754808966343 1244154953726632213449515)
              ·
                refine ⟨1866232430589948320174273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244154953726632213449515 1866232430589948320174273)
                ·
                  refine ⟨1399674322942461240130705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1866232430589948320174273 1399674322942461240130705)
                  ·
                    refine ⟨1049755742206845930098029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1399674322942461240130705 1049755742206845930098029)
                    ·
                      refine ⟨393658403327567223786761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1049755742206845930098029 393658403327567223786761)
                      ·
                        rfl

theorem cell23_766647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 2, 2, 3].length) (baseStart_766647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766647 prefixEnd_766647 := by exact prefixLift 766647
  have htrace : WordTrace (prefixWord ++ tailWord_766647) baseStart_766647 baseEnd_766647 := by
    simpa [prefixWord, tailWord_766647, baseEnd_766647] using wordTrace_append hprefix tailTrace_766647
  have hstable : (prefixWord ++ tailWord_766647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766647).length < 2 ^ (prefixWord ++ tailWord_766647).sum := by decide
  have hdescent : baseEnd_766647 < baseStart_766647 := by decide
  rcases family_descends (prefixWord ++ tailWord_766647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766693 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 1, 6]
def baseStart_766693 : Nat := 118140960795 + 766693 * 2 ^ 59
def prefixEnd_766693 : Nat := 4983230072969 + 3 ^ 40 * 766693 * 2
def baseEnd_766693 : Nat := 131227341145891347937183

theorem tailTrace_766693 : CollatzResearch.WordTrace tailWord_766693 prefixEnd_766693 131227341145891347937183 := by
  unfold tailWord_766693
  simp only [CollatzResearch.WordTrace]
  refine ⟨27963591011409676584784733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18642394007606451056523155 27963591011409676584784733)
  ·
    refine ⟨10486346629278628719294275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27963591011409676584784733 10486346629278628719294275)
    ·
      refine ⟨15729519943917943078941413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10486346629278628719294275 15729519943917943078941413)
      ·
        refine ⟨2949284989484614327301515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15729519943917943078941413 2949284989484614327301515)
        ·
          refine ⟨4423927484226921490952273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2949284989484614327301515 4423927484226921490952273)
          ·
            refine ⟨3317945613170191118214205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4423927484226921490952273 3317945613170191118214205)
            ·
              refine ⟨1244229604938821669330327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3317945613170191118214205 1244229604938821669330327)
              ·
                refine ⟨1866344407408232503995491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244229604938821669330327 1866344407408232503995491)
                ·
                  refine ⟨2799516611112348755993237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866344407408232503995491 2799516611112348755993237)
                  ·
                    refine ⟨131227341145891347937183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2799516611112348755993237 131227341145891347937183)
                    ·
                      rfl

theorem cell23_766693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_766693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766693 prefixEnd_766693 := by exact prefixLift 766693
  have htrace : WordTrace (prefixWord ++ tailWord_766693) baseStart_766693 baseEnd_766693 := by
    simpa [prefixWord, tailWord_766693, baseEnd_766693] using wordTrace_append hprefix tailTrace_766693
  have hstable : (prefixWord ++ tailWord_766693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766693).length < 2 ^ (prefixWord ++ tailWord_766693).sum := by decide
  have hdescent : baseEnd_766693 < baseStart_766693 := by decide
  rcases family_descends (prefixWord ++ tailWord_766693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766785 : List Nat := [1, 2, 5, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_766785 : Nat := 118140960795 + 766785 * 2 ^ 59
def prefixEnd_766785 : Nat := 4983230072969 + 3 ^ 40 * 766785 * 2
def baseEnd_766785 : Nat := 393729263657887683861127

theorem tailTrace_766785 : CollatzResearch.WordTrace tailWord_766785 prefixEnd_766785 393729263657887683861127 := by
  unfold tailWord_766785
  simp only [CollatzResearch.WordTrace]
  refine ⟨27966946527076376297133809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18644631018050917531422539 27966946527076376297133809)
  ·
    refine ⟨20975209895307282222850357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27966946527076376297133809 20975209895307282222850357)
    ·
      refine ⟨1966425927685057708392221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20975209895307282222850357 1966425927685057708392221)
      ·
        refine ⟨737409722881896640647083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1966425927685057708392221 737409722881896640647083)
        ·
          refine ⟨1106114584322844960970625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737409722881896640647083 1106114584322844960970625)
          ·
            refine ⟨829585938242133720727969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1106114584322844960970625 829585938242133720727969)
            ·
              refine ⟨622189453681600290545977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829585938242133720727969 622189453681600290545977)
              ·
                refine ⟨466642090261200217909483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622189453681600290545977 466642090261200217909483)
                ·
                  refine ⟨699963135391800326864225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466642090261200217909483 699963135391800326864225)
                  ·
                    refine ⟨524972351543850245148169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 699963135391800326864225 524972351543850245148169)
                    ·
                      refine ⟨393729263657887683861127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 524972351543850245148169 393729263657887683861127)
                      ·
                        rfl

theorem cell23_766785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_766785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766785 prefixEnd_766785 := by exact prefixLift 766785
  have htrace : WordTrace (prefixWord ++ tailWord_766785) baseStart_766785 baseEnd_766785 := by
    simpa [prefixWord, tailWord_766785, baseEnd_766785] using wordTrace_append hprefix tailTrace_766785
  have hstable : (prefixWord ++ tailWord_766785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766785).length < 2 ^ (prefixWord ++ tailWord_766785).sum := by decide
  have hdescent : baseEnd_766785 < baseStart_766785 := by decide
  rcases family_descends (prefixWord ++ tailWord_766785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766793 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 2, 4, 3]
def baseStart_766793 : Nat := 118140960795 + 766793 * 2 ^ 59
def prefixEnd_766793 : Nat := 4983230072969 + 3 ^ 40 * 766793 * 2
def baseEnd_766793 : Nat := 393733371503123652561089

theorem tailTrace_766793 : CollatzResearch.WordTrace tailWord_766793 prefixEnd_766793 393733371503123652561089 := by
  unfold tailWord_766793
  simp only [CollatzResearch.WordTrace]
  refine ⟨27967238311047393663425033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18644825540698262442283355 27967238311047393663425033)
  ·
    refine ⟨20975428733285545247568775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27967238311047393663425033 20975428733285545247568775)
    ·
      refine ⟨31463143099928317871353163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20975428733285545247568775 31463143099928317871353163)
      ·
        refine ⟨47194714649892476807029745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31463143099928317871353163 47194714649892476807029745)
        ·
          refine ⟨35396035987419357605272309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47194714649892476807029745 35396035987419357605272309)
          ·
            refine ⟨3318378373820564775494279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35396035987419357605272309 3318378373820564775494279)
            ·
              refine ⟨4977567560730847163241419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3318378373820564775494279 4977567560730847163241419)
              ·
                refine ⟨7466351341096270744862129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4977567560730847163241419 7466351341096270744862129)
                ·
                  refine ⟨5599763505822203058646597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7466351341096270744862129 5599763505822203058646597)
                  ·
                    refine ⟨1049955657341663073496237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5599763505822203058646597 1049955657341663073496237)
                    ·
                      refine ⟨393733371503123652561089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1049955657341663073496237 393733371503123652561089)
                      ·
                        rfl

theorem cell23_766793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 4, 3].length) (baseStart_766793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766793 prefixEnd_766793 := by exact prefixLift 766793
  have htrace : WordTrace (prefixWord ++ tailWord_766793) baseStart_766793 baseEnd_766793 := by
    simpa [prefixWord, tailWord_766793, baseEnd_766793] using wordTrace_append hprefix tailTrace_766793
  have hstable : (prefixWord ++ tailWord_766793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766793).length < 2 ^ (prefixWord ++ tailWord_766793).sum := by decide
  have hdescent : baseEnd_766793 < baseStart_766793 := by decide
  rcases family_descends (prefixWord ++ tailWord_766793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766807 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 1, 4, 2]
def baseStart_766807 : Nat := 118140960795 + 766807 * 2 ^ 59
def prefixEnd_766807 : Nat := 4983230072969 + 3 ^ 40 * 766807 * 2
def baseEnd_766807 : Nat := 393740560232286597786025

theorem tailTrace_766807 : CollatzResearch.WordTrace tailWord_766807 prefixEnd_766807 393740560232286597786025 := by
  unfold tailWord_766807
  simp only [CollatzResearch.WordTrace]
  refine ⟨27967748932996674054434675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18645165955331116036289783 27967748932996674054434675)
  ·
    refine ⟨41951623399495011081652013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27967748932996674054434675 41951623399495011081652013)
    ·
      refine ⟨15731858774810629155619505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41951623399495011081652013 15731858774810629155619505)
      ·
        refine ⟨11798894081107971866714629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15731858774810629155619505 11798894081107971866714629)
        ·
          refine ⟨2212292640207744725008993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11798894081107971866714629 2212292640207744725008993)
          ·
            refine ⟨1659219480155808543756745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2212292640207744725008993 1659219480155808543756745)
            ·
              refine ⟨1244414610116856407817559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1659219480155808543756745 1244414610116856407817559)
              ·
                refine ⟨1866621915175284611726339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244414610116856407817559 1866621915175284611726339)
                ·
                  refine ⟨2799932872762926917589509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866621915175284611726339 2799932872762926917589509)
                  ·
                    refine ⟨524987413643048797048033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2799932872762926917589509 524987413643048797048033)
                    ·
                      refine ⟨393740560232286597786025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 524987413643048797048033 393740560232286597786025)
                      ·
                        rfl

theorem cell23_766807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_766807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766807 prefixEnd_766807 := by exact prefixLift 766807
  have htrace : WordTrace (prefixWord ++ tailWord_766807) baseStart_766807 baseEnd_766807 := by
    simpa [prefixWord, tailWord_766807, baseEnd_766807] using wordTrace_append hprefix tailTrace_766807
  have hstable : (prefixWord ++ tailWord_766807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766807).length < 2 ^ (prefixWord ++ tailWord_766807).sum := by decide
  have hdescent : baseEnd_766807 < baseStart_766807 := by decide
  rcases family_descends (prefixWord ++ tailWord_766807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766843 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 2, 5]
def baseStart_766843 : Nat := 118140960795 + 766843 * 2 ^ 59
def prefixEnd_766843 : Nat := 4983230072969 + 3 ^ 40 * 766843 * 2
def baseEnd_766843 : Nat := 131253015178616152311953

theorem tailTrace_766843 : CollatzResearch.WordTrace tailWord_766843 prefixEnd_766843 131253015178616152311953 := by
  unfold tailWord_766843
  simp only [CollatzResearch.WordTrace]
  refine ⟨27969061960866252202745183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18646041307244168135163455 27969061960866252202745183)
  ·
    refine ⟨41953592941299378304117775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27969061960866252202745183 41953592941299378304117775)
    ·
      refine ⟨62930389411949067456176663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41953592941299378304117775 62930389411949067456176663)
      ·
        refine ⟨94395584117923601184264995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62930389411949067456176663 94395584117923601184264995)
        ·
          refine ⟨141593376176885401776397493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94395584117923601184264995 141593376176885401776397493)
          ·
            refine ⟨13274379016583006416537265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141593376176885401776397493 13274379016583006416537265)
            ·
              refine ⟨9955784262437254812402949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13274379016583006416537265 9955784262437254812402949)
              ·
                refine ⟨1866709549206985277325553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9955784262437254812402949 1866709549206985277325553)
                ·
                  refine ⟨1400032161905238957994165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1866709549206985277325553 1400032161905238957994165)
                  ·
                    refine ⟨131253015178616152311953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1400032161905238957994165 131253015178616152311953)
                    ·
                      rfl

theorem cell23_766843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 5].length) (baseStart_766843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766843 prefixEnd_766843 := by exact prefixLift 766843
  have htrace : WordTrace (prefixWord ++ tailWord_766843) baseStart_766843 baseEnd_766843 := by
    simpa [prefixWord, tailWord_766843, baseEnd_766843] using wordTrace_append hprefix tailTrace_766843
  have hstable : (prefixWord ++ tailWord_766843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766843).length < 2 ^ (prefixWord ++ tailWord_766843).sum := by decide
  have hdescent : baseEnd_766843 < baseStart_766843 := by decide
  rcases family_descends (prefixWord ++ tailWord_766843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766880 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 1, 6, 2]
def baseStart_766880 : Nat := 118140960795 + 766880 * 2 ^ 59
def prefixEnd_766880 : Nat := 4983230072969 + 3 ^ 40 * 766880 * 2
def baseEnd_766880 : Nat := 393778044320064812173189

theorem tailTrace_766880 : CollatzResearch.WordTrace tailWord_766880 prefixEnd_766880 393778044320064812173189 := by
  unfold tailWord_766880
  simp only [CollatzResearch.WordTrace]
  refine ⟨13985205730866103760921047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18646940974488138347894729 13985205730866103760921047)
  ·
    refine ⟨20977808596299155641381571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13985205730866103760921047 20977808596299155641381571)
    ·
      refine ⟨31466712894448733462072357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20977808596299155641381571 31466712894448733462072357)
      ·
        refine ⟨5900008667709137524138567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31466712894448733462072357 5900008667709137524138567)
        ·
          refine ⟨8850013001563706286207851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5900008667709137524138567 8850013001563706286207851)
          ·
            refine ⟨13275019502345559429311777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8850013001563706286207851 13275019502345559429311777)
            ·
              refine ⟨9956264626759169571983833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13275019502345559429311777 9956264626759169571983833)
              ·
                refine ⟨7467198470069377178987875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9956264626759169571983833 7467198470069377178987875)
                ·
                  refine ⟨11200797705104065768481813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7467198470069377178987875 11200797705104065768481813)
                  ·
                    refine ⟨525037392426753082897585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11200797705104065768481813 525037392426753082897585)
                    ·
                      refine ⟨393778044320064812173189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 525037392426753082897585 393778044320064812173189)
                      ·
                        rfl

theorem cell23_766880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_766880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766880 prefixEnd_766880 := by exact prefixLift 766880
  have htrace : WordTrace (prefixWord ++ tailWord_766880) baseStart_766880 baseEnd_766880 := by
    simpa [prefixWord, tailWord_766880, baseEnd_766880] using wordTrace_append hprefix tailTrace_766880
  have hstable : (prefixWord ++ tailWord_766880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766880).length < 2 ^ (prefixWord ++ tailWord_766880).sum := by decide
  have hdescent : baseEnd_766880 < baseStart_766880 := by decide
  rcases family_descends (prefixWord ++ tailWord_766880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766897 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 2, 1, 4]
def baseStart_766897 : Nat := 118140960795 + 766897 * 2 ^ 59
def prefixEnd_766897 : Nat := 4983230072969 + 3 ^ 40 * 766897 * 2
def baseEnd_766897 : Nat := 393786773491191245660611

theorem tailTrace_766897 : CollatzResearch.WordTrace tailWord_766897 prefixEnd_766897 393786773491191245660611 := by
  unfold tailWord_766897
  simp only [CollatzResearch.WordTrace]
  refine ⟨27971031502670619425210945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18647354335113746283473963 27971031502670619425210945)
  ·
    refine ⟨20978273627002964568908209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27971031502670619425210945 20978273627002964568908209)
    ·
      refine ⟨15733705220252223426681157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20978273627002964568908209 15733705220252223426681157)
      ·
        refine ⟨2950069728797291892502717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15733705220252223426681157 2950069728797291892502717)
        ·
          refine ⟨1106276148298984459688519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2950069728797291892502717 1106276148298984459688519)
          ·
            refine ⟨1659414222448476689532779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106276148298984459688519 1659414222448476689532779)
            ·
              refine ⟨2489121333672715034299169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659414222448476689532779 2489121333672715034299169)
              ·
                refine ⟨1866841000254536275724377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2489121333672715034299169 1866841000254536275724377)
                ·
                  refine ⟨1400130750190902206793283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1866841000254536275724377 1400130750190902206793283)
                  ·
                    refine ⟨2100196125286353310189925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1400130750190902206793283 2100196125286353310189925)
                    ·
                      refine ⟨393786773491191245660611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2100196125286353310189925 393786773491191245660611)
                      ·
                        rfl

theorem cell23_766897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_766897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766897 prefixEnd_766897 := by exact prefixLift 766897
  have htrace : WordTrace (prefixWord ++ tailWord_766897) baseStart_766897 baseEnd_766897 := by
    simpa [prefixWord, tailWord_766897, baseEnd_766897] using wordTrace_append hprefix tailTrace_766897
  have hstable : (prefixWord ++ tailWord_766897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766897).length < 2 ^ (prefixWord ++ tailWord_766897).sum := by decide
  have hdescent : baseEnd_766897 < baseStart_766897 := by decide
  rcases family_descends (prefixWord ++ tailWord_766897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766903 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 8]
def baseStart_766903 : Nat := 118140960795 + 766903 * 2 ^ 59
def prefixEnd_766903 : Nat := 4983230072969 + 3 ^ 40 * 766903 * 2
def baseEnd_766903 : Nat := 43754428263902024687287

theorem tailTrace_766903 : CollatzResearch.WordTrace tailWord_766903 prefixEnd_766903 43754428263902024687287 := by
  unfold tailWord_766903
  simp only [CollatzResearch.WordTrace]
  refine ⟨27971250340648882449929363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18647500227099254966619575 27971250340648882449929363)
  ·
    refine ⟨41956875510973323674894045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27971250340648882449929363 41956875510973323674894045)
    ·
      refine ⟨15733828316614996378085267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41956875510973323674894045 15733828316614996378085267)
      ·
        refine ⟨23600742474922494567127901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15733828316614996378085267 23600742474922494567127901)
        ·
          refine ⟨8850278428095935462672963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23600742474922494567127901 8850278428095935462672963)
          ·
            refine ⟨13275417642143903194009445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8850278428095935462672963 13275417642143903194009445)
            ·
              refine ⟨2489140807901981848876771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13275417642143903194009445 2489140807901981848876771)
              ·
                refine ⟨3733711211852972773315157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489140807901981848876771 3733711211852972773315157)
                ·
                  refine ⟨43754428263902024687287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3733711211852972773315157 43754428263902024687287)
                  ·
                    rfl

theorem cell23_766903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 8].length) (baseStart_766903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766903 prefixEnd_766903 := by exact prefixLift 766903
  have htrace : WordTrace (prefixWord ++ tailWord_766903) baseStart_766903 baseEnd_766903 := by
    simpa [prefixWord, tailWord_766903, baseEnd_766903] using wordTrace_append hprefix tailTrace_766903
  have hstable : (prefixWord ++ tailWord_766903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766903).length < 2 ^ (prefixWord ++ tailWord_766903).sum := by decide
  have hdescent : baseEnd_766903 < baseStart_766903 := by decide
  rcases family_descends (prefixWord ++ tailWord_766903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766934 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_766934 : Nat := 118140960795 + 766934 * 2 ^ 59
def prefixEnd_766934 : Nat := 4983230072969 + 3 ^ 40 * 766934 * 2
def baseEnd_766934 : Nat := 393805772275407600897941

theorem tailTrace_766934 : CollatzResearch.WordTrace tailWord_766934 prefixEnd_766934 393805772275407600897941 := by
  unfold tailWord_766934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1748273812721035921519241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18648254002357716496205237 1748273812721035921519241)
  ·
    refine ⟨1311205359540776941139431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1748273812721035921519241 1311205359540776941139431)
    ·
      refine ⟨1966808039311165411709147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1311205359540776941139431 1966808039311165411709147)
      ·
        refine ⟨2950212058966748117563721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1966808039311165411709147 2950212058966748117563721)
        ·
          refine ⟨2212659044225061088172791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2950212058966748117563721 2212659044225061088172791)
          ·
            refine ⟨3318988566337591632259187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212659044225061088172791 3318988566337591632259187)
            ·
              refine ⟨4978482849506387448388781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3318988566337591632259187 4978482849506387448388781)
              ·
                refine ⟨1866931068564895293145793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4978482849506387448388781 1866931068564895293145793)
                ·
                  refine ⟨1400198301423671469859345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1866931068564895293145793 1400198301423671469859345)
                  ·
                    refine ⟨1050148726067753602394509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1400198301423671469859345 1050148726067753602394509)
                    ·
                      refine ⟨393805772275407600897941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1050148726067753602394509 393805772275407600897941)
                      ·
                        rfl

theorem cell23_766934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_766934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766934 prefixEnd_766934 := by exact prefixLift 766934
  have htrace : WordTrace (prefixWord ++ tailWord_766934) baseStart_766934 baseEnd_766934 := by
    simpa [prefixWord, tailWord_766934, baseEnd_766934] using wordTrace_append hprefix tailTrace_766934
  have hstable : (prefixWord ++ tailWord_766934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766934).length < 2 ^ (prefixWord ++ tailWord_766934).sum := by decide
  have hdescent : baseEnd_766934 < baseStart_766934 := by decide
  rcases family_descends (prefixWord ++ tailWord_766934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766958 : List Nat := [4, 1, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_766958 : Nat := 118140960795 + 766958 * 2 ^ 59
def prefixEnd_766958 : Nat := 4983230072969 + 3 ^ 40 * 766958 * 2
def baseEnd_766958 : Nat := 131272698603705168999277

theorem tailTrace_766958 : CollatzResearch.WordTrace tailWord_766958 prefixEnd_766958 131272698603705168999277 := by
  unfold tailWord_766958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3496657044431203355397691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18648837570299751228787685 3496657044431203355397691)
  ·
    refine ⟨5244985566646805033096537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3496657044431203355397691 5244985566646805033096537)
    ·
      refine ⟨3933739174985103774822403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5244985566646805033096537 3933739174985103774822403)
      ·
        refine ⟨5900608762477655662233605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3933739174985103774822403 5900608762477655662233605)
        ·
          refine ⟨1106364142964560436668801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5900608762477655662233605 1106364142964560436668801)
          ·
            refine ⟨829773107223420327501601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1106364142964560436668801 829773107223420327501601)
            ·
              refine ⟨622329830417565245626201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829773107223420327501601 622329830417565245626201)
              ·
                refine ⟨466747372813173934219651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622329830417565245626201 466747372813173934219651)
                ·
                  refine ⟨700121059219760901329477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466747372813173934219651 700121059219760901329477)
                  ·
                    refine ⟨131272698603705168999277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 700121059219760901329477 131272698603705168999277)
                    ·
                      rfl

theorem cell23_766958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_766958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766958 prefixEnd_766958 := by exact prefixLift 766958
  have htrace : WordTrace (prefixWord ++ tailWord_766958) baseStart_766958 baseEnd_766958 := by
    simpa [prefixWord, tailWord_766958, baseEnd_766958] using wordTrace_append hprefix tailTrace_766958
  have hstable : (prefixWord ++ tailWord_766958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766958).length < 2 ^ (prefixWord ++ tailWord_766958).sum := by decide
  have hdescent : baseEnd_766958 < baseStart_766958 := by decide
  rcases family_descends (prefixWord ++ tailWord_766958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766993 : List Nat := [1, 2, 2, 1, 1, 2, 1, 13]
def baseStart_766993 : Nat := 118140960795 + 766993 * 2 ^ 59
def prefixEnd_766993 : Nat := 4983230072969 + 3 ^ 40 * 766993 * 2
def baseEnd_766993 : Nat := 14586521023482328520747

theorem tailTrace_766993 : CollatzResearch.WordTrace tailWord_766993 prefixEnd_766993 14586521023482328520747 := by
  unfold tailWord_766993
  simp only [CollatzResearch.WordTrace]
  refine ⟨27974532910322827820705633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18649688606881885213803755 27974532910322827820705633)
  ·
    refine ⟨20980899682742120865529225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27974532910322827820705633 20980899682742120865529225)
    ·
      refine ⟨15735674762056590649146919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20980899682742120865529225 15735674762056590649146919)
      ·
        refine ⟨23603512143084885973720379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15735674762056590649146919 23603512143084885973720379)
        ·
          refine ⟨35405268214627328960580569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23603512143084885973720379 35405268214627328960580569)
          ·
            refine ⟨26553951160970496720435427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35405268214627328960580569 26553951160970496720435427)
            ·
              refine ⟨39830926741455745080653141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26553951160970496720435427 39830926741455745080653141)
              ·
                refine ⟨14586521023482328520747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 39830926741455745080653141 14586521023482328520747)
                ·
                  rfl

theorem cell23_766993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 13].length) (baseStart_766993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_766993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_766993 prefixEnd_766993 := by exact prefixLift 766993
  have htrace : WordTrace (prefixWord ++ tailWord_766993) baseStart_766993 baseEnd_766993 := by
    simpa [prefixWord, tailWord_766993, baseEnd_766993] using wordTrace_append hprefix tailTrace_766993
  have hstable : (prefixWord ++ tailWord_766993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766993).length < 2 ^ (prefixWord ++ tailWord_766993).sum := by decide
  have hdescent : baseEnd_766993 < baseStart_766993 := by decide
  rcases family_descends (prefixWord ++ tailWord_766993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767003 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 7]
def baseStart_767003 : Nat := 118140960795 + 767003 * 2 ^ 59
def prefixEnd_767003 : Nat := 4983230072969 + 3 ^ 40 * 767003 * 2
def baseEnd_767003 : Nat := 393841202440567830935123

theorem tailTrace_767003 : CollatzResearch.WordTrace tailWord_767003 prefixEnd_767003 393841202440567830935123 := by
  unfold tailWord_767003
  simp only [CollatzResearch.WordTrace]
  refine ⟨27974897640286599528569663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18649931760191066352379775 27974897640286599528569663)
  ·
    refine ⟨41962346460429899292854495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27974897640286599528569663 41962346460429899292854495)
    ·
      refine ⟨62943519690644848939281743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41962346460429899292854495 62943519690644848939281743)
      ·
        refine ⟨94415279535967273408922615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62943519690644848939281743 94415279535967273408922615)
        ·
          refine ⟨141622919303950910113383923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94415279535967273408922615 141622919303950910113383923)
          ·
            refine ⟨212434378955926365170075885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141622919303950910113383923 212434378955926365170075885)
            ·
              refine ⟨79662892108472386938778457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212434378955926365170075885 79662892108472386938778457)
              ·
                refine ⟨59747169081354290204083843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79662892108472386938778457 59747169081354290204083843)
                ·
                  refine ⟨89620753622031435306125765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59747169081354290204083843 89620753622031435306125765)
                  ·
                    refine ⟨16803891304130894119898581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89620753622031435306125765 16803891304130894119898581)
                    ·
                      refine ⟨393841202440567830935123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16803891304130894119898581 393841202440567830935123)
                      ·
                        rfl

theorem cell23_767003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_767003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767003 prefixEnd_767003 := by exact prefixLift 767003
  have htrace : WordTrace (prefixWord ++ tailWord_767003) baseStart_767003 baseEnd_767003 := by
    simpa [prefixWord, tailWord_767003, baseEnd_767003] using wordTrace_append hprefix tailTrace_767003
  have hstable : (prefixWord ++ tailWord_767003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767003).length < 2 ^ (prefixWord ++ tailWord_767003).sum := by decide
  have hdescent : baseEnd_767003 < baseStart_767003 := by decide
  rcases family_descends (prefixWord ++ tailWord_767003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767004 : List Nat := [2, 2, 3, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_767004 : Nat := 118140960795 + 767004 * 2 ^ 59
def prefixEnd_767004 : Nat := 4983230072969 + 3 ^ 40 * 767004 * 2
def baseEnd_767004 : Nat := 393841715921222327022619

theorem tailTrace_767004 : CollatzResearch.WordTrace tailWord_767004 prefixEnd_767004 393841715921222327022619 := by
  unfold tailWord_767004
  simp only [CollatzResearch.WordTrace]
  refine ⟨13987467056641488349678033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18649956075521984466237377 13987467056641488349678033)
  ·
    refine ⟨10490600292481116262258525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13987467056641488349678033 10490600292481116262258525)
    ·
      refine ⟨3933975109680418598346947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10490600292481116262258525 3933975109680418598346947)
      ·
        refine ⟨5900962664520627897520421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3933975109680418598346947 5900962664520627897520421)
        ·
          refine ⟨1106430499597617730785079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5900962664520627897520421 1106430499597617730785079)
          ·
            refine ⟨1659645749396426596177619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106430499597617730785079 1659645749396426596177619)
            ·
              refine ⟨2489468624094639894266429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659645749396426596177619 2489468624094639894266429)
              ·
                refine ⟨933550734035489960349911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2489468624094639894266429 933550734035489960349911)
                ·
                  refine ⟨1400326101053234940524867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 933550734035489960349911 1400326101053234940524867)
                  ·
                    refine ⟨2100489151579852410787301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1400326101053234940524867 2100489151579852410787301)
                    ·
                      refine ⟨393841715921222327022619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2100489151579852410787301 393841715921222327022619)
                      ·
                        rfl

theorem cell23_767004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_767004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767004 prefixEnd_767004 := by exact prefixLift 767004
  have htrace : WordTrace (prefixWord ++ tailWord_767004) baseStart_767004 baseEnd_767004 := by
    simpa [prefixWord, tailWord_767004, baseEnd_767004] using wordTrace_append hprefix tailTrace_767004
  have hstable : (prefixWord ++ tailWord_767004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767004).length < 2 ^ (prefixWord ++ tailWord_767004).sum := by decide
  have hdescent : baseEnd_767004 < baseStart_767004 := by decide
  rcases family_descends (prefixWord ++ tailWord_767004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767010 : List Nat := [3, 3, 1, 1, 1, 4, 10]
def baseStart_767010 : Nat := 118140960795 + 767010 * 2 ^ 59
def prefixEnd_767010 : Nat := 4983230072969 + 3 ^ 40 * 767010 * 2
def baseEnd_767010 : Nat := 4862281442038880290711

theorem tailTrace_767010 : CollatzResearch.WordTrace tailWord_767010 prefixEnd_767010 4862281442038880290711 := by
  unfold tailWord_767010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993788237815309931018621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18650101967507493149382989 6993788237815309931018621)
  ·
    refine ⟨2622670589180741224131983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6993788237815309931018621 2622670589180741224131983)
    ·
      refine ⟨3934005883771111836197975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2622670589180741224131983 3934005883771111836197975)
      ·
        refine ⟨5901008825656667754296963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3934005883771111836197975 5901008825656667754296963)
        ·
          refine ⟨8851513238485001631445445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5901008825656667754296963 8851513238485001631445445)
          ·
            refine ⟨1659658732215937805896021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8851513238485001631445445 1659658732215937805896021)
            ·
              refine ⟨4862281442038880290711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1659658732215937805896021 4862281442038880290711)
              ·
                rfl

theorem cell23_767010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 10].length) (baseStart_767010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767010 prefixEnd_767010 := by exact prefixLift 767010
  have htrace : WordTrace (prefixWord ++ tailWord_767010) baseStart_767010 baseEnd_767010 := by
    simpa [prefixWord, tailWord_767010, baseEnd_767010] using wordTrace_append hprefix tailTrace_767010
  have hstable : (prefixWord ++ tailWord_767010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767010).length < 2 ^ (prefixWord ++ tailWord_767010).sum := by decide
  have hdescent : baseEnd_767010 < baseStart_767010 := by decide
  rcases family_descends (prefixWord ++ tailWord_767010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767041 : List Nat := [1, 2, 5, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_767041 : Nat := 118140960795 + 767041 * 2 ^ 59
def prefixEnd_767041 : Nat := 4983230072969 + 3 ^ 40 * 767041 * 2
def baseEnd_767041 : Nat := 393860714705438682259949

theorem tailTrace_767041 : CollatzResearch.WordTrace tailWord_767041 prefixEnd_767041 393860714705438682259949 := by
  unfold tailWord_767041
  simp only [CollatzResearch.WordTrace]
  refine ⟨27976283614148932018452977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18650855742765954678968651 27976283614148932018452977)
  ·
    refine ⟨20982212710611699013839733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27976283614148932018452977 20982212710611699013839733)
    ·
      refine ⟨1967082441619846782547475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20982212710611699013839733 1967082441619846782547475)
      ·
        refine ⟨2950623662429770173821213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967082441619846782547475 2950623662429770173821213)
        ·
          refine ⟨1106483873411163815182955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2950623662429770173821213 1106483873411163815182955)
          ·
            refine ⟨1659725810116745722774433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106483873411163815182955 1659725810116745722774433)
            ·
              refine ⟨1244794357587559292080825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1659725810116745722774433 1244794357587559292080825)
              ·
                refine ⟨933595768190669469060619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244794357587559292080825 933595768190669469060619)
                ·
                  refine ⟨1400393652286004203590929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 933595768190669469060619 1400393652286004203590929)
                  ·
                    refine ⟨1050295239214503152693197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1400393652286004203590929 1050295239214503152693197)
                    ·
                      refine ⟨393860714705438682259949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1050295239214503152693197 393860714705438682259949)
                      ·
                        rfl

theorem cell23_767041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_767041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767041 prefixEnd_767041 := by exact prefixLift 767041
  have htrace : WordTrace (prefixWord ++ tailWord_767041) baseStart_767041 baseEnd_767041 := by
    simpa [prefixWord, tailWord_767041, baseEnd_767041] using wordTrace_append hprefix tailTrace_767041
  have hstable : (prefixWord ++ tailWord_767041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767041).length < 2 ^ (prefixWord ++ tailWord_767041).sum := by decide
  have hdescent : baseEnd_767041 < baseStart_767041 := by decide
  rcases family_descends (prefixWord ++ tailWord_767041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767050 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_767050 : Nat := 118140960795 + 767050 * 2 ^ 59
def prefixEnd_767050 : Nat := 4983230072969 + 3 ^ 40 * 767050 * 2
def baseEnd_767050 : Nat := 393865336031329147047407

theorem tailTrace_767050 : CollatzResearch.WordTrace tailWord_767050 prefixEnd_767050 393865336031329147047407 := by
  unfold tailWord_767050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6994152967779081638882651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18651074580744217703687069 6994152967779081638882651)
  ·
    refine ⟨10491229451668622458323977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6994152967779081638882651 10491229451668622458323977)
    ·
      refine ⟨7868422088751466843742983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10491229451668622458323977 7868422088751466843742983)
      ·
        refine ⟨11802633133127200265614475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7868422088751466843742983 11802633133127200265614475)
        ·
          refine ⟨17703949699690800398421713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11802633133127200265614475 17703949699690800398421713)
          ·
            refine ⟨13277962274768100298816285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17703949699690800398421713 13277962274768100298816285)
            ·
              refine ⟨4979235853038037612056107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13277962274768100298816285 4979235853038037612056107)
              ·
                refine ⟨7468853779557056418084161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4979235853038037612056107 7468853779557056418084161)
                ·
                  refine ⟨5601640334667792313563121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7468853779557056418084161 5601640334667792313563121)
                  ·
                    refine ⟨4201230251000844235172341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5601640334667792313563121 4201230251000844235172341)
                    ·
                      refine ⟨393865336031329147047407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4201230251000844235172341 393865336031329147047407)
                      ·
                        rfl

theorem cell23_767050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_767050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767050 prefixEnd_767050 := by exact prefixLift 767050
  have htrace : WordTrace (prefixWord ++ tailWord_767050) baseStart_767050 baseEnd_767050 := by
    simpa [prefixWord, tailWord_767050, baseEnd_767050] using wordTrace_append hprefix tailTrace_767050
  have hstable : (prefixWord ++ tailWord_767050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767050).length < 2 ^ (prefixWord ++ tailWord_767050).sum := by decide
  have hdescent : baseEnd_767050 < baseStart_767050 := by decide
  rcases family_descends (prefixWord ++ tailWord_767050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767064 : List Nat := [2, 1, 2, 2, 1, 3, 1, 5, 1, 3, 2]
def baseStart_767064 : Nat := 118140960795 + 767064 * 2 ^ 59
def prefixEnd_767064 : Nat := 4983230072969 + 3 ^ 40 * 767064 * 2
def baseEnd_767064 : Nat := 393872524760492092272343

theorem tailTrace_767064 : CollatzResearch.WordTrace tailWord_767064 prefixEnd_767064 393872524760492092272343 := by
  unfold tailWord_767064
  simp only [CollatzResearch.WordTrace]
  refine ⟨13988561246532803473270123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18651414995377071297693497 13988561246532803473270123)
  ·
    refine ⟨20982841869799205209905185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13988561246532803473270123 20982841869799205209905185)
    ·
      refine ⟨15737131402349403907428889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20982841869799205209905185 15737131402349403907428889)
      ·
        refine ⟨11802848551762052930571667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15737131402349403907428889 11802848551762052930571667)
        ·
          refine ⟨17704272827643079395857501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11802848551762052930571667 17704272827643079395857501)
          ·
            refine ⟨6639102310366154773446563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17704272827643079395857501 6639102310366154773446563)
            ·
              refine ⟨9958653465549232160169845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6639102310366154773446563 9958653465549232160169845)
              ·
                refine ⟨933623762395240515015923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9958653465549232160169845 933623762395240515015923)
                ·
                  refine ⟨1400435643592860772523885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 933623762395240515015923 1400435643592860772523885)
                  ·
                    refine ⟨525163366347322789696457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1400435643592860772523885 525163366347322789696457)
                    ·
                      refine ⟨393872524760492092272343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 525163366347322789696457 393872524760492092272343)
                      ·
                        rfl

theorem cell23_767064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_767064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767064 prefixEnd_767064 := by exact prefixLift 767064
  have htrace : WordTrace (prefixWord ++ tailWord_767064) baseStart_767064 baseEnd_767064 := by
    simpa [prefixWord, tailWord_767064, baseEnd_767064] using wordTrace_append hprefix tailTrace_767064
  have hstable : (prefixWord ++ tailWord_767064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767064).length < 2 ^ (prefixWord ++ tailWord_767064).sum := by decide
  have hdescent : baseEnd_767064 < baseStart_767064 := by decide
  rcases family_descends (prefixWord ++ tailWord_767064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767100 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 9]
def baseStart_767100 : Nat := 118140960795 + 767100 * 2 ^ 59
def prefixEnd_767100 : Nat := 4983230072969 + 3 ^ 40 * 767100 * 2
def baseEnd_767100 : Nat := 43765667784894883491353

theorem tailTrace_767100 : CollatzResearch.WordTrace tailWord_767100 prefixEnd_767100 43765667784894883491353 := by
  unfold tailWord_767100
  simp only [CollatzResearch.WordTrace]
  refine ⟨13989217760467592547425377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18652290347290123396567169 13989217760467592547425377)
  ·
    refine ⟨10491913320350694410569033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13989217760467592547425377 10491913320350694410569033)
    ·
      refine ⟨7868934990263020807926775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10491913320350694410569033 7868934990263020807926775)
      ·
        refine ⟨11803402485394531211890163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7868934990263020807926775 11803402485394531211890163)
        ·
          refine ⟨17705103728091796817835245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11803402485394531211890163 17705103728091796817835245)
          ·
            refine ⟨6639413898034423806688217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17705103728091796817835245 6639413898034423806688217)
            ·
              refine ⟨4979560423525817855016163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6639413898034423806688217 4979560423525817855016163)
              ·
                refine ⟨7469340635288726782524245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4979560423525817855016163 7469340635288726782524245)
                ·
                  refine ⟨43765667784894883491353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7469340635288726782524245 43765667784894883491353)
                  ·
                    rfl

theorem cell23_767100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_767100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767100 prefixEnd_767100 := by exact prefixLift 767100
  have htrace : WordTrace (prefixWord ++ tailWord_767100) baseStart_767100 baseEnd_767100 := by
    simpa [prefixWord, tailWord_767100, baseEnd_767100] using wordTrace_append hprefix tailTrace_767100
  have hstable : (prefixWord ++ tailWord_767100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767100).length < 2 ^ (prefixWord ++ tailWord_767100).sum := by decide
  have hdescent : baseEnd_767100 < baseStart_767100 := by decide
  rcases family_descends (prefixWord ++ tailWord_767100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767128 : List Nat := [2, 1, 2, 4, 2, 2, 2, 2, 2, 2, 2]
def baseStart_767128 : Nat := 118140960795 + 767128 * 2 ^ 59
def prefixEnd_767128 : Nat := 4983230072969 + 3 ^ 40 * 767128 * 2
def baseEnd_767128 : Nat := 393905387522379841872049

theorem tailTrace_767128 : CollatzResearch.WordTrace tailWord_767128 prefixEnd_767128 393905387522379841872049 := by
  unfold tailWord_767128
  simp only [CollatzResearch.WordTrace]
  refine ⟨13989728382416872938435019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18652971176555830584580025 13989728382416872938435019)
  ·
    refine ⟨20984592573625309407652529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13989728382416872938435019 20984592573625309407652529)
    ·
      refine ⟨15738444430218982055739397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20984592573625309407652529 15738444430218982055739397)
      ·
        refine ⟨2950958330666059135451137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15738444430218982055739397 2950958330666059135451137)
        ·
          refine ⟨2213218747999544351588353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2950958330666059135451137 2213218747999544351588353)
          ·
            refine ⟨1659914060999658263691265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2213218747999544351588353 1659914060999658263691265)
            ·
              refine ⟨1244935545749743697768449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1659914060999658263691265 1244935545749743697768449)
              ·
                refine ⟨933701659312307773326337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244935545749743697768449 933701659312307773326337)
                ·
                  refine ⟨700276244484230829994753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 933701659312307773326337 700276244484230829994753)
                  ·
                    refine ⟨525207183363173122496065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 700276244484230829994753 525207183363173122496065)
                    ·
                      refine ⟨393905387522379841872049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 525207183363173122496065 393905387522379841872049)
                      ·
                        rfl

theorem cell23_767128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_767128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767128 prefixEnd_767128 := by exact prefixLift 767128
  have htrace : WordTrace (prefixWord ++ tailWord_767128) baseStart_767128 baseEnd_767128 := by
    simpa [prefixWord, tailWord_767128, baseEnd_767128] using wordTrace_append hprefix tailTrace_767128
  have hstable : (prefixWord ++ tailWord_767128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767128).length < 2 ^ (prefixWord ++ tailWord_767128).sum := by decide
  have hdescent : baseEnd_767128 < baseStart_767128 := by decide
  rcases family_descends (prefixWord ++ tailWord_767128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767160 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 1, 10]
def baseStart_767160 : Nat := 118140960795 + 767160 * 2 ^ 59
def prefixEnd_767160 : Nat := 4983230072969 + 3 ^ 40 * 767160 * 2
def baseEnd_767160 : Nat := 131307272967774572223967

theorem tailTrace_767160 : CollatzResearch.WordTrace tailWord_767160 prefixEnd_767160 131307272967774572223967 := by
  unfold tailWord_767160
  simp only [CollatzResearch.WordTrace]
  refine ⟨13990311950358907671017467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18653749267145210228023289 13990311950358907671017467)
  ·
    refine ⟨20985467925538361506526201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13990311950358907671017467 20985467925538361506526201)
    ·
      refine ⟨15739100944153771129894651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20985467925538361506526201 15739100944153771129894651)
      ·
        refine ⟨23608651416230656694841977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15739100944153771129894651 23608651416230656694841977)
        ·
          refine ⟨17706488562172992521131483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23608651416230656694841977 17706488562172992521131483)
          ·
            refine ⟨26559732843259488781697225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17706488562172992521131483 26559732843259488781697225)
            ·
              refine ⟨19919799632444616586272919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26559732843259488781697225 19919799632444616586272919)
              ·
                refine ⟨29879699448666924879409379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19919799632444616586272919 29879699448666924879409379)
                ·
                  refine ⟨44819549173000387319114069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29879699448666924879409379 44819549173000387319114069)
                  ·
                    refine ⟨131307272967774572223967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 44819549173000387319114069 131307272967774572223967)
                    ·
                      rfl

theorem cell23_767160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_767160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767160 prefixEnd_767160 := by exact prefixLift 767160
  have htrace : WordTrace (prefixWord ++ tailWord_767160) baseStart_767160 baseEnd_767160 := by
    simpa [prefixWord, tailWord_767160, baseEnd_767160] using wordTrace_append hprefix tailTrace_767160
  have hstable : (prefixWord ++ tailWord_767160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767160).length < 2 ^ (prefixWord ++ tailWord_767160).sum := by decide
  have hdescent : baseEnd_767160 < baseStart_767160 := by decide
  rcases family_descends (prefixWord ++ tailWord_767160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767164 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 2, 5]
def baseStart_767164 : Nat := 118140960795 + 767164 * 2 ^ 59
def prefixEnd_767164 : Nat := 4983230072969 + 3 ^ 40 * 767164 * 2
def baseEnd_767164 : Nat := 131307957608647233673961

theorem tailTrace_767164 : CollatzResearch.WordTrace tailWord_767164 prefixEnd_767164 131307957608647233673961 := by
  unfold tailWord_767164
  simp only [CollatzResearch.WordTrace]
  refine ⟨13990384896351662012590273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18653846528468882683453697 13990384896351662012590273)
  ·
    refine ⟨10492788672263746509442705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13990384896351662012590273 10492788672263746509442705)
    ·
      refine ⟨7869591504197809882082029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10492788672263746509442705 7869591504197809882082029)
      ·
        refine ⟨2951096814074178705780761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7869591504197809882082029 2951096814074178705780761)
        ·
          refine ⟨2213322610555634029335571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2951096814074178705780761 2213322610555634029335571)
          ·
            refine ⟨3319983915833451044003357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2213322610555634029335571 3319983915833451044003357)
            ·
              refine ⟨1244993968437544141501259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3319983915833451044003357 1244993968437544141501259)
              ·
                refine ⟨1867490952656316212251889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244993968437544141501259 1867490952656316212251889)
                ·
                  refine ⟨1400618214492237159188917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1867490952656316212251889 1400618214492237159188917)
                  ·
                    refine ⟨131307957608647233673961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1400618214492237159188917 131307957608647233673961)
                    ·
                      rfl

theorem cell23_767164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_767164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767164 prefixEnd_767164 := by exact prefixLift 767164
  have htrace : WordTrace (prefixWord ++ tailWord_767164) baseStart_767164 baseEnd_767164 := by
    simpa [prefixWord, tailWord_767164, baseEnd_767164] using wordTrace_append hprefix tailTrace_767164
  have hstable : (prefixWord ++ tailWord_767164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767164).length < 2 ^ (prefixWord ++ tailWord_767164).sum := by decide
  have hdescent : baseEnd_767164 < baseStart_767164 := by decide
  rcases family_descends (prefixWord ++ tailWord_767164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767217 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 1, 7, 3]
def baseStart_767217 : Nat := 118140960795 + 767217 * 2 ^ 59
def prefixEnd_767217 : Nat := 4983230072969 + 3 ^ 40 * 767217 * 2
def baseEnd_767217 : Nat := 393951087300629993659139

theorem tailTrace_767217 : CollatzResearch.WordTrace tailWord_767217 prefixEnd_767217 393951087300629993659139 := by
  unfold tailWord_767217
  simp only [CollatzResearch.WordTrace]
  refine ⟨27982702861511314076859905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18655135241007542717906603 27982702861511314076859905)
  ·
    refine ⟨20987027146133485557644929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27982702861511314076859905 20987027146133485557644929)
    ·
      refine ⟨15740270359600114168233697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20987027146133485557644929 15740270359600114168233697)
      ·
        refine ⟨11805202769700085626175273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15740270359600114168233697 11805202769700085626175273)
        ·
          refine ⟨8853902077275064219631455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11805202769700085626175273 8853902077275064219631455)
          ·
            refine ⟨13280853115912596329447183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8853902077275064219631455 13280853115912596329447183)
            ·
              refine ⟨19921279673868894494170775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13280853115912596329447183 19921279673868894494170775)
              ·
                refine ⟨29881919510803341741256163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19921279673868894494170775 29881919510803341741256163)
                ·
                  refine ⟨44822879266205012611884245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29881919510803341741256163 44822879266205012611884245)
                  ·
                    refine ⟨1050536232801679983091037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44822879266205012611884245 1050536232801679983091037)
                    ·
                      refine ⟨393951087300629993659139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1050536232801679983091037 393951087300629993659139)
                      ·
                        rfl

theorem cell23_767217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_767217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767217 prefixEnd_767217 := by exact prefixLift 767217
  have htrace : WordTrace (prefixWord ++ tailWord_767217) baseStart_767217 baseEnd_767217 := by
    simpa [prefixWord, tailWord_767217, baseEnd_767217] using wordTrace_append hprefix tailTrace_767217
  have hstable : (prefixWord ++ tailWord_767217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767217).length < 2 ^ (prefixWord ++ tailWord_767217).sum := by decide
  have hdescent : baseEnd_767217 < baseStart_767217 := by decide
  rcases family_descends (prefixWord ++ tailWord_767217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767327 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 4, 7]
def baseStart_767327 : Nat := 118140960795 + 767327 * 2 ^ 59
def prefixEnd_767327 : Nat := 4983230072969 + 3 ^ 40 * 767327 * 2
def baseEnd_767327 : Nat := 131335856724208187761211

theorem tailTrace_767327 : CollatzResearch.WordTrace tailWord_767327 prefixEnd_767327 131335856724208187761211 := by
  unfold tailWord_767327
  simp only [CollatzResearch.WordTrace]
  refine ⟨27986714891112802863364235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18657809927408535242242823 27986714891112802863364235)
  ·
    refine ⟨41980072336669204295046353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27986714891112802863364235 41980072336669204295046353)
    ·
      refine ⟨31485054252501903221284765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41980072336669204295046353 31485054252501903221284765)
      ·
        refine ⟨11806895344688213707981787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31485054252501903221284765 11806895344688213707981787)
        ·
          refine ⟨17710343017032320561972681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11806895344688213707981787 17710343017032320561972681)
          ·
            refine ⟨13282757262774240421479511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17710343017032320561972681 13282757262774240421479511)
            ·
              refine ⟨19924135894161360632219267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13282757262774240421479511 19924135894161360632219267)
              ·
                refine ⟨29886203841242040948328901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19924135894161360632219267 29886203841242040948328901)
                ·
                  refine ⟨5603663220232882677811669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29886203841242040948328901 5603663220232882677811669)
                  ·
                    refine ⟨131335856724208187761211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5603663220232882677811669 131335856724208187761211)
                    ·
                      rfl

theorem cell23_767327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_767327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767327 prefixEnd_767327 := by exact prefixLift 767327
  have htrace : WordTrace (prefixWord ++ tailWord_767327) baseStart_767327 baseEnd_767327 := by
    simpa [prefixWord, tailWord_767327, baseEnd_767327] using wordTrace_append hprefix tailTrace_767327
  have hstable : (prefixWord ++ tailWord_767327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767327).length < 2 ^ (prefixWord ++ tailWord_767327).sum := by decide
  have hdescent : baseEnd_767327 < baseStart_767327 := by decide
  rcases family_descends (prefixWord ++ tailWord_767327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767341 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_767341 : Nat := 118140960795 + 767341 * 2 ^ 59
def prefixEnd_767341 : Nat := 4983230072969 + 3 ^ 40 * 767341 * 2
def baseEnd_767341 : Nat := 394014758901787508508569

theorem tailTrace_767341 : CollatzResearch.WordTrace tailWord_767341 prefixEnd_767341 394014758901787508508569 := by
  unfold tailWord_767341
  simp only [CollatzResearch.WordTrace]
  refine ⟨27987225513062083254373877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18658150342041388836249251 27987225513062083254373877)
  ·
    refine ⟨2623802391849570305097551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27987225513062083254373877 2623802391849570305097551)
    ·
      refine ⟨3935703587774355457646327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2623802391849570305097551 3935703587774355457646327)
      ·
        refine ⟨5903555381661533186469491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3935703587774355457646327 5903555381661533186469491)
        ·
          refine ⟨8855333072492299779704237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5903555381661533186469491 8855333072492299779704237)
          ·
            refine ⟨3320749902184612417389089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8855333072492299779704237 3320749902184612417389089)
            ·
              refine ⟨2490562426638459313041817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3320749902184612417389089 2490562426638459313041817)
              ·
                refine ⟨1867921819978844484781363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2490562426638459313041817 1867921819978844484781363)
                ·
                  refine ⟨2801882729968266727172045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1867921819978844484781363 2801882729968266727172045)
                  ·
                    refine ⟨1050706023738100022689517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2801882729968266727172045 1050706023738100022689517)
                    ·
                      refine ⟨394014758901787508508569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1050706023738100022689517 394014758901787508508569)
                      ·
                        rfl

theorem cell23_767341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_767341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767341 prefixEnd_767341 := by exact prefixLift 767341
  have htrace : WordTrace (prefixWord ++ tailWord_767341) baseStart_767341 baseEnd_767341 := by
    simpa [prefixWord, tailWord_767341, baseEnd_767341] using wordTrace_append hprefix tailTrace_767341
  have hstable : (prefixWord ++ tailWord_767341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767341).length < 2 ^ (prefixWord ++ tailWord_767341).sum := by decide
  have hdescent : baseEnd_767341 < baseStart_767341 := by decide
  rcases family_descends (prefixWord ++ tailWord_767341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767342 : List Nat := [4, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_767342 : Nat := 118140960795 + 767342 * 2 ^ 59
def prefixEnd_767342 : Nat := 4983230072969 + 3 ^ 40 * 767342 * 2
def baseEnd_767342 : Nat := 394015272382442004596065

theorem tailTrace_767342 : CollatzResearch.WordTrace tailWord_767342 prefixEnd_767342 394015272382442004596065 := by
  unfold tailWord_767342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3498407748257307553145035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18658174657372306950106853 3498407748257307553145035)
  ·
    refine ⟨5247611622385961329717553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3498407748257307553145035 5247611622385961329717553)
    ·
      refine ⟨3935708716789470997288165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5247611622385961329717553 3935708716789470997288165)
      ·
        refine ⟨737945384398025811991531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3935708716789470997288165 737945384398025811991531)
        ·
          refine ⟨1106918076597038717987297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737945384398025811991531 1106918076597038717987297)
          ·
            refine ⟨830188557447779038490473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1106918076597038717987297 830188557447779038490473)
            ·
              refine ⟨622641418085834278867855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830188557447779038490473 622641418085834278867855)
              ·
                refine ⟨933962127128751418301783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 622641418085834278867855 933962127128751418301783)
                ·
                  refine ⟨1400943190693127127452675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 933962127128751418301783 1400943190693127127452675)
                  ·
                    refine ⟨2101414786039690691179013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1400943190693127127452675 2101414786039690691179013)
                    ·
                      refine ⟨394015272382442004596065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2101414786039690691179013 394015272382442004596065)
                      ·
                        rfl

theorem cell23_767342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_767342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767342 prefixEnd_767342 := by exact prefixLift 767342
  have htrace : WordTrace (prefixWord ++ tailWord_767342) baseStart_767342 baseEnd_767342 := by
    simpa [prefixWord, tailWord_767342, baseEnd_767342] using wordTrace_append hprefix tailTrace_767342
  have hstable : (prefixWord ++ tailWord_767342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767342).length < 2 ^ (prefixWord ++ tailWord_767342).sum := by decide
  have hdescent : baseEnd_767342 < baseStart_767342 := by decide
  rcases family_descends (prefixWord ++ tailWord_767342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767426 : List Nat := [3, 5, 2, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_767426 : Nat := 118140960795 + 767426 * 2 ^ 59
def prefixEnd_767426 : Nat := 4983230072969 + 3 ^ 40 * 767426 * 2
def baseEnd_767426 : Nat := 394058404757419675945679

theorem tailTrace_767426 : CollatzResearch.WordTrace tailWord_767426 prefixEnd_767426 394058404757419675945679 := by
  unfold tailWord_767426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6997581429438535692804533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18660217145169428514145421 6997581429438535692804533)
  ·
    refine ⟨656023259009862721200425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6997581429438535692804533 656023259009862721200425)
    ·
      refine ⟨492017444257397040900319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 656023259009862721200425 492017444257397040900319)
      ·
        refine ⟨738026166386095561350479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492017444257397040900319 738026166386095561350479)
        ·
          refine ⟨1107039249579143342025719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738026166386095561350479 1107039249579143342025719)
          ·
            refine ⟨1660558874368715013038579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107039249579143342025719 1660558874368715013038579)
            ·
              refine ⟨2490838311553072519557869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660558874368715013038579 2490838311553072519557869)
              ·
                refine ⟨934064366832402194834201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2490838311553072519557869 934064366832402194834201)
                ·
                  refine ⟨700548275124301646125651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 934064366832402194834201 700548275124301646125651)
                  ·
                    refine ⟨1050822412686452469188477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 700548275124301646125651 1050822412686452469188477)
                    ·
                      refine ⟨394058404757419675945679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1050822412686452469188477 394058404757419675945679)
                      ·
                        rfl

theorem cell23_767426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_767426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767426 prefixEnd_767426 := by exact prefixLift 767426
  have htrace : WordTrace (prefixWord ++ tailWord_767426) baseStart_767426 baseEnd_767426 := by
    simpa [prefixWord, tailWord_767426, baseEnd_767426] using wordTrace_append hprefix tailTrace_767426
  have hstable : (prefixWord ++ tailWord_767426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767426).length < 2 ^ (prefixWord ++ tailWord_767426).sum := by decide
  have hdescent : baseEnd_767426 < baseStart_767426 := by decide
  rcases family_descends (prefixWord ++ tailWord_767426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767461 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_767461 : Nat := 118140960795 + 767461 * 2 ^ 59
def prefixEnd_767461 : Nat := 4983230072969 + 3 ^ 40 * 767461 * 2
def baseEnd_767461 : Nat := 394076376580327039008017

theorem tailTrace_767461 : CollatzResearch.WordTrace tailWord_767461 prefixEnd_767461 394076376580327039008017 := by
  unfold tailWord_767461
  simp only [CollatzResearch.WordTrace]
  refine ⟨27991602272627343748742237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18661068181751562499161491 27991602272627343748742237)
  ·
    refine ⟨10496850852235253905778339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27991602272627343748742237 10496850852235253905778339)
    ·
      refine ⟨15745276278352880858667509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10496850852235253905778339 15745276278352880858667509)
      ·
        refine ⟨1476119651095582580500079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15745276278352880858667509 1476119651095582580500079)
        ·
          refine ⟨2214179476643373870750119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476119651095582580500079 2214179476643373870750119)
          ·
            refine ⟨3321269214965060806125179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214179476643373870750119 3321269214965060806125179)
            ·
              refine ⟨4981903822447591209187769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321269214965060806125179 4981903822447591209187769)
              ·
                refine ⟨3736427866835693406890827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4981903822447591209187769 3736427866835693406890827)
                ·
                  refine ⟨5604641800253540110336241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736427866835693406890827 5604641800253540110336241)
                  ·
                    refine ⟨4203481350190155082752181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5604641800253540110336241 4203481350190155082752181)
                    ·
                      refine ⟨394076376580327039008017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4203481350190155082752181 394076376580327039008017)
                      ·
                        rfl

theorem cell23_767461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_767461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767461 prefixEnd_767461 := by exact prefixLift 767461
  have htrace : WordTrace (prefixWord ++ tailWord_767461) baseStart_767461 baseEnd_767461 := by
    simpa [prefixWord, tailWord_767461, baseEnd_767461] using wordTrace_append hprefix tailTrace_767461
  have hstable : (prefixWord ++ tailWord_767461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767461).length < 2 ^ (prefixWord ++ tailWord_767461).sum := by decide
  have hdescent : baseEnd_767461 < baseStart_767461 := by decide
  rcases family_descends (prefixWord ++ tailWord_767461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767471 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 4]
def baseStart_767471 : Nat := 118140960795 + 767471 * 2 ^ 59
def prefixEnd_767471 : Nat := 4983230072969 + 3 ^ 40 * 767471 * 2
def baseEnd_767471 : Nat := 394081511386871999882971

theorem tailTrace_767471 : CollatzResearch.WordTrace tailWord_767471 prefixEnd_767471 394081511386871999882971 := by
  unfold tailWord_767471
  simp only [CollatzResearch.WordTrace]
  refine ⟨27991967002591115456606267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18661311335060743637737511 27991967002591115456606267)
  ·
    refine ⟨41987950503886673184909401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27991967002591115456606267 41987950503886673184909401)
    ·
      refine ⟨31490962877915004888682051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41987950503886673184909401 31490962877915004888682051)
      ·
        refine ⟨47236444316872507333023077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31490962877915004888682051 47236444316872507333023077)
        ·
          refine ⟨8856833309413595124941827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47236444316872507333023077 8856833309413595124941827)
          ·
            refine ⟨13285249964120392687412741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8856833309413595124941827 13285249964120392687412741)
            ·
              refine ⟨2490984368272573628889889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13285249964120392687412741 2490984368272573628889889)
              ·
                refine ⟨1868238276204430221667417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2490984368272573628889889 1868238276204430221667417)
                ·
                  refine ⟨1401178707153322666250563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1868238276204430221667417 1401178707153322666250563)
                  ·
                    refine ⟨2101768060729983999375845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1401178707153322666250563 2101768060729983999375845)
                    ·
                      refine ⟨394081511386871999882971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2101768060729983999375845 394081511386871999882971)
                      ·
                        rfl

theorem cell23_767471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_767471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767471 prefixEnd_767471 := by exact prefixLift 767471
  have htrace : WordTrace (prefixWord ++ tailWord_767471) baseStart_767471 baseEnd_767471 := by
    simpa [prefixWord, tailWord_767471, baseEnd_767471] using wordTrace_append hprefix tailTrace_767471
  have hstable : (prefixWord ++ tailWord_767471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767471).length < 2 ^ (prefixWord ++ tailWord_767471).sum := by decide
  have hdescent : baseEnd_767471 < baseStart_767471 := by decide
  rcases family_descends (prefixWord ++ tailWord_767471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767481 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 3, 4]
def baseStart_767481 : Nat := 118140960795 + 767481 * 2 ^ 59
def prefixEnd_767481 : Nat := 4983230072969 + 3 ^ 40 * 767481 * 2
def baseEnd_767481 : Nat := 131362215397805653585975

theorem tailTrace_767481 : CollatzResearch.WordTrace tailWord_767481 prefixEnd_767481 131362215397805653585975 := by
  unfold tailWord_767481
  simp only [CollatzResearch.WordTrace]
  refine ⟨27992331732554887164470297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18661554488369924776313531 27992331732554887164470297)
  ·
    refine ⟨20994248799416165373352723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27992331732554887164470297 20994248799416165373352723)
    ·
      refine ⟨31491373199124248060029085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20994248799416165373352723 31491373199124248060029085)
      ·
        refine ⟨11809264949671593022510907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31491373199124248060029085 11809264949671593022510907)
        ·
          refine ⟨17713897424507389533766361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11809264949671593022510907 17713897424507389533766361)
          ·
            refine ⟨13285423068380542150324771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17713897424507389533766361 13285423068380542150324771)
            ·
              refine ⟨19928134602570813225487157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13285423068380542150324771 19928134602570813225487157)
              ·
                refine ⟨1868262618991013739889421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19928134602570813225487157 1868262618991013739889421)
                ·
                  refine ⟨700598482121630152458533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1868262618991013739889421 700598482121630152458533)
                  ·
                    refine ⟨131362215397805653585975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 700598482121630152458533 131362215397805653585975)
                    ·
                      rfl

theorem cell23_767481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 4].length) (baseStart_767481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767481 prefixEnd_767481 := by exact prefixLift 767481
  have htrace : WordTrace (prefixWord ++ tailWord_767481) baseStart_767481 baseEnd_767481 := by
    simpa [prefixWord, tailWord_767481, baseEnd_767481] using wordTrace_append hprefix tailTrace_767481
  have hstable : (prefixWord ++ tailWord_767481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767481).length < 2 ^ (prefixWord ++ tailWord_767481).sum := by decide
  have hdescent : baseEnd_767481 < baseStart_767481 := by decide
  rcases family_descends (prefixWord ++ tailWord_767481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767498 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 3, 4]
def baseStart_767498 : Nat := 118140960795 + 767498 * 2 ^ 59
def prefixEnd_767498 : Nat := 4983230072969 + 3 ^ 40 * 767498 * 2
def baseEnd_767498 : Nat := 131365125121514464748449

theorem tailTrace_767498 : CollatzResearch.WordTrace tailWord_767498 prefixEnd_767498 131365125121514464748449 := by
  unfold tailWord_767498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6998237943373324766959787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18661967848995532711892765 6998237943373324766959787)
  ·
    refine ⟨10497356915059987150439681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6998237943373324766959787 10497356915059987150439681)
    ·
      refine ⟨7873017686294990362829761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10497356915059987150439681 7873017686294990362829761)
      ·
        refine ⟨5904763264721242772122321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7873017686294990362829761 5904763264721242772122321)
        ·
          refine ⟨4428572448540932079091741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5904763264721242772122321 4428572448540932079091741)
          ·
            refine ⟨1660714668202849529659403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4428572448540932079091741 1660714668202849529659403)
            ·
              refine ⟨2491072002304274294489105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660714668202849529659403 2491072002304274294489105)
              ·
                refine ⟨1868304001728205720866829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2491072002304274294489105 1868304001728205720866829)
                ·
                  refine ⟨700614000648077145325061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1868304001728205720866829 700614000648077145325061)
                  ·
                    refine ⟨131365125121514464748449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 700614000648077145325061 131365125121514464748449)
                    ·
                      rfl

theorem cell23_767498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_767498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767498 prefixEnd_767498 := by exact prefixLift 767498
  have htrace : WordTrace (prefixWord ++ tailWord_767498) baseStart_767498 baseEnd_767498 := by
    simpa [prefixWord, tailWord_767498, baseEnd_767498] using wordTrace_append hprefix tailTrace_767498
  have hstable : (prefixWord ++ tailWord_767498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767498).length < 2 ^ (prefixWord ++ tailWord_767498).sum := by decide
  have hdescent : baseEnd_767498 < baseStart_767498 := by decide
  rcases family_descends (prefixWord ++ tailWord_767498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767528 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 8]
def baseStart_767528 : Nat := 118140960795 + 767528 * 2 ^ 59
def prefixEnd_767528 : Nat := 4983230072969 + 3 ^ 40 * 767528 * 2
def baseEnd_767528 : Nat := 43790086642686475207801

theorem tailTrace_767528 : CollatzResearch.WordTrace tailWord_767528 prefixEnd_767528 43790086642686475207801 := by
  unfold tailWord_767528
  simp only [CollatzResearch.WordTrace]
  refine ⟨13997022981692307095715619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18662697308923076127620825 13997022981692307095715619)
  ·
    refine ⟨20995534472538460643573429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13997022981692307095715619 20995534472538460643573429)
    ·
      refine ⟨1968331356800480685335009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20995534472538460643573429 1968331356800480685335009)
      ·
        refine ⟨1476248517600360514001257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1968331356800480685335009 1476248517600360514001257)
        ·
          refine ⟨1107186388200270385500943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1476248517600360514001257 1107186388200270385500943)
          ·
            refine ⟨1660779582300405578251415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107186388200270385500943 1660779582300405578251415)
            ·
              refine ⟨2491169373450608367377123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660779582300405578251415 2491169373450608367377123)
              ·
                refine ⟨3736754060175912551065685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491169373450608367377123 3736754060175912551065685)
                ·
                  refine ⟨43790086642686475207801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3736754060175912551065685 43790086642686475207801)
                  ·
                    rfl

theorem cell23_767528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 8].length) (baseStart_767528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767528 prefixEnd_767528 := by exact prefixLift 767528
  have htrace : WordTrace (prefixWord ++ tailWord_767528) baseStart_767528 baseEnd_767528 := by
    simpa [prefixWord, tailWord_767528, baseEnd_767528] using wordTrace_append hprefix tailTrace_767528
  have hstable : (prefixWord ++ tailWord_767528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767528).length < 2 ^ (prefixWord ++ tailWord_767528).sum := by decide
  have hdescent : baseEnd_767528 < baseStart_767528 := by decide
  rcases family_descends (prefixWord ++ tailWord_767528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767561 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 3, 1, 4]
def baseStart_767561 : Nat := 118140960795 + 767561 * 2 ^ 59
def prefixEnd_767561 : Nat := 4983230072969 + 3 ^ 40 * 767561 * 2
def baseEnd_767561 : Nat := 394127724645776647757557

theorem tailTrace_767561 : CollatzResearch.WordTrace tailWord_767561 prefixEnd_767561 394127724645776647757557 := by
  unfold tailWord_767561
  simp only [CollatzResearch.WordTrace]
  refine ⟨27995249572265060827382537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18663499714843373884921691 27995249572265060827382537)
  ·
    refine ⟨20996437179198795620536903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27995249572265060827382537 20996437179198795620536903)
    ·
      refine ⟨31494655768798193430805355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20996437179198795620536903 31494655768798193430805355)
      ·
        refine ⟨47241983653197290146208033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31494655768798193430805355 47241983653197290146208033)
        ·
          refine ⟨35431487739897967609656025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47241983653197290146208033 35431487739897967609656025)
          ·
            refine ⟨26573615804923475707242019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35431487739897967609656025 26573615804923475707242019)
            ·
              refine ⟨39860423707385213560863029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26573615804923475707242019 39860423707385213560863029)
              ·
                refine ⟨3736914722567363771330909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39860423707385213560863029 3736914722567363771330909)
                ·
                  refine ⟨1401343020962761414249091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3736914722567363771330909 1401343020962761414249091)
                  ·
                    refine ⟨2102014531444142121373637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1401343020962761414249091 2102014531444142121373637)
                    ·
                      refine ⟨394127724645776647757557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2102014531444142121373637 394127724645776647757557)
                      ·
                        rfl

theorem cell23_767561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_767561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767561 prefixEnd_767561 := by exact prefixLift 767561
  have htrace : WordTrace (prefixWord ++ tailWord_767561) baseStart_767561 baseEnd_767561 := by
    simpa [prefixWord, tailWord_767561, baseEnd_767561] using wordTrace_append hprefix tailTrace_767561
  have hstable : (prefixWord ++ tailWord_767561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767561).length < 2 ^ (prefixWord ++ tailWord_767561).sum := by decide
  have hdescent : baseEnd_767561 < baseStart_767561 := by decide
  rcases family_descends (prefixWord ++ tailWord_767561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767588 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_767588 : Nat := 118140960795 + 767588 * 2 ^ 59
def prefixEnd_767588 : Nat := 4983230072969 + 3 ^ 40 * 767588 * 2
def baseEnd_767588 : Nat := 131380529541149347373311

theorem tailTrace_767588 : CollatzResearch.WordTrace tailWord_767588 prefixEnd_767588 131380529541149347373311 := by
  unfold tailWord_767588
  simp only [CollatzResearch.WordTrace]
  refine ⟨13998117171583622219307709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18664156228778162959076945 13998117171583622219307709)
  ·
    refine ⟨5249293939343858332240391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13998117171583622219307709 5249293939343858332240391)
    ·
      refine ⟨7873940909015787498360587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5249293939343858332240391 7873940909015787498360587)
      ·
        refine ⟨11810911363523681247540881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7873940909015787498360587 11810911363523681247540881)
        ·
          refine ⟨8858183522642760935655661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11810911363523681247540881 8858183522642760935655661)
          ·
            refine ⟨3321818820991035350870873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8858183522642760935655661 3321818820991035350870873)
            ·
              refine ⟨2491364115743276513153155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3321818820991035350870873 2491364115743276513153155)
              ·
                refine ⟨3737046173614914769729733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491364115743276513153155 3737046173614914769729733)
                ·
                  refine ⟨700696157552796519324325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3737046173614914769729733 700696157552796519324325)
                  ·
                    refine ⟨131380529541149347373311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 700696157552796519324325 131380529541149347373311)
                    ·
                      rfl

theorem cell23_767588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_767588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767588 prefixEnd_767588 := by exact prefixLift 767588
  have htrace : WordTrace (prefixWord ++ tailWord_767588) baseStart_767588 baseEnd_767588 := by
    simpa [prefixWord, tailWord_767588, baseEnd_767588] using wordTrace_append hprefix tailTrace_767588
  have hstable : (prefixWord ++ tailWord_767588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767588).length < 2 ^ (prefixWord ++ tailWord_767588).sum := by decide
  have hdescent : baseEnd_767588 < baseStart_767588 := by decide
  rcases family_descends (prefixWord ++ tailWord_767588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767589 : List Nat := [1, 3, 1, 3, 3, 2, 3, 2, 1, 1, 3]
def baseStart_767589 : Nat := 118140960795 + 767589 * 2 ^ 59
def prefixEnd_767589 : Nat := 4983230072969 + 3 ^ 40 * 767589 * 2
def baseEnd_767589 : Nat := 394142102104102538207429

theorem tailTrace_767589 : CollatzResearch.WordTrace tailWord_767589 prefixEnd_767589 394142102104102538207429 := by
  unfold tailWord_767589
  simp only [CollatzResearch.WordTrace]
  refine ⟨27996270816163621609401821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18664180544109081072934547 27996270816163621609401821)
  ·
    refine ⟨10498601556061358103525683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27996270816163621609401821 10498601556061358103525683)
    ·
      refine ⟨15747902334092037155288525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10498601556061358103525683 15747902334092037155288525)
      ·
        refine ⟨5905463375284513933233197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15747902334092037155288525 5905463375284513933233197)
        ·
          refine ⟨2214548765731692724962449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5905463375284513933233197 2214548765731692724962449)
          ·
            refine ⟨1660911574298769543721837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2214548765731692724962449 1660911574298769543721837)
            ·
              refine ⟨622841840362038578895689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1660911574298769543721837 622841840362038578895689)
              ·
                refine ⟨467131380271528934171767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622841840362038578895689 467131380271528934171767)
                ·
                  refine ⟨700697070407293401257651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 467131380271528934171767 700697070407293401257651)
                  ·
                    refine ⟨1051045605610940101886477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 700697070407293401257651 1051045605610940101886477)
                    ·
                      refine ⟨394142102104102538207429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1051045605610940101886477 394142102104102538207429)
                      ·
                        rfl

theorem cell23_767589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_767589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767589 prefixEnd_767589 := by exact prefixLift 767589
  have htrace : WordTrace (prefixWord ++ tailWord_767589) baseStart_767589 baseEnd_767589 := by
    simpa [prefixWord, tailWord_767589, baseEnd_767589] using wordTrace_append hprefix tailTrace_767589
  have hstable : (prefixWord ++ tailWord_767589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767589).length < 2 ^ (prefixWord ++ tailWord_767589).sum := by decide
  have hdescent : baseEnd_767589 < baseStart_767589 := by decide
  rcases family_descends (prefixWord ++ tailWord_767589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767591 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_767591 : Nat := 118140960795 + 767591 * 2 ^ 59
def prefixEnd_767591 : Nat := 4983230072969 + 3 ^ 40 * 767591 * 2
def baseEnd_767591 : Nat := 394143129065411530382419

theorem tailTrace_767591 : CollatzResearch.WordTrace tailWord_767591 prefixEnd_767591 394143129065411530382419 := by
  unfold tailWord_767591
  simp only [CollatzResearch.WordTrace]
  refine ⟨27996343762156375950974627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18664229174770917300649751 27996343762156375950974627)
  ·
    refine ⟨41994515643234563926461941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27996343762156375950974627 41994515643234563926461941)
    ·
      refine ⟨3936985841553240368105807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41994515643234563926461941 3936985841553240368105807)
      ·
        refine ⟨5905478762329860552158711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3936985841553240368105807 5905478762329860552158711)
        ·
          refine ⟨8858218143494790828238067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5905478762329860552158711 8858218143494790828238067)
          ·
            refine ⟨13287327215242186242357101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8858218143494790828238067 13287327215242186242357101)
            ·
              refine ⟨4982747705715819840883913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13287327215242186242357101 4982747705715819840883913)
              ·
                refine ⟨3737060779286864880662935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4982747705715819840883913 3737060779286864880662935)
                ·
                  refine ⟨5605591168930297320994403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3737060779286864880662935 5605591168930297320994403)
                  ·
                    refine ⟨8408386753395445981491605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5605591168930297320994403 8408386753395445981491605)
                    ·
                      refine ⟨394143129065411530382419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8408386753395445981491605 394143129065411530382419)
                      ·
                        rfl

theorem cell23_767591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_767591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767591 prefixEnd_767591 := by exact prefixLift 767591
  have htrace : WordTrace (prefixWord ++ tailWord_767591) baseStart_767591 baseEnd_767591 := by
    simpa [prefixWord, tailWord_767591, baseEnd_767591] using wordTrace_append hprefix tailTrace_767591
  have hstable : (prefixWord ++ tailWord_767591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767591).length < 2 ^ (prefixWord ++ tailWord_767591).sum := by decide
  have hdescent : baseEnd_767591 < baseStart_767591 := by decide
  rcases family_descends (prefixWord ++ tailWord_767591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767628 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 1, 3, 3]
def baseStart_767628 : Nat := 118140960795 + 767628 * 2 ^ 59
def prefixEnd_767628 : Nat := 4983230072969 + 3 ^ 40 * 767628 * 2
def baseEnd_767628 : Nat := 394162127849627885619749

theorem tailTrace_767628 : CollatzResearch.WordTrace tailWord_767628 prefixEnd_767628 394162127849627885619749 := by
  unfold tailWord_767628
  simp only [CollatzResearch.WordTrace]
  refine ⟨13998846631511165635035769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18665128842014887513381025 13998846631511165635035769)
  ·
    refine ⟨10499134973633374226276827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13998846631511165635035769 10499134973633374226276827)
    ·
      refine ⟨15748702460450061339415241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10499134973633374226276827 15748702460450061339415241)
      ·
        refine ⟨11811526845337546004561431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15748702460450061339415241 11811526845337546004561431)
        ·
          refine ⟨17717290268006319006842147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11811526845337546004561431 17717290268006319006842147)
          ·
            refine ⟨26575935402009478510263221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17717290268006319006842147 26575935402009478510263221)
            ·
              refine ⟨2491493943938388610337177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26575935402009478510263221 2491493943938388610337177)
              ·
                refine ⟨1868620457953791457752883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2491493943938388610337177 1868620457953791457752883)
                ·
                  refine ⟨2802930686930687186629325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1868620457953791457752883 2802930686930687186629325)
                  ·
                    refine ⟨1051099007599007694985997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2802930686930687186629325 1051099007599007694985997)
                    ·
                      refine ⟨394162127849627885619749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1051099007599007694985997 394162127849627885619749)
                      ·
                        rfl

theorem cell23_767628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_767628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767628 prefixEnd_767628 := by exact prefixLift 767628
  have htrace : WordTrace (prefixWord ++ tailWord_767628) baseStart_767628 baseEnd_767628 := by
    simpa [prefixWord, tailWord_767628, baseEnd_767628] using wordTrace_append hprefix tailTrace_767628
  have hstable : (prefixWord ++ tailWord_767628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767628).length < 2 ^ (prefixWord ++ tailWord_767628).sum := by decide
  have hdescent : baseEnd_767628 < baseStart_767628 := by decide
  rcases family_descends (prefixWord ++ tailWord_767628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767646 : List Nat := [4, 3, 1, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_767646 : Nat := 118140960795 + 767646 * 2 ^ 59
def prefixEnd_767646 : Nat := 4983230072969 + 3 ^ 40 * 767646 * 2
def baseEnd_767646 : Nat := 394171370501408815194667

theorem tailTrace_767646 : CollatzResearch.WordTrace tailWord_767646 prefixEnd_767646 394171370501408815194667 := by
  unfold tailWord_767646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3499793722119640043028349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18665566517971413562817861 3499793722119640043028349)
  ·
    refine ⟨1312422645794865016135631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3499793722119640043028349 1312422645794865016135631)
    ·
      refine ⟨1968633968692297524203447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1312422645794865016135631 1968633968692297524203447)
      ·
        refine ⟨2952950953038446286305171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968633968692297524203447 2952950953038446286305171)
        ·
          refine ⟨4429426429557669429457757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952950953038446286305171 4429426429557669429457757)
          ·
            refine ⟨1661034911084126036046659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4429426429557669429457757 1661034911084126036046659)
            ·
              refine ⟨2491552366626189054069989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1661034911084126036046659 2491552366626189054069989)
              ·
                refine ⟨467166068742410447638123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2491552366626189054069989 467166068742410447638123)
                ·
                  refine ⟨700749103113615671457185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 467166068742410447638123 700749103113615671457185)
                  ·
                    refine ⟨525561827335211753592889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 700749103113615671457185 525561827335211753592889)
                    ·
                      refine ⟨394171370501408815194667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 525561827335211753592889 394171370501408815194667)
                      ·
                        rfl

theorem cell23_767646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_767646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767646 prefixEnd_767646 := by exact prefixLift 767646
  have htrace : WordTrace (prefixWord ++ tailWord_767646) baseStart_767646 baseEnd_767646 := by
    simpa [prefixWord, tailWord_767646, baseEnd_767646] using wordTrace_append hprefix tailTrace_767646
  have hstable : (prefixWord ++ tailWord_767646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767646).length < 2 ^ (prefixWord ++ tailWord_767646).sum := by decide
  have hdescent : baseEnd_767646 < baseStart_767646 := by decide
  rcases family_descends (prefixWord ++ tailWord_767646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767651 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 4]
def baseStart_767651 : Nat := 118140960795 + 767651 * 2 ^ 59
def prefixEnd_767651 : Nat := 4983230072969 + 3 ^ 40 * 767651 * 2
def baseEnd_767651 : Nat := 394173937904681295632143

theorem tailTrace_767651 : CollatzResearch.WordTrace tailWord_767651 prefixEnd_767651 394173937904681295632143 := by
  unfold tailWord_767651
  simp only [CollatzResearch.WordTrace]
  refine ⟨27998532141939006198158807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18665688094626004132105871 27998532141939006198158807)
  ·
    refine ⟨41997798212908509297238211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27998532141939006198158807 41997798212908509297238211)
    ·
      refine ⟨62996697319362763945857317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41997798212908509297238211 62996697319362763945857317)
      ·
        refine ⟨11811880747380518239848247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62996697319362763945857317 11811880747380518239848247)
        ·
          refine ⟨17717821121070777359772371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11811880747380518239848247 17717821121070777359772371)
          ·
            refine ⟨26576731681606166039658557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17717821121070777359772371 26576731681606166039658557)
            ·
              refine ⟨9966274380602312264871959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26576731681606166039658557 9966274380602312264871959)
              ·
                refine ⟨14949411570903468397307939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9966274380602312264871959 14949411570903468397307939)
                ·
                  refine ⟨22424117356355202595961909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14949411570903468397307939 22424117356355202595961909)
                  ·
                    refine ⟨2102261002158300243371429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22424117356355202595961909 2102261002158300243371429)
                    ·
                      refine ⟨394173937904681295632143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2102261002158300243371429 394173937904681295632143)
                      ·
                        rfl

theorem cell23_767651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_767651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767651 prefixEnd_767651 := by exact prefixLift 767651
  have htrace : WordTrace (prefixWord ++ tailWord_767651) baseStart_767651 baseEnd_767651 := by
    simpa [prefixWord, tailWord_767651, baseEnd_767651] using wordTrace_append hprefix tailTrace_767651
  have hstable : (prefixWord ++ tailWord_767651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767651).length < 2 ^ (prefixWord ++ tailWord_767651).sum := by decide
  have hdescent : baseEnd_767651 < baseStart_767651 := by decide
  rcases family_descends (prefixWord ++ tailWord_767651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767685 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 6, 2, 2]
def baseStart_767685 : Nat := 118140960795 + 767685 * 2 ^ 59
def prefixEnd_767685 : Nat := 4983230072969 + 3 ^ 40 * 767685 * 2
def baseEnd_767685 : Nat := 394191396246934162606987

theorem tailTrace_767685 : CollatzResearch.WordTrace tailWord_767685 prefixEnd_767685 394191396246934162606987 := by
  unfold tailWord_767685
  simp only [CollatzResearch.WordTrace]
  refine ⟨27999772223815830004896509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18666514815877220003264339 27999772223815830004896509)
  ·
    refine ⟨10499914583930936251836191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27999772223815830004896509 10499914583930936251836191)
    ·
      refine ⟨15749871875896404377754287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10499914583930936251836191 15749871875896404377754287)
      ·
        refine ⟨23624807813844606566631431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15749871875896404377754287 23624807813844606566631431)
        ·
          refine ⟨35437211720766909849947147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23624807813844606566631431 35437211720766909849947147)
          ·
            refine ⟨53155817581150364774920721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35437211720766909849947147 53155817581150364774920721)
            ·
              refine ⟨39866863185862773581190541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53155817581150364774920721 39866863185862773581190541)
              ·
                refine ⟨14950073694698540092946453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39866863185862773581190541 14950073694698540092946453)
                ·
                  refine ⟨700784704438994066856865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14950073694698540092946453 700784704438994066856865)
                  ·
                    refine ⟨525588528329245550142649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 700784704438994066856865 525588528329245550142649)
                    ·
                      refine ⟨394191396246934162606987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 525588528329245550142649 394191396246934162606987)
                      ·
                        rfl

theorem cell23_767685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 2, 2].length) (baseStart_767685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767685 prefixEnd_767685 := by exact prefixLift 767685
  have htrace : WordTrace (prefixWord ++ tailWord_767685) baseStart_767685 baseEnd_767685 := by
    simpa [prefixWord, tailWord_767685, baseEnd_767685] using wordTrace_append hprefix tailTrace_767685
  have hstable : (prefixWord ++ tailWord_767685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767685).length < 2 ^ (prefixWord ++ tailWord_767685).sum := by decide
  have hdescent : baseEnd_767685 < baseStart_767685 := by decide
  rcases family_descends (prefixWord ++ tailWord_767685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767738 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 2, 5]
def baseStart_767738 : Nat := 118140960795 + 767738 * 2 ^ 59
def prefixEnd_767738 : Nat := 4983230072969 + 3 ^ 40 * 767738 * 2
def baseEnd_767738 : Nat := 131406203573874151748081

theorem tailTrace_767738 : CollatzResearch.WordTrace tailWord_767738 prefixEnd_767738 131406203573874151748081 := by
  unfold tailWord_767738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7000426323155955014143967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18667803528415880037717245 7000426323155955014143967)
  ·
    refine ⟨10500639484733932521215951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7000426323155955014143967 10500639484733932521215951)
    ·
      refine ⟨15750959227100898781823927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10500639484733932521215951 15750959227100898781823927)
      ·
        refine ⟨23626438840651348172735891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15750959227100898781823927 23626438840651348172735891)
        ·
          refine ⟨35439658260977022259103837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23626438840651348172735891 35439658260977022259103837)
          ·
            refine ⟨13289871847866383347163939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35439658260977022259103837 13289871847866383347163939)
            ·
              refine ⟨19934807771799575020745909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13289871847866383347163939 19934807771799575020745909)
              ·
                refine ⟨1868888228606210158194929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19934807771799575020745909 1868888228606210158194929)
                ·
                  refine ⟨1401666171454657618646197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1868888228606210158194929 1401666171454657618646197)
                  ·
                    refine ⟨131406203573874151748081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1401666171454657618646197 131406203573874151748081)
                    ·
                      rfl

theorem cell23_767738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_767738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767738 prefixEnd_767738 := by exact prefixLift 767738
  have htrace : WordTrace (prefixWord ++ tailWord_767738) baseStart_767738 baseEnd_767738 := by
    simpa [prefixWord, tailWord_767738, baseEnd_767738] using wordTrace_append hprefix tailTrace_767738
  have hstable : (prefixWord ++ tailWord_767738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767738).length < 2 ^ (prefixWord ++ tailWord_767738).sum := by decide
  have hdescent : baseEnd_767738 < baseStart_767738 := by decide
  rcases family_descends (prefixWord ++ tailWord_767738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767775 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 1, 6, 2]
def baseStart_767775 : Nat := 118140960795 + 767775 * 2 ^ 59
def prefixEnd_767775 : Nat := 4983230072969 + 3 ^ 40 * 767775 * 2
def baseEnd_767775 : Nat := 394237609505838810481573

theorem tailTrace_767775 : CollatzResearch.WordTrace tailWord_767775 prefixEnd_767775 394237609505838810481573 := by
  unfold tailWord_767775
  simp only [CollatzResearch.WordTrace]
  refine ⟨28003054793489775375672779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18668703195659850250448519 28003054793489775375672779)
  ·
    refine ⟨42004582190234663063509169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28003054793489775375672779 42004582190234663063509169)
    ·
      refine ⟨31503436642675997297631877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42004582190234663063509169 31503436642675997297631877)
      ·
        refine ⟨5906894370501749493305977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31503436642675997297631877 5906894370501749493305977)
        ·
          refine ⟨4430170777876312119979483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5906894370501749493305977 4430170777876312119979483)
          ·
            refine ⟨6645256166814468179969225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4430170777876312119979483 6645256166814468179969225)
            ·
              refine ⟨4983942125110851134976919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6645256166814468179969225 4983942125110851134976919)
              ·
                refine ⟨7475913187666276702465379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4983942125110851134976919 7475913187666276702465379)
                ·
                  refine ⟨11213869781499415053698069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7475913187666276702465379 11213869781499415053698069)
                  ·
                    refine ⟨525650146007785080642097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11213869781499415053698069 525650146007785080642097)
                    ·
                      refine ⟨394237609505838810481573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 525650146007785080642097 394237609505838810481573)
                      ·
                        rfl

theorem cell23_767775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_767775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767775 prefixEnd_767775 := by exact prefixLift 767775
  have htrace : WordTrace (prefixWord ++ tailWord_767775) baseStart_767775 baseEnd_767775 := by
    simpa [prefixWord, tailWord_767775, baseEnd_767775] using wordTrace_append hprefix tailTrace_767775
  have hstable : (prefixWord ++ tailWord_767775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767775).length < 2 ^ (prefixWord ++ tailWord_767775).sum := by decide
  have hdescent : baseEnd_767775 < baseStart_767775 := by decide
  rcases family_descends (prefixWord ++ tailWord_767775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767818 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_767818 : Nat := 118140960795 + 767818 * 2 ^ 59
def prefixEnd_767818 : Nat := 4983230072969 + 3 ^ 40 * 767818 * 2
def baseEnd_767818 : Nat := 394259689173982142243875

theorem tailTrace_767818 : CollatzResearch.WordTrace tailWord_767818 prefixEnd_767818 394259689173982142243875 := by
  unfold tailWord_767818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001155783083498429872027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18669748754889329146325405 7001155783083498429872027)
  ·
    refine ⟨10501733674625247644808041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7001155783083498429872027 10501733674625247644808041)
    ·
      refine ⟨7876300255968935733606031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10501733674625247644808041 7876300255968935733606031)
      ·
        refine ⟨11814450383953403600409047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7876300255968935733606031 11814450383953403600409047)
        ·
          refine ⟨17721675575930105400613571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11814450383953403600409047 17721675575930105400613571)
          ·
            refine ⟨26582513363895158100920357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17721675575930105400613571 26582513363895158100920357)
            ·
              refine ⟨4984221255730342143922567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26582513363895158100920357 4984221255730342143922567)
              ·
                refine ⟨7476331883595513215883851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4984221255730342143922567 7476331883595513215883851)
                ·
                  refine ⟨11214497825393269823825777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7476331883595513215883851 11214497825393269823825777)
                  ·
                    refine ⟨8410873369044952367869333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11214497825393269823825777 8410873369044952367869333)
                    ·
                      refine ⟨394259689173982142243875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8410873369044952367869333 394259689173982142243875)
                      ·
                        rfl

theorem cell23_767818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_767818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767818 prefixEnd_767818 := by exact prefixLift 767818
  have htrace : WordTrace (prefixWord ++ tailWord_767818) baseStart_767818 baseEnd_767818 := by
    simpa [prefixWord, tailWord_767818, baseEnd_767818] using wordTrace_append hprefix tailTrace_767818
  have hstable : (prefixWord ++ tailWord_767818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767818).length < 2 ^ (prefixWord ++ tailWord_767818).sum := by decide
  have hdescent : baseEnd_767818 < baseStart_767818 := by decide
  rcases family_descends (prefixWord ++ tailWord_767818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767845 : List Nat := [1, 3, 1, 3, 1, 1, 1, 6, 1, 5]
def baseStart_767845 : Nat := 118140960795 + 767845 * 2 ^ 59
def prefixEnd_767845 : Nat := 4983230072969 + 3 ^ 40 * 767845 * 2
def baseEnd_767845 : Nat := 131424517717217845535417

theorem tailTrace_767845 : CollatzResearch.WordTrace tailWord_767845 prefixEnd_767845 131424517717217845535417 := by
  unfold tailWord_767845
  simp only [CollatzResearch.WordTrace]
  refine ⟨28005607903236177330720989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18670405268824118220480659 28005607903236177330720989)
  ·
    refine ⟨10502102963713566499020371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28005607903236177330720989 10502102963713566499020371)
    ·
      refine ⟨15753154445570349748530557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10502102963713566499020371 15753154445570349748530557)
      ·
        refine ⟨5907432917088881155698959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15753154445570349748530557 5907432917088881155698959)
        ·
          refine ⟨8861149375633321733548439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5907432917088881155698959 8861149375633321733548439)
          ·
            refine ⟨13291724063449982600322659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8861149375633321733548439 13291724063449982600322659)
            ·
              refine ⟨19937586095174973900483989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13291724063449982600322659 19937586095174973900483989)
              ·
                refine ⟨934574348211326901585187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19937586095174973900483989 934574348211326901585187)
                ·
                  refine ⟨1401861522316990352377781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 934574348211326901585187 1401861522316990352377781)
                  ·
                    refine ⟨131424517717217845535417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1401861522316990352377781 131424517717217845535417)
                    ·
                      rfl

theorem cell23_767845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_767845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767845 prefixEnd_767845 := by exact prefixLift 767845
  have htrace : WordTrace (prefixWord ++ tailWord_767845) baseStart_767845 baseEnd_767845 := by
    simpa [prefixWord, tailWord_767845, baseEnd_767845] using wordTrace_append hprefix tailTrace_767845
  have hstable : (prefixWord ++ tailWord_767845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767845).length < 2 ^ (prefixWord ++ tailWord_767845).sum := by decide
  have hdescent : baseEnd_767845 < baseStart_767845 := by decide
  rcases family_descends (prefixWord ++ tailWord_767845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767852 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 1, 5, 2]
def baseStart_767852 : Nat := 118140960795 + 767852 * 2 ^ 59
def prefixEnd_767852 : Nat := 4983230072969 + 3 ^ 40 * 767852 * 2
def baseEnd_767852 : Nat := 394277147516235009218719

theorem tailTrace_767852 : CollatzResearch.WordTrace tailWord_767852 prefixEnd_767852 394277147516235009218719 := by
  unfold tailWord_767852
  simp only [CollatzResearch.WordTrace]
  refine ⟨14002931607105408763112905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18670575476140545017483873 14002931607105408763112905)
  ·
    refine ⟨10502198705329056572334679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14002931607105408763112905 10502198705329056572334679)
    ·
      refine ⟨15753298057993584858502019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10502198705329056572334679 15753298057993584858502019)
      ·
        refine ⟨23629947086990377287753029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15753298057993584858502019 23629947086990377287753029)
        ·
          refine ⟨4430615078810695741453693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23629947086990377287753029 4430615078810695741453693)
          ·
            refine ⟨1661480654554010903045135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4430615078810695741453693 1661480654554010903045135)
            ·
              refine ⟨2492220981831016354567703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1661480654554010903045135 2492220981831016354567703)
              ·
                refine ⟨3738331472746524531851555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2492220981831016354567703 3738331472746524531851555)
                ·
                  refine ⟨5607497209119786797777333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738331472746524531851555 5607497209119786797777333)
                  ·
                    refine ⟨525702863354980012291625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5607497209119786797777333 525702863354980012291625)
                    ·
                      refine ⟨394277147516235009218719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 525702863354980012291625 394277147516235009218719)
                      ·
                        rfl

theorem cell23_767852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 5, 2].length) (baseStart_767852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767852 prefixEnd_767852 := by exact prefixLift 767852
  have htrace : WordTrace (prefixWord ++ tailWord_767852) baseStart_767852 baseEnd_767852 := by
    simpa [prefixWord, tailWord_767852, baseEnd_767852] using wordTrace_append hprefix tailTrace_767852
  have hstable : (prefixWord ++ tailWord_767852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767852).length < 2 ^ (prefixWord ++ tailWord_767852).sum := by decide
  have hdescent : baseEnd_767852 < baseStart_767852 := by decide
  rcases family_descends (prefixWord ++ tailWord_767852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767892 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_767892 : Nat := 118140960795 + 767892 * 2 ^ 59
def prefixEnd_767892 : Nat := 4983230072969 + 3 ^ 40 * 767892 * 2
def baseEnd_767892 : Nat := 131432562247471617572845

theorem tailTrace_767892 : CollatzResearch.WordTrace tailWord_767892 prefixEnd_767892 131432562247471617572845 := by
  unfold tailWord_767892
  simp only [CollatzResearch.WordTrace]
  refine ⟨14003661067032952178840965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18671548089377269571787953 14003661067032952178840965)
  ·
    refine ⟨2625686450068678533532681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14003661067032952178840965 2625686450068678533532681)
    ·
      refine ⟨1969264837551508900149511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2625686450068678533532681 1969264837551508900149511)
      ·
        refine ⟨2953897256327263350224267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1969264837551508900149511 2953897256327263350224267)
        ·
          refine ⟨4430845884490895025336401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2953897256327263350224267 4430845884490895025336401)
          ·
            refine ⟨3323134413368171269002301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4430845884490895025336401 3323134413368171269002301)
            ·
              refine ⟨1246175405013064225875863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3323134413368171269002301 1246175405013064225875863)
              ·
                refine ⟨1869263107519596338813795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246175405013064225875863 1869263107519596338813795)
                ·
                  refine ⟨2803894661279394508220693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869263107519596338813795 2803894661279394508220693)
                  ·
                    refine ⟨131432562247471617572845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2803894661279394508220693 131432562247471617572845)
                    ·
                      rfl

theorem cell23_767892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_767892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767892 prefixEnd_767892 := by exact prefixLift 767892
  have htrace : WordTrace (prefixWord ++ tailWord_767892) baseStart_767892 baseEnd_767892 := by
    simpa [prefixWord, tailWord_767892, baseEnd_767892] using wordTrace_append hprefix tailTrace_767892
  have hstable : (prefixWord ++ tailWord_767892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767892).length < 2 ^ (prefixWord ++ tailWord_767892).sum := by decide
  have hdescent : baseEnd_767892 < baseStart_767892 := by decide
  rcases family_descends (prefixWord ++ tailWord_767892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767895 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_767895 : Nat := 118140960795 + 767895 * 2 ^ 59
def prefixEnd_767895 : Nat := 4983230072969 + 3 ^ 40 * 767895 * 2
def baseEnd_767895 : Nat := 394299227184378340981021

theorem tailTrace_767895 : CollatzResearch.WordTrace tailWord_767895 prefixEnd_767895 394299227184378340981021 := by
  unfold tailWord_767895
  simp only [CollatzResearch.WordTrace]
  refine ⟨28007431553055035870041139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18671621035370023913360759 28007431553055035870041139)
  ·
    refine ⟨42011147329582553805061709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28007431553055035870041139 42011147329582553805061709)
    ·
      refine ⟨15754180248593457676898141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42011147329582553805061709 15754180248593457676898141)
      ·
        refine ⟨5907817593222546628836803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15754180248593457676898141 5907817593222546628836803)
        ·
          refine ⟨8861726389833819943255205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5907817593222546628836803 8861726389833819943255205)
          ·
            refine ⟨1661573698093841239360351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8861726389833819943255205 1661573698093841239360351)
            ·
              refine ⟨2492360547140761859040527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1661573698093841239360351 2492360547140761859040527)
              ·
                refine ⟨3738540820711142788560791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2492360547140761859040527 3738540820711142788560791)
                ·
                  refine ⟨5607811231066714182841187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738540820711142788560791 5607811231066714182841187)
                  ·
                    refine ⟨8411716846600071274261781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5607811231066714182841187 8411716846600071274261781)
                    ·
                      refine ⟨394299227184378340981021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8411716846600071274261781 394299227184378340981021)
                      ·
                        rfl

theorem cell23_767895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_767895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_767895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_767895 prefixEnd_767895 := by exact prefixLift 767895
  have htrace : WordTrace (prefixWord ++ tailWord_767895) baseStart_767895 baseEnd_767895 := by
    simpa [prefixWord, tailWord_767895, baseEnd_767895] using wordTrace_append hprefix tailTrace_767895
  have hstable : (prefixWord ++ tailWord_767895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767895).length < 2 ^ (prefixWord ++ tailWord_767895).sum := by decide
  have hdescent : baseEnd_767895 < baseStart_767895 := by decide
  rcases family_descends (prefixWord ++ tailWord_767895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768029 : List Nat := [1, 4, 2, 2, 2, 1, 1, 5, 5]
def baseStart_768029 : Nat := 118140960795 + 768029 * 2 ^ 59
def prefixEnd_768029 : Nat := 4983230072969 + 3 ^ 40 * 768029 * 2
def baseEnd_768029 : Nat := 43818670399120090745045

theorem tailTrace_768029 : CollatzResearch.WordTrace tailWord_768029 prefixEnd_768029 43818670399120090745045 := by
  unfold tailWord_768029
  simp only [CollatzResearch.WordTrace]
  refine ⟨28012318934569576755419141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18674879289713051170279427 28012318934569576755419141)
  ·
    refine ⟨5252309800231795641641089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28012318934569576755419141 5252309800231795641641089)
    ·
      refine ⟨3939232350173846731230817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5252309800231795641641089 3939232350173846731230817)
      ·
        refine ⟨2954424262630385048423113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3939232350173846731230817 2954424262630385048423113)
        ·
          refine ⟨2215818196972788786317335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2954424262630385048423113 2215818196972788786317335)
          ·
            refine ⟨3323727295459183179476003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215818196972788786317335 3323727295459183179476003)
            ·
              refine ⟨4985590943188774769214005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3323727295459183179476003 4985590943188774769214005)
              ·
                refine ⟨467399150923947634613813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4985590943188774769214005 467399150923947634613813)
                ·
                  refine ⟨43818670399120090745045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 467399150923947634613813 43818670399120090745045)
                  ·
                    rfl

theorem cell23_768029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_768029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768029 prefixEnd_768029 := by exact prefixLift 768029
  have htrace : WordTrace (prefixWord ++ tailWord_768029) baseStart_768029 baseEnd_768029 := by
    simpa [prefixWord, tailWord_768029, baseEnd_768029] using wordTrace_append hprefix tailTrace_768029
  have hstable : (prefixWord ++ tailWord_768029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768029).length < 2 ^ (prefixWord ++ tailWord_768029).sum := by decide
  have hdescent : baseEnd_768029 < baseStart_768029 := by decide
  rcases family_descends (prefixWord ++ tailWord_768029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768072 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 5, 4]
def baseStart_768072 : Nat := 118140960795 + 768072 * 2 ^ 59
def prefixEnd_768072 : Nat := 4983230072969 + 3 ^ 40 * 768072 * 2
def baseEnd_768072 : Nat := 131463371086741382822569

theorem tailTrace_768072 : CollatzResearch.WordTrace tailWord_768072 prefixEnd_768072 131463371086741382822569 := by
  unfold tailWord_768072
  simp only [CollatzResearch.WordTrace]
  refine ⟨14006943636706897549617235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18675924848942530066156313 14006943636706897549617235)
  ·
    refine ⟨21010415455060346324425853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14006943636706897549617235 21010415455060346324425853)
    ·
      refine ⟨7878905795647629871659695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21010415455060346324425853 7878905795647629871659695)
      ·
        refine ⟨11818358693471444807489543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7878905795647629871659695 11818358693471444807489543)
        ·
          refine ⟨17727538040207167211234315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11818358693471444807489543 17727538040207167211234315)
          ·
            refine ⟨26591307060310750816851473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17727538040207167211234315 26591307060310750816851473)
            ·
              refine ⟨19943480295233063112638605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26591307060310750816851473 19943480295233063112638605)
              ·
                refine ⟨7478805110712398667239477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19943480295233063112638605 7478805110712398667239477)
                ·
                  refine ⟨701137979129287375053701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7478805110712398667239477 701137979129287375053701)
                  ·
                    refine ⟨131463371086741382822569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 701137979129287375053701 131463371086741382822569)
                    ·
                      rfl

theorem cell23_768072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_768072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768072 prefixEnd_768072 := by exact prefixLift 768072
  have htrace : WordTrace (prefixWord ++ tailWord_768072) baseStart_768072 baseEnd_768072 := by
    simpa [prefixWord, tailWord_768072, baseEnd_768072] using wordTrace_append hprefix tailTrace_768072
  have hstable : (prefixWord ++ tailWord_768072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768072).length < 2 ^ (prefixWord ++ tailWord_768072).sum := by decide
  have hdescent : baseEnd_768072 < baseStart_768072 := by decide
  rcases family_descends (prefixWord ++ tailWord_768072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768075 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 6]
def baseStart_768075 : Nat := 118140960795 + 768075 * 2 ^ 59
def prefixEnd_768075 : Nat := 4983230072969 + 3 ^ 40 * 768075 * 2
def baseEnd_768075 : Nat := 394391653702187636730193

theorem tailTrace_768075 : CollatzResearch.WordTrace tailWord_768075 prefixEnd_768075 394391653702187636730193 := by
  unfold tailWord_768075
  simp only [CollatzResearch.WordTrace]
  refine ⟨28013996692402926611593679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18675997794935284407729119 28013996692402926611593679)
  ·
    refine ⟨42020995038604389917390519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28013996692402926611593679 42020995038604389917390519)
    ·
      refine ⟨63031492557906584876085779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42020995038604389917390519 63031492557906584876085779)
      ·
        refine ⟨94547238836859877314128669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63031492557906584876085779 94547238836859877314128669)
        ·
          refine ⟨35455214563822453992798251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94547238836859877314128669 35455214563822453992798251)
          ·
            refine ⟨53182821845733680989197377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35455214563822453992798251 53182821845733680989197377)
            ·
              refine ⟨39887116384300260741898033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53182821845733680989197377 39887116384300260741898033)
              ·
                refine ⟨29915337288225195556423525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39887116384300260741898033 29915337288225195556423525)
                ·
                  refine ⟨5609125741542224166829411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29915337288225195556423525 5609125741542224166829411)
                  ·
                    refine ⟨8413688612313336250244117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5609125741542224166829411 8413688612313336250244117)
                    ·
                      refine ⟨394391653702187636730193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8413688612313336250244117 394391653702187636730193)
                      ·
                        rfl

theorem cell23_768075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 6].length) (baseStart_768075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768075 prefixEnd_768075 := by exact prefixLift 768075
  have htrace : WordTrace (prefixWord ++ tailWord_768075) baseStart_768075 baseEnd_768075 := by
    simpa [prefixWord, tailWord_768075, baseEnd_768075] using wordTrace_append hprefix tailTrace_768075
  have hstable : (prefixWord ++ tailWord_768075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768075).length < 2 ^ (prefixWord ++ tailWord_768075).sum := by decide
  have hdescent : baseEnd_768075 < baseStart_768075 := by decide
  rcases family_descends (prefixWord ++ tailWord_768075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768119 : List Nat := [1, 1, 3, 1, 1, 5, 4, 1, 6]
def baseStart_768119 : Nat := 118140960795 + 768119 * 2 ^ 59
def prefixEnd_768119 : Nat := 4983230072969 + 3 ^ 40 * 768119 * 2
def baseEnd_768119 : Nat := 43823805205665051619999

theorem tailTrace_768119 : CollatzResearch.WordTrace tailWord_768119 prefixEnd_768119 43823805205665051619999 := by
  unfold tailWord_768119
  simp only [CollatzResearch.WordTrace]
  refine ⟨28015601504243522126195411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18677067669495681417463607 28015601504243522126195411)
  ·
    refine ⟨42023402256365283189293117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28015601504243522126195411 42023402256365283189293117)
    ·
      refine ⟨15758775846136981195984919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42023402256365283189293117 15758775846136981195984919)
      ·
        refine ⟨23638163769205471793977379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15758775846136981195984919 23638163769205471793977379)
        ·
          refine ⟨35457245653808207690966069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23638163769205471793977379 35457245653808207690966069)
          ·
            refine ⟨3324116780044519471028069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35457245653808207690966069 3324116780044519471028069)
            ·
              refine ⟨623271896258347400817763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3324116780044519471028069 623271896258347400817763)
              ·
                refine ⟨934907844387521101226645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623271896258347400817763 934907844387521101226645)
                ·
                  refine ⟨43823805205665051619999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 934907844387521101226645 43823805205665051619999)
                  ·
                    rfl

theorem cell23_768119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 6].length) (baseStart_768119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768119 prefixEnd_768119 := by exact prefixLift 768119
  have htrace : WordTrace (prefixWord ++ tailWord_768119) baseStart_768119 baseEnd_768119 := by
    simpa [prefixWord, tailWord_768119, baseEnd_768119] using wordTrace_append hprefix tailTrace_768119
  have hstable : (prefixWord ++ tailWord_768119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768119).length < 2 ^ (prefixWord ++ tailWord_768119).sum := by decide
  have hdescent : baseEnd_768119 < baseStart_768119 := by decide
  rcases family_descends (prefixWord ++ tailWord_768119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768156 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_768156 : Nat := 118140960795 + 768156 * 2 ^ 59
def prefixEnd_768156 : Nat := 4983230072969 + 3 ^ 40 * 768156 * 2
def baseEnd_768156 : Nat := 394433245635201819817321

theorem tailTrace_768156 : CollatzResearch.WordTrace tailWord_768156 prefixEnd_768156 394433245635201819817321 := by
  unfold tailWord_768156
  simp only [CollatzResearch.WordTrace]
  refine ⟨14008475502554738722646161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18677967336739651630194881 14008475502554738722646161)
  ·
    refine ⟨10506356626916054041984621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14008475502554738722646161 10506356626916054041984621)
    ·
      refine ⟨3939883735093520265744233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10506356626916054041984621 3939883735093520265744233)
      ·
        refine ⟨2954912801320140199308175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3939883735093520265744233 2954912801320140199308175)
        ·
          refine ⟨4432369201980210298962263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2954912801320140199308175 4432369201980210298962263)
          ·
            refine ⟨6648553802970315448443395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4432369201980210298962263 6648553802970315448443395)
            ·
              refine ⟨9972830704455473172665093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648553802970315448443395 9972830704455473172665093)
              ·
                refine ⟨1869905757085401219874705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9972830704455473172665093 1869905757085401219874705)
                ·
                  refine ⟨1402429317814050914906029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1869905757085401219874705 1402429317814050914906029)
                  ·
                    refine ⟨525910994180269093089761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1402429317814050914906029 525910994180269093089761)
                    ·
                      refine ⟨394433245635201819817321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 525910994180269093089761 394433245635201819817321)
                      ·
                        rfl

theorem cell23_768156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_768156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768156 prefixEnd_768156 := by exact prefixLift 768156
  have htrace : WordTrace (prefixWord ++ tailWord_768156) baseStart_768156 baseEnd_768156 := by
    simpa [prefixWord, tailWord_768156, baseEnd_768156] using wordTrace_append hprefix tailTrace_768156
  have hstable : (prefixWord ++ tailWord_768156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768156).length < 2 ^ (prefixWord ++ tailWord_768156).sum := by decide
  have hdescent : baseEnd_768156 < baseStart_768156 := by decide
  rcases family_descends (prefixWord ++ tailWord_768156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768186 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2]
def baseStart_768186 : Nat := 118140960795 + 768186 * 2 ^ 59
def prefixEnd_768186 : Nat := 4983230072969 + 3 ^ 40 * 768186 * 2
def baseEnd_768186 : Nat := 394448650054836702442183

theorem tailTrace_768186 : CollatzResearch.WordTrace tailWord_768186 prefixEnd_768186 394448650054836702442183 := by
  unfold tailWord_768186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7004511298750198142221103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18678696796667195045922941 7004511298750198142221103)
  ·
    refine ⟨10506766948125297213331655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7004511298750198142221103 10506766948125297213331655)
    ·
      refine ⟨15760150422187945819997483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10506766948125297213331655 15760150422187945819997483)
      ·
        refine ⟨23640225633281918729996225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15760150422187945819997483 23640225633281918729996225)
        ·
          refine ⟨17730169224961439047497169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23640225633281918729996225 17730169224961439047497169)
          ·
            refine ⟨13297626918721079285622877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17730169224961439047497169 13297626918721079285622877)
            ·
              refine ⟨4986610094520404732108579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13297626918721079285622877 4986610094520404732108579)
              ·
                refine ⟨7479915141780607098162869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4986610094520404732108579 7479915141780607098162869)
                ·
                  refine ⟨701242044541931915452769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7479915141780607098162869 701242044541931915452769)
                  ·
                    refine ⟨525931533406448936589577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 701242044541931915452769 525931533406448936589577)
                    ·
                      refine ⟨394448650054836702442183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 525931533406448936589577 394448650054836702442183)
                      ·
                        rfl

theorem cell23_768186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2].length) (baseStart_768186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768186 prefixEnd_768186 := by exact prefixLift 768186
  have htrace : WordTrace (prefixWord ++ tailWord_768186) baseStart_768186 baseEnd_768186 := by
    simpa [prefixWord, tailWord_768186, baseEnd_768186] using wordTrace_append hprefix tailTrace_768186
  have hstable : (prefixWord ++ tailWord_768186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768186).length < 2 ^ (prefixWord ++ tailWord_768186).sum := by decide
  have hdescent : baseEnd_768186 < baseStart_768186 := by decide
  rcases family_descends (prefixWord ++ tailWord_768186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768190 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_768190 : Nat := 118140960795 + 768190 * 2 ^ 59
def prefixEnd_768190 : Nat := 4983230072969 + 3 ^ 40 * 768190 * 2
def baseEnd_768190 : Nat := 394450703977454686792165

theorem tailTrace_768190 : CollatzResearch.WordTrace tailWord_768190 prefixEnd_768190 394450703977454686792165 := by
  unfold tailWord_768190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3502273885873287656503753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18678794057990867501353349 3502273885873287656503753)
  ·
    refine ⟨2626705414404965742377815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3502273885873287656503753 2626705414404965742377815)
    ·
      refine ⟨3940058121607448613566723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2626705414404965742377815 3940058121607448613566723)
      ·
        refine ⟨5910087182411172920350085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3940058121607448613566723 5910087182411172920350085)
        ·
          refine ⟨1108141346702094922565641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5910087182411172920350085 1108141346702094922565641)
          ·
            refine ⟨831106010026571191924231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1108141346702094922565641 831106010026571191924231)
            ·
              refine ⟨1246659015039856787886347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831106010026571191924231 1246659015039856787886347)
              ·
                refine ⟨1869988522559785181829521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246659015039856787886347 1869988522559785181829521)
                ·
                  refine ⟨1402491391919838886372141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1869988522559785181829521 1402491391919838886372141)
                  ·
                    refine ⟨525934271969939582389553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1402491391919838886372141 525934271969939582389553)
                    ·
                      refine ⟨394450703977454686792165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 525934271969939582389553 394450703977454686792165)
                      ·
                        rfl

theorem cell23_768190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_768190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768190 prefixEnd_768190 := by exact prefixLift 768190
  have htrace : WordTrace (prefixWord ++ tailWord_768190) baseStart_768190 baseEnd_768190 := by
    simpa [prefixWord, tailWord_768190, baseEnd_768190] using wordTrace_append hprefix tailTrace_768190
  have hstable : (prefixWord ++ tailWord_768190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768190).length < 2 ^ (prefixWord ++ tailWord_768190).sum := by decide
  have hdescent : baseEnd_768190 < baseStart_768190 := by decide
  rcases family_descends (prefixWord ++ tailWord_768190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768289 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_768289 : Nat := 118140960795 + 768289 * 2 ^ 59
def prefixEnd_768289 : Nat := 4983230072969 + 3 ^ 40 * 768289 * 2
def baseEnd_768289 : Nat := 394501538562249799454209

theorem tailTrace_768289 : CollatzResearch.WordTrace tailWord_768289 prefixEnd_768289 394501538562249799454209 := by
  unfold tailWord_768289
  simp only [CollatzResearch.WordTrace]
  refine ⟨28021801913627641159883921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18681201275751760773255947 28021801913627641159883921)
  ·
    refine ⟨21016351435220730869912941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28021801913627641159883921 21016351435220730869912941)
    ·
      refine ⟨7881131788207774076217353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21016351435220730869912941 7881131788207774076217353)
      ·
        refine ⟨5910848841155830557163015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7881131788207774076217353 5910848841155830557163015)
        ·
          refine ⟨8866273261733745835744523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5910848841155830557163015 8866273261733745835744523)
          ·
            refine ⟨13299409892600618753616785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8866273261733745835744523 13299409892600618753616785)
            ·
              refine ⟨9974557419450464065212589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13299409892600618753616785 9974557419450464065212589)
              ·
                refine ⟨3740459032293924024454721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9974557419450464065212589 3740459032293924024454721)
                ·
                  refine ⟨2805344274220443018341041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3740459032293924024454721 2805344274220443018341041)
                  ·
                    refine ⟨2104008205665332263755781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2805344274220443018341041 2104008205665332263755781)
                    ·
                      refine ⟨394501538562249799454209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2104008205665332263755781 394501538562249799454209)
                      ·
                        rfl

theorem cell23_768289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_768289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768289 prefixEnd_768289 := by exact prefixLift 768289
  have htrace : WordTrace (prefixWord ++ tailWord_768289) baseStart_768289 baseEnd_768289 := by
    simpa [prefixWord, tailWord_768289, baseEnd_768289] using wordTrace_append hprefix tailTrace_768289
  have hstable : (prefixWord ++ tailWord_768289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768289).length < 2 ^ (prefixWord ++ tailWord_768289).sum := by decide
  have hdescent : baseEnd_768289 < baseStart_768289 := by decide
  rcases family_descends (prefixWord ++ tailWord_768289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768316 : List Nat := [2, 2, 2, 2, 1, 2, 2, 5, 5]
def baseStart_768316 : Nat := 118140960795 + 768316 * 2 ^ 59
def prefixEnd_768316 : Nat := 4983230072969 + 3 ^ 40 * 768316 * 2
def baseEnd_768316 : Nat := 43835044726657910424065

theorem tailTrace_768316 : CollatzResearch.WordTrace tailWord_768316 prefixEnd_768316 43835044726657910424065 := by
  unfold tailWord_768316
  simp only [CollatzResearch.WordTrace]
  refine ⟨14011393342264912385558401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18681857789686549847411201 14011393342264912385558401)
  ·
    refine ⟨10508545006698684289168801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14011393342264912385558401 10508545006698684289168801)
    ·
      refine ⟨7881408755024013216876601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10508545006698684289168801 7881408755024013216876601)
      ·
        refine ⟨5911056566268009912657451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7881408755024013216876601 5911056566268009912657451)
        ·
          refine ⟨8866584849402014868986177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5911056566268009912657451 8866584849402014868986177)
          ·
            refine ⟨6649938637051511151739633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8866584849402014868986177 6649938637051511151739633)
            ·
              refine ⟨4987453977788633363804725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6649938637051511151739633 4987453977788633363804725)
              ·
                refine ⟨467573810417684377856693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4987453977788633363804725 467573810417684377856693)
                ·
                  refine ⟨43835044726657910424065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 467573810417684377856693 43835044726657910424065)
                  ·
                    rfl

theorem cell23_768316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 5].length) (baseStart_768316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768316 prefixEnd_768316 := by exact prefixLift 768316
  have htrace : WordTrace (prefixWord ++ tailWord_768316) baseStart_768316 baseEnd_768316 := by
    simpa [prefixWord, tailWord_768316, baseEnd_768316] using wordTrace_append hprefix tailTrace_768316
  have hstable : (prefixWord ++ tailWord_768316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768316).length < 2 ^ (prefixWord ++ tailWord_768316).sum := by decide
  have hdescent : baseEnd_768316 < baseStart_768316 := by decide
  rcases family_descends (prefixWord ++ tailWord_768316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768336 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 2, 5, 2]
def baseStart_768336 : Nat := 118140960795 + 768336 * 2 ^ 59
def prefixEnd_768336 : Nat := 4983230072969 + 3 ^ 40 * 768336 * 2
def baseEnd_768336 : Nat := 394525672153011115566493

theorem tailTrace_768336 : CollatzResearch.WordTrace tailWord_768336 prefixEnd_768336 394525672153011115566493 := by
  unfold tailWord_768336
  simp only [CollatzResearch.WordTrace]
  refine ⟨14011758072228684093422431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18682344096304912124563241 14011758072228684093422431)
  ·
    refine ⟨21017637108343026140133647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14011758072228684093422431 21017637108343026140133647)
    ·
      refine ⟨31526455662514539210200471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21017637108343026140133647 31526455662514539210200471)
      ·
        refine ⟨47289683493771808815300707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31526455662514539210200471 47289683493771808815300707)
        ·
          refine ⟨70934525240657713222951061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47289683493771808815300707 70934525240657713222951061)
          ·
            refine ⟨3325055870655830307325831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70934525240657713222951061 3325055870655830307325831)
            ·
              refine ⟨4987583805983745460988747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3325055870655830307325831 4987583805983745460988747)
              ·
                refine ⟨7481375708975618191483121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4987583805983745460988747 7481375708975618191483121)
                ·
                  refine ⟨5611031781731713643612341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7481375708975618191483121 5611031781731713643612341)
                  ·
                    refine ⟨526034229537348154088657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5611031781731713643612341 526034229537348154088657)
                    ·
                      refine ⟨394525672153011115566493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 526034229537348154088657 394525672153011115566493)
                      ·
                        rfl

theorem cell23_768336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 5, 2].length) (baseStart_768336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768336 prefixEnd_768336 := by exact prefixLift 768336
  have htrace : WordTrace (prefixWord ++ tailWord_768336) baseStart_768336 baseEnd_768336 := by
    simpa [prefixWord, tailWord_768336, baseEnd_768336] using wordTrace_append hprefix tailTrace_768336
  have hstable : (prefixWord ++ tailWord_768336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768336).length < 2 ^ (prefixWord ++ tailWord_768336).sum := by decide
  have hdescent : baseEnd_768336 < baseStart_768336 := by decide
  rcases family_descends (prefixWord ++ tailWord_768336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768379 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 6]
def baseStart_768379 : Nat := 118140960795 + 768379 * 2 ^ 59
def prefixEnd_768379 : Nat := 4983230072969 + 3 ^ 40 * 768379 * 2
def baseEnd_768379 : Nat := 394547751821154447328795

theorem tailTrace_768379 : CollatzResearch.WordTrace tailWord_768379 prefixEnd_768379 394547751821154447328795 := by
  unfold tailWord_768379
  simp only [CollatzResearch.WordTrace]
  refine ⟨28025084483301586530660191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18683389655534391020440127 28025084483301586530660191)
  ·
    refine ⟨42037626724952379795990287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28025084483301586530660191 42037626724952379795990287)
    ·
      refine ⟨63056440087428569693985431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42037626724952379795990287 63056440087428569693985431)
      ·
        refine ⟨94584660131142854540978147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63056440087428569693985431 94584660131142854540978147)
        ·
          refine ⟨141876990196714281811467221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94584660131142854540978147 141876990196714281811467221)
          ·
            refine ⟨3325241957735490979956263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 141876990196714281811467221 3325241957735490979956263)
            ·
              refine ⟨4987862936603236469934395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3325241957735490979956263 4987862936603236469934395)
              ·
                refine ⟨7481794404904854704901593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4987862936603236469934395 7481794404904854704901593)
                ·
                  refine ⟨5611345803678641028676195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7481794404904854704901593 5611345803678641028676195)
                  ·
                    refine ⟨8417018705517961543014293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5611345803678641028676195 8417018705517961543014293)
                    ·
                      refine ⟨394547751821154447328795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8417018705517961543014293 394547751821154447328795)
                      ·
                        rfl

theorem cell23_768379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 6].length) (baseStart_768379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768379 prefixEnd_768379 := by exact prefixLift 768379
  have htrace : WordTrace (prefixWord ++ tailWord_768379) baseStart_768379 baseEnd_768379 := by
    simpa [prefixWord, tailWord_768379, baseEnd_768379] using wordTrace_append hprefix tailTrace_768379
  have hstable : (prefixWord ++ tailWord_768379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768379).length < 2 ^ (prefixWord ++ tailWord_768379).sum := by decide
  have hdescent : baseEnd_768379 < baseStart_768379 := by decide
  rcases family_descends (prefixWord ++ tailWord_768379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768393 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 3, 4]
def baseStart_768393 : Nat := 118140960795 + 768393 * 2 ^ 59
def prefixEnd_768393 : Nat := 4983230072969 + 3 ^ 40 * 768393 * 2
def baseEnd_768393 : Nat := 131518313516772464184577

theorem tailTrace_768393 : CollatzResearch.WordTrace tailWord_768393 prefixEnd_768393 131518313516772464184577 := by
  unfold tailWord_768393
  simp only [CollatzResearch.WordTrace]
  refine ⟨28025595105250866921669833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18683730070167244614446555 28025595105250866921669833)
  ·
    refine ⟨21019196328938150191252375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28025595105250866921669833 21019196328938150191252375)
    ·
      refine ⟨31528794493407225286878563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21019196328938150191252375 31528794493407225286878563)
      ·
        refine ⟨47293191740110837930317845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31528794493407225286878563 47293191740110837930317845)
        ·
          refine ⟨2216868362817695527983649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47293191740110837930317845 2216868362817695527983649)
          ·
            refine ⟨1662651272113271645987737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2216868362817695527983649 1662651272113271645987737)
            ·
              refine ⟨1246988454084953734490803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1662651272113271645987737 1246988454084953734490803)
              ·
                refine ⟨1870482681127430601736205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246988454084953734490803 1870482681127430601736205)
                ·
                  refine ⟨701431005422786475651077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1870482681127430601736205 701431005422786475651077)
                  ·
                    refine ⟨131518313516772464184577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 701431005422786475651077 131518313516772464184577)
                    ·
                      rfl

theorem cell23_768393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 4].length) (baseStart_768393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768393 prefixEnd_768393 := by exact prefixLift 768393
  have htrace : WordTrace (prefixWord ++ tailWord_768393) baseStart_768393 baseEnd_768393 := by
    simpa [prefixWord, tailWord_768393, baseEnd_768393] using wordTrace_append hprefix tailTrace_768393
  have hstable : (prefixWord ++ tailWord_768393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768393).length < 2 ^ (prefixWord ++ tailWord_768393).sum := by decide
  have hdescent : baseEnd_768393 < baseStart_768393 := by decide
  rcases family_descends (prefixWord ++ tailWord_768393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768409 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 6]
def baseStart_768409 : Nat := 118140960795 + 768409 * 2 ^ 59
def prefixEnd_768409 : Nat := 4983230072969 + 3 ^ 40 * 768409 * 2
def baseEnd_768409 : Nat := 394563156240789329953657

theorem tailTrace_768409 : CollatzResearch.WordTrace tailWord_768409 prefixEnd_768409 394563156240789329953657 := by
  unfold tailWord_768409
  simp only [CollatzResearch.WordTrace]
  refine ⟨28026178673192901654252281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18684119115461934436168187 28026178673192901654252281)
  ·
    refine ⟨21019634004894676240689211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28026178673192901654252281 21019634004894676240689211)
    ·
      refine ⟨31529451007342014361033817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21019634004894676240689211 31529451007342014361033817)
      ·
        refine ⟨23647088255506510770775363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31529451007342014361033817 23647088255506510770775363)
        ·
          refine ⟨35470632383259766156163045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23647088255506510770775363 35470632383259766156163045)
          ·
            refine ⟨6650743571861206154280571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35470632383259766156163045 6650743571861206154280571)
            ·
              refine ⟨9976115357791809231420857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6650743571861206154280571 9976115357791809231420857)
              ·
                refine ⟨7482086518343856923565643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9976115357791809231420857 7482086518343856923565643)
                ·
                  refine ⟨11223129777515785385348465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7482086518343856923565643 11223129777515785385348465)
                  ·
                    refine ⟨8417347333136839039011349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11223129777515785385348465 8417347333136839039011349)
                    ·
                      refine ⟨394563156240789329953657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8417347333136839039011349 394563156240789329953657)
                      ·
                        rfl

theorem cell23_768409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_768409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768409 prefixEnd_768409 := by exact prefixLift 768409
  have htrace : WordTrace (prefixWord ++ tailWord_768409) baseStart_768409 baseEnd_768409 := by
    simpa [prefixWord, tailWord_768409, baseEnd_768409] using wordTrace_append hprefix tailTrace_768409
  have hstable : (prefixWord ++ tailWord_768409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768409).length < 2 ^ (prefixWord ++ tailWord_768409).sum := by decide
  have hdescent : baseEnd_768409 < baseStart_768409 := by decide
  rcases family_descends (prefixWord ++ tailWord_768409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768483 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 1, 6]
def baseStart_768483 : Nat := 118140960795 + 768483 * 2 ^ 59
def prefixEnd_768483 : Nat := 4983230072969 + 3 ^ 40 * 768483 * 2
def baseEnd_768483 : Nat := 131533717936407346809439

theorem tailTrace_768483 : CollatzResearch.WordTrace tailWord_768483 prefixEnd_768483 131533717936407346809439 := by
  unfold tailWord_768483
  simp only [CollatzResearch.WordTrace]
  refine ⟨28028877674924812292446103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18685918449949874861630735 28028877674924812292446103)
  ·
    refine ⟨42043316512387218438669155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28028877674924812292446103 42043316512387218438669155)
    ·
      refine ⟨63064974768580827658003733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42043316512387218438669155 63064974768580827658003733)
      ·
        refine ⟨2956170692277226296468925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63064974768580827658003733 2956170692277226296468925)
        ·
          refine ⟨1108564009603959861175847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2956170692277226296468925 1108564009603959861175847)
          ·
            refine ⟨1662846014405939791763771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108564009603959861175847 1662846014405939791763771)
            ·
              refine ⟨2494269021608909687645657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1662846014405939791763771 2494269021608909687645657)
              ·
                refine ⟨1870701766206682265734243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2494269021608909687645657 1870701766206682265734243)
                ·
                  refine ⟨2806052649310023398601365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1870701766206682265734243 2806052649310023398601365)
                  ·
                    refine ⟨131533717936407346809439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2806052649310023398601365 131533717936407346809439)
                    ·
                      rfl

theorem cell23_768483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 6].length) (baseStart_768483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768483 prefixEnd_768483 := by exact prefixLift 768483
  have htrace : WordTrace (prefixWord ++ tailWord_768483) baseStart_768483 baseEnd_768483 := by
    simpa [prefixWord, tailWord_768483, baseEnd_768483] using wordTrace_append hprefix tailTrace_768483
  have hstable : (prefixWord ++ tailWord_768483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768483).length < 2 ^ (prefixWord ++ tailWord_768483).sum := by decide
  have hdescent : baseEnd_768483 < baseStart_768483 := by decide
  rcases family_descends (prefixWord ++ tailWord_768483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768513 : List Nat := [1, 2, 4, 1, 3, 3, 1, 8]
def baseStart_768513 : Nat := 118140960795 + 768513 * 2 ^ 59
def prefixEnd_768513 : Nat := 4983230072969 + 3 ^ 40 * 768513 * 2
def baseEnd_768513 : Nat := 14615428082550256409377

theorem tailTrace_768513 : CollatzResearch.WordTrace tailWord_768513 prefixEnd_768513 14615428082550256409377 := by
  unfold tailWord_768513
  simp only [CollatzResearch.WordTrace]
  refine ⟨28029971864816127416038193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18686647909877418277358795 28029971864816127416038193)
  ·
    refine ⟨21022478898612095562028645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28029971864816127416038193 21022478898612095562028645)
    ·
      refine ⟨3941714793489767917880371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21022478898612095562028645 3941714793489767917880371)
      ·
        refine ⟨5912572190234651876820557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3941714793489767917880371 5912572190234651876820557)
        ·
          refine ⟨2217214571337994453807709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5912572190234651876820557 2217214571337994453807709)
          ·
            refine ⟨831455464251747920177891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2217214571337994453807709 831455464251747920177891)
            ·
              refine ⟨1247183196377621880266837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831455464251747920177891 1247183196377621880266837)
              ·
                refine ⟨14615428082550256409377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1247183196377621880266837 14615428082550256409377)
                ·
                  rfl

theorem cell23_768513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 8].length) (baseStart_768513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768513 prefixEnd_768513 := by exact prefixLift 768513
  have htrace : WordTrace (prefixWord ++ tailWord_768513) baseStart_768513 baseEnd_768513 := by
    simpa [prefixWord, tailWord_768513, baseEnd_768513] using wordTrace_append hprefix tailTrace_768513
  have hstable : (prefixWord ++ tailWord_768513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768513).length < 2 ^ (prefixWord ++ tailWord_768513).sum := by decide
  have hdescent : baseEnd_768513 < baseStart_768513 := by decide
  rcases family_descends (prefixWord ++ tailWord_768513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768523 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 3]
def baseStart_768523 : Nat := 118140960795 + 768523 * 2 ^ 59
def prefixEnd_768523 : Nat := 4983230072969 + 3 ^ 40 * 768523 * 2
def baseEnd_768523 : Nat := 394621693035401883928133

theorem tailTrace_768523 : CollatzResearch.WordTrace tailWord_768523 prefixEnd_768523 394621693035401883928133 := by
  unfold tailWord_768523
  simp only [CollatzResearch.WordTrace]
  refine ⟨28030336594779899123902223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18686891063186599415934815 28030336594779899123902223)
  ·
    refine ⟨42045504892169848685853335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28030336594779899123902223 42045504892169848685853335)
    ·
      refine ⟨63068257338254773028780003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42045504892169848685853335 63068257338254773028780003)
      ·
        refine ⟨94602386007382159543170005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63068257338254773028780003 94602386007382159543170005)
        ·
          refine ⟨2217243422048019364293047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 94602386007382159543170005 2217243422048019364293047)
          ·
            refine ⟨3325865133072029046439571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217243422048019364293047 3325865133072029046439571)
            ·
              refine ⟨4988797699608043569659357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3325865133072029046439571 4988797699608043569659357)
              ·
                refine ⟨1870799137353016338622259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4988797699608043569659357 1870799137353016338622259)
                ·
                  refine ⟨2806198706029524507933389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1870799137353016338622259 2806198706029524507933389)
                  ·
                    refine ⟨1052324514761071690475021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2806198706029524507933389 1052324514761071690475021)
                    ·
                      refine ⟨394621693035401883928133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1052324514761071690475021 394621693035401883928133)
                      ·
                        rfl

theorem cell23_768523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 3].length) (baseStart_768523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768523 prefixEnd_768523 := by exact prefixLift 768523
  have htrace : WordTrace (prefixWord ++ tailWord_768523) baseStart_768523 baseEnd_768523 := by
    simpa [prefixWord, tailWord_768523, baseEnd_768523] using wordTrace_append hprefix tailTrace_768523
  have hstable : (prefixWord ++ tailWord_768523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768523).length < 2 ^ (prefixWord ++ tailWord_768523).sum := by decide
  have hdescent : baseEnd_768523 < baseStart_768523 := by decide
  rcases family_descends (prefixWord ++ tailWord_768523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768544 : List Nat := [2, 1, 1, 6, 2, 2, 2, 1, 1, 2, 3]
def baseStart_768544 : Nat := 118140960795 + 768544 * 2 ^ 59
def prefixEnd_768544 : Nat := 4983230072969 + 3 ^ 40 * 768544 * 2
def baseEnd_768544 : Nat := 394632476129146301765537

theorem tailTrace_768544 : CollatzResearch.WordTrace tailWord_768544 prefixEnd_768544 394632476129146301765537 := by
  unfold tailWord_768544
  simp only [CollatzResearch.WordTrace]
  refine ⟨14015551263851909855208343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18687401685135879806944457 14015551263851909855208343)
  ·
    refine ⟨21023326895777864782812515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14015551263851909855208343 21023326895777864782812515)
    ·
      refine ⟨31534990343666797174218773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21023326895777864782812515 31534990343666797174218773)
      ·
        refine ⟨1478202672359381117541505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31534990343666797174218773 1478202672359381117541505)
        ·
          refine ⟨1108652004269535838156129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1478202672359381117541505 1108652004269535838156129)
          ·
            refine ⟨831489003202151878617097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1108652004269535838156129 831489003202151878617097)
            ·
              refine ⟨623616752401613908962823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831489003202151878617097 623616752401613908962823)
              ·
                refine ⟨935425128602420863444235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623616752401613908962823 935425128602420863444235)
                ·
                  refine ⟨1403137692903631295166353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935425128602420863444235 1403137692903631295166353)
                  ·
                    refine ⟨1052353269677723471374765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1403137692903631295166353 1052353269677723471374765)
                    ·
                      refine ⟨394632476129146301765537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1052353269677723471374765 394632476129146301765537)
                      ·
                        rfl

theorem cell23_768544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_768544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768544 prefixEnd_768544 := by exact prefixLift 768544
  have htrace : WordTrace (prefixWord ++ tailWord_768544) baseStart_768544 baseEnd_768544 := by
    simpa [prefixWord, tailWord_768544, baseEnd_768544] using wordTrace_append hprefix tailTrace_768544
  have hstable : (prefixWord ++ tailWord_768544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768544).length < 2 ^ (prefixWord ++ tailWord_768544).sum := by decide
  have hdescent : baseEnd_768544 < baseStart_768544 := by decide
  rcases family_descends (prefixWord ++ tailWord_768544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768551 : List Nat := [1, 1, 7, 2, 2, 1, 1, 2, 2, 4]
def baseStart_768551 : Nat := 118140960795 + 768551 * 2 ^ 59
def prefixEnd_768551 : Nat := 4983230072969 + 3 ^ 40 * 768551 * 2
def baseEnd_768551 : Nat := 131545356831242591459335

theorem tailTrace_768551 : CollatzResearch.WordTrace tailWord_768551 prefixEnd_768551 131545356831242591459335 := by
  unfold tailWord_768551
  simp only [CollatzResearch.WordTrace]
  refine ⟨28031357838678459905921507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18687571892452306603947671 28031357838678459905921507)
  ·
    refine ⟨42047036758017689858882261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28031357838678459905921507 42047036758017689858882261)
    ·
      refine ⟨985477424016039606067553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 42047036758017689858882261 985477424016039606067553)
      ·
        refine ⟨739108068012029704550665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 985477424016039606067553 739108068012029704550665)
        ·
          refine ⟨554331051009022278412999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 739108068012029704550665 554331051009022278412999)
          ·
            refine ⟨831496576513533417619499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554331051009022278412999 831496576513533417619499)
            ·
              refine ⟨1247244864770300126429249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831496576513533417619499 1247244864770300126429249)
              ·
                refine ⟨935433648577725094821937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247244864770300126429249 935433648577725094821937)
                ·
                  refine ⟨701575236433293821116453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 935433648577725094821937 701575236433293821116453)
                  ·
                    refine ⟨131545356831242591459335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 701575236433293821116453 131545356831242591459335)
                    ·
                      rfl

theorem cell23_768551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_768551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768551 prefixEnd_768551 := by exact prefixLift 768551
  have htrace : WordTrace (prefixWord ++ tailWord_768551) baseStart_768551 baseEnd_768551 := by
    simpa [prefixWord, tailWord_768551, baseEnd_768551] using wordTrace_append hprefix tailTrace_768551
  have hstable : (prefixWord ++ tailWord_768551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768551).length < 2 ^ (prefixWord ++ tailWord_768551).sum := by decide
  have hdescent : baseEnd_768551 < baseStart_768551 := by decide
  rcases family_descends (prefixWord ++ tailWord_768551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768573 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_768573 : Nat := 118140960795 + 768573 * 2 ^ 59
def prefixEnd_768573 : Nat := 4983230072969 + 3 ^ 40 * 768573 * 2
def baseEnd_768573 : Nat := 131549122356042229434301

theorem tailTrace_768573 : CollatzResearch.WordTrace tailWord_768573 prefixEnd_768573 131549122356042229434301 := by
  unfold tailWord_768573
  simp only [CollatzResearch.WordTrace]
  refine ⟨28032160244598757663222373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18688106829732505108814915 28032160244598757663222373)
  ·
    refine ⟨5256030045862267061854195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28032160244598757663222373 5256030045862267061854195)
    ·
      refine ⟨7884045068793400592781293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5256030045862267061854195 7884045068793400592781293)
      ·
        refine ⟨2956516900797525222292985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7884045068793400592781293 2956516900797525222292985)
        ·
          refine ⟨2217387675598143916719739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2956516900797525222292985 2217387675598143916719739)
          ·
            refine ⟨3326081513397215875079609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217387675598143916719739 3326081513397215875079609)
            ·
              refine ⟨2494561135047911906309707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3326081513397215875079609 2494561135047911906309707)
              ·
                refine ⟨3741841702571867859464561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494561135047911906309707 3741841702571867859464561)
                ·
                  refine ⟨2806381276928900894598421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3741841702571867859464561 2806381276928900894598421)
                  ·
                    refine ⟨131549122356042229434301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2806381276928900894598421 131549122356042229434301)
                    ·
                      rfl

theorem cell23_768573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_768573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768573 prefixEnd_768573 := by exact prefixLift 768573
  have htrace : WordTrace (prefixWord ++ tailWord_768573) baseStart_768573 baseEnd_768573 := by
    simpa [prefixWord, tailWord_768573, baseEnd_768573] using wordTrace_append hprefix tailTrace_768573
  have hstable : (prefixWord ++ tailWord_768573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768573).length < 2 ^ (prefixWord ++ tailWord_768573).sum := by decide
  have hdescent : baseEnd_768573 < baseStart_768573 := by decide
  rcases family_descends (prefixWord ++ tailWord_768573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768574 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_768574 : Nat := 118140960795 + 768574 * 2 ^ 59
def prefixEnd_768574 : Nat := 4983230072969 + 3 ^ 40 * 768574 * 2
def baseEnd_768574 : Nat := 394647880548781184390399

theorem tailTrace_768574 : CollatzResearch.WordTrace tailWord_768574 prefixEnd_768574 394647880548781184390399 := by
  unfold tailWord_768574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3504024589699391854251097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18688131145063423222672517 3504024589699391854251097)
  ·
    refine ⟨2628018442274543890688323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3504024589699391854251097 2628018442274543890688323)
    ·
      refine ⟨3942027663411815836032485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2628018442274543890688323 3942027663411815836032485)
      ·
        refine ⟨739130186889715469256091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3942027663411815836032485 739130186889715469256091)
        ·
          refine ⟨1108695280334573203884137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739130186889715469256091 1108695280334573203884137)
          ·
            refine ⟨831521460250929902913103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1108695280334573203884137 831521460250929902913103)
            ·
              refine ⟨1247282190376394854369655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831521460250929902913103 1247282190376394854369655)
              ·
                refine ⟨1870923285564592281554483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1247282190376394854369655 1870923285564592281554483)
                ·
                  refine ⟨2806384928346888422331725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1870923285564592281554483 2806384928346888422331725)
                  ·
                    refine ⟨1052394348130083158374397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2806384928346888422331725 1052394348130083158374397)
                    ·
                      refine ⟨394647880548781184390399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1052394348130083158374397 394647880548781184390399)
                      ·
                        rfl

theorem cell23_768574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_768574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768574 prefixEnd_768574 := by exact prefixLift 768574
  have htrace : WordTrace (prefixWord ++ tailWord_768574) baseStart_768574 baseEnd_768574 := by
    simpa [prefixWord, tailWord_768574, baseEnd_768574] using wordTrace_append hprefix tailTrace_768574
  have hstable : (prefixWord ++ tailWord_768574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768574).length < 2 ^ (prefixWord ++ tailWord_768574).sum := by decide
  have hdescent : baseEnd_768574 < baseStart_768574 := by decide
  rcases family_descends (prefixWord ++ tailWord_768574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768656 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 9]
def baseStart_768656 : Nat := 118140960795 + 768656 * 2 ^ 59
def prefixEnd_768656 : Nat := 4983230072969 + 3 ^ 40 * 768656 * 2
def baseEnd_768656 : Nat := 394689985962449863565021

theorem tailTrace_768656 : CollatzResearch.WordTrace tailWord_768656 prefixEnd_768656 394689985962449863565021 := by
  unfold tailWord_768656
  simp only [CollatzResearch.WordTrace]
  refine ⟨14017593751649031419246911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18690125002198708558995881 14017593751649031419246911)
  ·
    refine ⟨21026390627473547128870367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14017593751649031419246911 21026390627473547128870367)
    ·
      refine ⟨31539585941210320693305551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21026390627473547128870367 31539585941210320693305551)
      ·
        refine ⟨47309378911815481039958327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31539585941210320693305551 47309378911815481039958327)
        ·
          refine ⟨70964068367723221559937491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47309378911815481039958327 70964068367723221559937491)
          ·
            refine ⟨106446102551584832339906237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70964068367723221559937491 106446102551584832339906237)
            ·
              refine ⟨39917288456844312127464839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106446102551584832339906237 39917288456844312127464839)
              ·
                refine ⟨59875932685266468191197259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39917288456844312127464839 59875932685266468191197259)
                ·
                  refine ⟨89813899027899702286795889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59875932685266468191197259 89813899027899702286795889)
                  ·
                    refine ⟨67360424270924776715096917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89813899027899702286795889 67360424270924776715096917)
                    ·
                      refine ⟨394689985962449863565021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 67360424270924776715096917 394689985962449863565021)
                      ·
                        rfl

theorem cell23_768656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_768656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768656 prefixEnd_768656 := by exact prefixLift 768656
  have htrace : WordTrace (prefixWord ++ tailWord_768656) baseStart_768656 baseEnd_768656 := by
    simpa [prefixWord, tailWord_768656, baseEnd_768656] using wordTrace_append hprefix tailTrace_768656
  have hstable : (prefixWord ++ tailWord_768656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768656).length < 2 ^ (prefixWord ++ tailWord_768656).sum := by decide
  have hdescent : baseEnd_768656 < baseStart_768656 := by decide
  rcases family_descends (prefixWord ++ tailWord_768656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768660 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_768660 : Nat := 118140960795 + 768660 * 2 ^ 59
def prefixEnd_768660 : Nat := 4983230072969 + 3 ^ 40 * 768660 * 2
def baseEnd_768660 : Nat := 394692039885067847915003

theorem tailTrace_768660 : CollatzResearch.WordTrace tailWord_768660 prefixEnd_768660 394692039885067847915003 := by
  unfold tailWord_768660
  simp only [CollatzResearch.WordTrace]
  refine ⟨14017666697641785760819717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18690222263522381014426289 14017666697641785760819717)
  ·
    refine ⟨2628312505807834830153697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14017666697641785760819717 2628312505807834830153697)
    ·
      refine ⟨1971234379355876122615273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2628312505807834830153697 1971234379355876122615273)
      ·
        refine ⟨1478425784516907091961455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1971234379355876122615273 1478425784516907091961455)
        ·
          refine ⟨2217638676775360637942183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478425784516907091961455 2217638676775360637942183)
          ·
            refine ⟨3326458015163040956913275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217638676775360637942183 3326458015163040956913275)
            ·
              refine ⟨4989687022744561435369913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3326458015163040956913275 4989687022744561435369913)
              ·
                refine ⟨3742265267058421076527435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4989687022744561435369913 3742265267058421076527435)
                ·
                  refine ⟨5613397900587631614791153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742265267058421076527435 5613397900587631614791153)
                  ·
                    refine ⟨4210048425440723711093365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5613397900587631614791153 4210048425440723711093365)
                    ·
                      refine ⟨394692039885067847915003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4210048425440723711093365 394692039885067847915003)
                      ·
                        rfl

theorem cell23_768660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_768660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768660 prefixEnd_768660 := by exact prefixLift 768660
  have htrace : WordTrace (prefixWord ++ tailWord_768660) baseStart_768660 baseEnd_768660 := by
    simpa [prefixWord, tailWord_768660, baseEnd_768660] using wordTrace_append hprefix tailTrace_768660
  have hstable : (prefixWord ++ tailWord_768660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768660).length < 2 ^ (prefixWord ++ tailWord_768660).sum := by decide
  have hdescent : baseEnd_768660 < baseStart_768660 := by decide
  rcases family_descends (prefixWord ++ tailWord_768660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768714 : List Nat := [3, 1, 2, 1, 4, 2, 2, 3, 1, 4]
def baseStart_768714 : Nat := 118140960795 + 768714 * 2 ^ 59
def prefixEnd_768714 : Nat := 4983230072969 + 3 ^ 40 * 768714 * 2
def baseEnd_768714 : Nat := 131573255946803545546585

theorem tailTrace_768714 : CollatzResearch.WordTrace tailWord_768714 prefixEnd_768714 131573255946803545546585 := by
  unfold tailWord_768714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7009325734271984686026299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18691535291391959162736797 7009325734271984686026299)
  ·
    refine ⟨10513988601407977029039449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7009325734271984686026299 10513988601407977029039449)
    ·
      refine ⟨7885491451055982771779587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10513988601407977029039449 7885491451055982771779587)
      ·
        refine ⟨11828237176583974157669381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7885491451055982771779587 11828237176583974157669381)
        ·
          refine ⟨2217794470609495154563009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11828237176583974157669381 2217794470609495154563009)
          ·
            refine ⟨1663345852957121365922257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2217794470609495154563009 1663345852957121365922257)
            ·
              refine ⟨1247509389717841024441693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1663345852957121365922257 1247509389717841024441693)
              ·
                refine ⟨467816021144190384165635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1247509389717841024441693 467816021144190384165635)
                ·
                  refine ⟨701724031716285576248453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 467816021144190384165635 701724031716285576248453)
                  ·
                    refine ⟨131573255946803545546585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 701724031716285576248453 131573255946803545546585)
                    ·
                      rfl

theorem cell23_768714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_768714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768714 prefixEnd_768714 := by exact prefixLift 768714
  have htrace : WordTrace (prefixWord ++ tailWord_768714) baseStart_768714 baseEnd_768714 := by
    simpa [prefixWord, tailWord_768714, baseEnd_768714] using wordTrace_append hprefix tailTrace_768714
  have hstable : (prefixWord ++ tailWord_768714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768714).length < 2 ^ (prefixWord ++ tailWord_768714).sum := by decide
  have hdescent : baseEnd_768714 < baseStart_768714 := by decide
  rcases family_descends (prefixWord ++ tailWord_768714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768737 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_768737 : Nat := 118140960795 + 768737 * 2 ^ 59
def prefixEnd_768737 : Nat := 4983230072969 + 3 ^ 40 * 768737 * 2
def baseEnd_768737 : Nat := 394731577895464046652149

theorem tailTrace_768737 : CollatzResearch.WordTrace tailWord_768737 prefixEnd_768737 394731577895464046652149 := by
  unfold tailWord_768737
  simp only [CollatzResearch.WordTrace]
  refine ⟨28038141816004613672192465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18692094544003075781461643 28038141816004613672192465)
  ·
    refine ⟨21028606362003460254144349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28038141816004613672192465 21028606362003460254144349)
    ·
      refine ⟨7885727385751297595304131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21028606362003460254144349 7885727385751297595304131)
      ·
        refine ⟨11828591078626946392956197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7885727385751297595304131 11828591078626946392956197)
        ·
          refine ⟨2217860827242552448679287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11828591078626946392956197 2217860827242552448679287)
          ·
            refine ⟨3326791240863828673018931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217860827242552448679287 3326791240863828673018931)
            ·
              refine ⟨4990186861295743009528397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3326791240863828673018931 4990186861295743009528397)
              ·
                refine ⟨1871320072985903628573149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4990186861295743009528397 1871320072985903628573149)
                ·
                  refine ⟨701745027369713860714931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1871320072985903628573149 701745027369713860714931)
                  ·
                    refine ⟨1052617541054570791072397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 701745027369713860714931 1052617541054570791072397)
                    ·
                      refine ⟨394731577895464046652149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1052617541054570791072397 394731577895464046652149)
                      ·
                        rfl

theorem cell23_768737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_768737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768737 prefixEnd_768737 := by exact prefixLift 768737
  have htrace : WordTrace (prefixWord ++ tailWord_768737) baseStart_768737 baseEnd_768737 := by
    simpa [prefixWord, tailWord_768737, baseEnd_768737] using wordTrace_append hprefix tailTrace_768737
  have hstable : (prefixWord ++ tailWord_768737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768737).length < 2 ^ (prefixWord ++ tailWord_768737).sum := by decide
  have hdescent : baseEnd_768737 < baseStart_768737 := by decide
  rcases family_descends (prefixWord ++ tailWord_768737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768760 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 2, 6, 2]
def baseStart_768760 : Nat := 118140960795 + 768760 * 2 ^ 59
def prefixEnd_768760 : Nat := 4983230072969 + 3 ^ 40 * 768760 * 2
def baseEnd_768760 : Nat := 394743387950517456664543

theorem tailTrace_768760 : CollatzResearch.WordTrace tailWord_768760 prefixEnd_768760 394743387950517456664543 := by
  unfold tailWord_768760
  simp only [CollatzResearch.WordTrace]
  refine ⟨14019490347460644300139867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18692653796614192400186489 14019490347460644300139867)
  ·
    refine ⟨21029235521190966450209801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14019490347460644300139867 21029235521190966450209801)
    ·
      refine ⟨15771926640893224837657351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21029235521190966450209801 15771926640893224837657351)
      ·
        refine ⟨23657889961339837256486027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15771926640893224837657351 23657889961339837256486027)
        ·
          refine ⟨35486834942009755884729041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23657889961339837256486027 35486834942009755884729041)
          ·
            refine ⟨26615126206507316913546781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35486834942009755884729041 26615126206507316913546781)
            ·
              refine ⟨9980672327440243842580043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26615126206507316913546781 9980672327440243842580043)
              ·
                refine ⟨14971008491160365763870065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9980672327440243842580043 14971008491160365763870065)
                ·
                  refine ⟨11228256368370274322902549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14971008491160365763870065 11228256368370274322902549)
                  ·
                    refine ⟨526324517267356608886057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11228256368370274322902549 526324517267356608886057)
                    ·
                      refine ⟨394743387950517456664543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 526324517267356608886057 394743387950517456664543)
                      ·
                        rfl

theorem cell23_768760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 6, 2].length) (baseStart_768760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768760 prefixEnd_768760 := by exact prefixLift 768760
  have htrace : WordTrace (prefixWord ++ tailWord_768760) baseStart_768760 baseEnd_768760 := by
    simpa [prefixWord, tailWord_768760, baseEnd_768760] using wordTrace_append hprefix tailTrace_768760
  have hstable : (prefixWord ++ tailWord_768760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768760).length < 2 ^ (prefixWord ++ tailWord_768760).sum := by decide
  have hdescent : baseEnd_768760 < baseStart_768760 := by decide
  rcases family_descends (prefixWord ++ tailWord_768760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768777 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 5, 2, 2]
def baseStart_768777 : Nat := 118140960795 + 768777 * 2 ^ 59
def prefixEnd_768777 : Nat := 4983230072969 + 3 ^ 40 * 768777 * 2
def baseEnd_768777 : Nat := 394752117121643890151965

theorem tailTrace_768777 : CollatzResearch.WordTrace tailWord_768777 prefixEnd_768777 394752117121643890151965 := by
  unfold tailWord_768777
  simp only [CollatzResearch.WordTrace]
  refine ⟨28039600735859700503648585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18693067157239800335765723 28039600735859700503648585)
  ·
    refine ⟨21029700551894775377736439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28039600735859700503648585 21029700551894775377736439)
    ·
      refine ⟨31544550827842163066604659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21029700551894775377736439 31544550827842163066604659)
      ·
        refine ⟨47316826241763244599906989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31544550827842163066604659 47316826241763244599906989)
        ·
          refine ⟨17743809840661216724965121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47316826241763244599906989 17743809840661216724965121)
          ·
            refine ⟨13307857380495912543723841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17743809840661216724965121 13307857380495912543723841)
            ·
              refine ⟨9980893035371934407792881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13307857380495912543723841 9980893035371934407792881)
              ·
                refine ⟨7485669776528950805844661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9980893035371934407792881 7485669776528950805844661)
                ·
                  refine ⟨701781541549589138047937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7485669776528950805844661 701781541549589138047937)
                  ·
                    refine ⟨526336156162191853535953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 701781541549589138047937 526336156162191853535953)
                    ·
                      refine ⟨394752117121643890151965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 526336156162191853535953 394752117121643890151965)
                      ·
                        rfl

theorem cell23_768777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 2, 2].length) (baseStart_768777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768777 prefixEnd_768777 := by exact prefixLift 768777
  have htrace : WordTrace (prefixWord ++ tailWord_768777) baseStart_768777 baseEnd_768777 := by
    simpa [prefixWord, tailWord_768777, baseEnd_768777] using wordTrace_append hprefix tailTrace_768777
  have hstable : (prefixWord ++ tailWord_768777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768777).length < 2 ^ (prefixWord ++ tailWord_768777).sum := by decide
  have hdescent : baseEnd_768777 < baseStart_768777 := by decide
  rcases family_descends (prefixWord ++ tailWord_768777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768780 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 5, 2, 3]
def baseStart_768780 : Nat := 118140960795 + 768780 * 2 ^ 59
def prefixEnd_768780 : Nat := 4983230072969 + 3 ^ 40 * 768780 * 2
def baseEnd_768780 : Nat := 394753657563607378414451

theorem tailTrace_768780 : CollatzResearch.WordTrace tailWord_768780 prefixEnd_768780 394753657563607378414451 := by
  unfold tailWord_768780
  simp only [CollatzResearch.WordTrace]
  refine ⟨14019855077424416008003897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18693140103232554677338529 14019855077424416008003897)
  ·
    refine ⟨10514891308068312006002923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14019855077424416008003897 10514891308068312006002923)
    ·
      refine ⟨15772336962102468009004385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10514891308068312006002923 15772336962102468009004385)
      ·
        refine ⟨11829252721576851006753289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15772336962102468009004385 11829252721576851006753289)
        ·
          refine ⟨8871939541182638255064967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11829252721576851006753289 8871939541182638255064967)
          ·
            refine ⟨13307909311773957382597451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8871939541182638255064967 13307909311773957382597451)
            ·
              refine ⟨19961863967660936073896177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13307909311773957382597451 19961863967660936073896177)
              ·
                refine ⟨14971397975745702055422133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19961863967660936073896177 14971397975745702055422133)
                ·
                  refine ⟨1403568560226159567695825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14971397975745702055422133 1403568560226159567695825)
                  ·
                    refine ⟨1052676420169619675771869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1403568560226159567695825 1052676420169619675771869)
                    ·
                      refine ⟨394753657563607378414451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1052676420169619675771869 394753657563607378414451)
                      ·
                        rfl

theorem cell23_768780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_768780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768780 prefixEnd_768780 := by exact prefixLift 768780
  have htrace : WordTrace (prefixWord ++ tailWord_768780) baseStart_768780 baseEnd_768780 := by
    simpa [prefixWord, tailWord_768780, baseEnd_768780] using wordTrace_append hprefix tailTrace_768780
  have hstable : (prefixWord ++ tailWord_768780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768780).length < 2 ^ (prefixWord ++ tailWord_768780).sum := by decide
  have hdescent : baseEnd_768780 < baseStart_768780 := by decide
  rcases family_descends (prefixWord ++ tailWord_768780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768800 : List Nat := [2, 1, 1, 5, 1, 3, 2, 8]
def baseStart_768800 : Nat := 118140960795 + 768800 * 2 ^ 59
def prefixEnd_768800 : Nat := 4983230072969 + 3 ^ 40 * 768800 * 2
def baseEnd_768800 : Nat := 14620886191729529635717

theorem tailTrace_768800 : CollatzResearch.WordTrace tailWord_768800 prefixEnd_768800 14620886191729529635717 := by
  unfold tailWord_768800
  simp only [CollatzResearch.WordTrace]
  refine ⟨14020219807388187715867927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18693626409850916954490569 14020219807388187715867927)
  ·
    refine ⟨21030329711082281573801891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14020219807388187715867927 21030329711082281573801891)
    ·
      refine ⟨31545494566623422360702837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21030329711082281573801891 31545494566623422360702837)
      ·
        refine ⟨2957390115620945846315891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31545494566623422360702837 2957390115620945846315891)
        ·
          refine ⟨4436085173431418769473837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2957390115620945846315891 4436085173431418769473837)
          ·
            refine ⟨1663531940036782038552689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4436085173431418769473837 1663531940036782038552689)
            ·
              refine ⟨1247648955027586528914517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1663531940036782038552689 1247648955027586528914517)
              ·
                refine ⟨14620886191729529635717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1247648955027586528914517 14620886191729529635717)
                ·
                  rfl

theorem cell23_768800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 8].length) (baseStart_768800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768800 prefixEnd_768800 := by exact prefixLift 768800
  have htrace : WordTrace (prefixWord ++ tailWord_768800) baseStart_768800 baseEnd_768800 := by
    simpa [prefixWord, tailWord_768800, baseEnd_768800] using wordTrace_append hprefix tailTrace_768800
  have hstable : (prefixWord ++ tailWord_768800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768800).length < 2 ^ (prefixWord ++ tailWord_768800).sum := by decide
  have hdescent : baseEnd_768800 < baseStart_768800 := by decide
  rcases family_descends (prefixWord ++ tailWord_768800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768803 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 6]
def baseStart_768803 : Nat := 118140960795 + 768803 * 2 ^ 59
def prefixEnd_768803 : Nat := 4983230072969 + 3 ^ 40 * 768803 * 2
def baseEnd_768803 : Nat := 394765467618660788426845

theorem tailTrace_768803 : CollatzResearch.WordTrace tailWord_768803 prefixEnd_768803 394765467618660788426845 := by
  unfold tailWord_768803
  simp only [CollatzResearch.WordTrace]
  refine ⟨28040549033765506944095063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18693699355843671296063375 28040549033765506944095063)
  ·
    refine ⟨42060823550648260416142595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28040549033765506944095063 42060823550648260416142595)
    ·
      refine ⟨63091235325972390624213893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42060823550648260416142595 63091235325972390624213893)
      ·
        refine ⟨11829606623619823242040105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63091235325972390624213893 11829606623619823242040105)
        ·
          refine ⟨8872204967714867431530079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11829606623619823242040105 8872204967714867431530079)
          ·
            refine ⟨13308307451572301147295119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8872204967714867431530079 13308307451572301147295119)
            ·
              refine ⟨19962461177358451720942679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13308307451572301147295119 19962461177358451720942679)
              ·
                refine ⟨29943691766037677581414019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19962461177358451720942679 29943691766037677581414019)
                ·
                  refine ⟨44915537649056516372121029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29943691766037677581414019 44915537649056516372121029)
                  ·
                    refine ⟨8421663309198096819772693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44915537649056516372121029 8421663309198096819772693)
                    ·
                      refine ⟨394765467618660788426845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8421663309198096819772693 394765467618660788426845)
                      ·
                        rfl

theorem cell23_768803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_768803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768803 prefixEnd_768803 := by exact prefixLift 768803
  have htrace : WordTrace (prefixWord ++ tailWord_768803) baseStart_768803 baseEnd_768803 := by
    simpa [prefixWord, tailWord_768803, baseEnd_768803] using wordTrace_append hprefix tailTrace_768803
  have hstable : (prefixWord ++ tailWord_768803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768803).length < 2 ^ (prefixWord ++ tailWord_768803).sum := by decide
  have hdescent : baseEnd_768803 < baseStart_768803 := by decide
  rcases family_descends (prefixWord ++ tailWord_768803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768804 : List Nat := [2, 3, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_768804 : Nat := 118140960795 + 768804 * 2 ^ 59
def prefixEnd_768804 : Nat := 4983230072969 + 3 ^ 40 * 768804 * 2
def baseEnd_768804 : Nat := 131588660366438428171447

theorem tailTrace_768804 : CollatzResearch.WordTrace tailWord_768804 prefixEnd_768804 131588660366438428171447 := by
  unfold tailWord_768804
  simp only [CollatzResearch.WordTrace]
  refine ⟨14020292753380942057440733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18693723671174589409920977 14020292753380942057440733)
  ·
    refine ⟨5257609782517853271540275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14020292753380942057440733 5257609782517853271540275)
    ·
      refine ⟨7886414673776779907310413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5257609782517853271540275 7886414673776779907310413)
      ·
        refine ⟨2957405502666292465241405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7886414673776779907310413 2957405502666292465241405)
        ·
          refine ⟨1109027063499859674465527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2957405502666292465241405 1109027063499859674465527)
          ·
            refine ⟨1663540595249789511698291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109027063499859674465527 1663540595249789511698291)
            ·
              refine ⟨2495310892874684267547437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663540595249789511698291 2495310892874684267547437)
              ·
                refine ⟨935741584828006600330289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2495310892874684267547437 935741584828006600330289)
                ·
                  refine ⟨701806188621004950247717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 935741584828006600330289 701806188621004950247717)
                  ·
                    refine ⟨131588660366438428171447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 701806188621004950247717 131588660366438428171447)
                    ·
                      rfl

theorem cell23_768804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_768804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768804 prefixEnd_768804 := by exact prefixLift 768804
  have htrace : WordTrace (prefixWord ++ tailWord_768804) baseStart_768804 baseEnd_768804 := by
    simpa [prefixWord, tailWord_768804, baseEnd_768804] using wordTrace_append hprefix tailTrace_768804
  have hstable : (prefixWord ++ tailWord_768804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768804).length < 2 ^ (prefixWord ++ tailWord_768804).sum := by decide
  have hdescent : baseEnd_768804 < baseStart_768804 := by decide
  rcases family_descends (prefixWord ++ tailWord_768804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768814 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_768814 : Nat := 118140960795 + 768814 * 2 ^ 59
def prefixEnd_768814 : Nat := 4983230072969 + 3 ^ 40 * 768814 * 2
def baseEnd_768814 : Nat := 394771115905860245389295

theorem tailTrace_768814 : CollatzResearch.WordTrace tailWord_768814 prefixEnd_768814 394771115905860245389295 := by
  unfold tailWord_768814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3505118779590706977843187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18693966824483770548496997 3505118779590706977843187)
  ·
    refine ⟨5257678169386060466764781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3505118779590706977843187 5257678169386060466764781)
    ·
      refine ⟨1971629313519772675036793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5257678169386060466764781 1971629313519772675036793)
      ·
        refine ⟨1478721985139829506277595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1971629313519772675036793 1478721985139829506277595)
        ·
          refine ⟨2218082977709744259416393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478721985139829506277595 2218082977709744259416393)
          ·
            refine ⟨1663562233282308194562295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2218082977709744259416393 1663562233282308194562295)
            ·
              refine ⟨2495343349923462291843443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663562233282308194562295 2495343349923462291843443)
              ·
                refine ⟨3743015024885193437765165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495343349923462291843443 3743015024885193437765165)
                ·
                  refine ⟨1403630634331947539161937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3743015024885193437765165 1403630634331947539161937)
                  ·
                    refine ⟨1052722975748960654371453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1403630634331947539161937 1052722975748960654371453)
                    ·
                      refine ⟨394771115905860245389295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1052722975748960654371453 394771115905860245389295)
                      ·
                        rfl

theorem cell23_768814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_768814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768814 prefixEnd_768814 := by exact prefixLift 768814
  have htrace : WordTrace (prefixWord ++ tailWord_768814) baseStart_768814 baseEnd_768814 := by
    simpa [prefixWord, tailWord_768814, baseEnd_768814] using wordTrace_append hprefix tailTrace_768814
  have hstable : (prefixWord ++ tailWord_768814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768814).length < 2 ^ (prefixWord ++ tailWord_768814).sum := by decide
  have hdescent : baseEnd_768814 < baseStart_768814 := by decide
  rcases family_descends (prefixWord ++ tailWord_768814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768838 : List Nat := [6, 1, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_768838 : Nat := 118140960795 + 768838 * 2 ^ 59
def prefixEnd_768838 : Nat := 4983230072969 + 3 ^ 40 * 768838 * 2
def baseEnd_768838 : Nat := 131594479813856050496395

theorem tailTrace_768838 : CollatzResearch.WordTrace tailWord_768838 prefixEnd_768838 131594479813856050496395 := by
  unfold tailWord_768838
  simp only [CollatzResearch.WordTrace]
  refine ⟨876307049644959622550599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18694550392425805281079445 876307049644959622550599)
  ·
    refine ⟨1314460574467439433825899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 876307049644959622550599 1314460574467439433825899)
    ·
      refine ⟨1971690861701159150738849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1314460574467439433825899 1971690861701159150738849)
      ·
        refine ⟨1478768146275869363054137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1971690861701159150738849 1478768146275869363054137)
        ·
          refine ⟨1109076109706902022290603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1478768146275869363054137 1109076109706902022290603)
          ·
            refine ⟨1663614164560353033435905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109076109706902022290603 1663614164560353033435905)
            ·
              refine ⟨1247710623420264775076929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1663614164560353033435905 1247710623420264775076929)
              ·
                refine ⟨935782967565198581307697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247710623420264775076929 935782967565198581307697)
                ·
                  refine ⟨701837225673898935980773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 935782967565198581307697 701837225673898935980773)
                  ·
                    refine ⟨131594479813856050496395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 701837225673898935980773 131594479813856050496395)
                    ·
                      rfl

theorem cell23_768838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_768838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768838 prefixEnd_768838 := by exact prefixLift 768838
  have htrace : WordTrace (prefixWord ++ tailWord_768838) baseStart_768838 baseEnd_768838 := by
    simpa [prefixWord, tailWord_768838, baseEnd_768838] using wordTrace_append hprefix tailTrace_768838
  have hstable : (prefixWord ++ tailWord_768838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768838).length < 2 ^ (prefixWord ++ tailWord_768838).sum := by decide
  have hdescent : baseEnd_768838 < baseStart_768838 := by decide
  rcases family_descends (prefixWord ++ tailWord_768838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768843 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 5, 8]
def baseStart_768843 : Nat := 118140960795 + 768843 * 2 ^ 59
def prefixEnd_768843 : Nat := 4983230072969 + 3 ^ 40 * 768843 * 2
def baseEnd_768843 : Nat := 131595335614946877308887

theorem tailTrace_768843 : CollatzResearch.WordTrace tailWord_768843 prefixEnd_768843 131595335614946877308887 := by
  unfold tailWord_768843
  simp only [CollatzResearch.WordTrace]
  refine ⟨28042007953620593775551183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18694671969080395850367455 28042007953620593775551183)
  ·
    refine ⟨42063011930430890663326775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28042007953620593775551183 42063011930430890663326775)
    ·
      refine ⟨63094517895646335994990163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42063011930430890663326775 63094517895646335994990163)
      ·
        refine ⟨94641776843469503992485245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63094517895646335994990163 94641776843469503992485245)
        ·
          refine ⟨35490666316301063997181967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94641776843469503992485245 35490666316301063997181967)
          ·
            refine ⟨53235999474451595995772951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35490666316301063997181967 53235999474451595995772951)
            ·
              refine ⟨79853999211677393993659427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53235999474451595995772951 79853999211677393993659427)
              ·
                refine ⟨119780998817516090990489141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79853999211677393993659427 119780998817516090990489141)
                ·
                  refine ⟨11229468639142133530358357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119780998817516090990489141 11229468639142133530358357)
                  ·
                    refine ⟨131595335614946877308887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11229468639142133530358357 131595335614946877308887)
                    ·
                      rfl

theorem cell23_768843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 8].length) (baseStart_768843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768843 prefixEnd_768843 := by exact prefixLift 768843
  have htrace : WordTrace (prefixWord ++ tailWord_768843) baseStart_768843 baseEnd_768843 := by
    simpa [prefixWord, tailWord_768843, baseEnd_768843] using wordTrace_append hprefix tailTrace_768843
  have hstable : (prefixWord ++ tailWord_768843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768843).length < 2 ^ (prefixWord ++ tailWord_768843).sum := by decide
  have hdescent : baseEnd_768843 < baseStart_768843 := by decide
  rcases family_descends (prefixWord ++ tailWord_768843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768844 : List Nat := [2, 2, 1, 3, 3, 1, 1, 4, 2, 1, 3]
def baseStart_768844 : Nat := 118140960795 + 768844 * 2 ^ 59
def prefixEnd_768844 : Nat := 4983230072969 + 3 ^ 40 * 768844 * 2
def baseEnd_768844 : Nat := 394786520325495128014157

theorem tailTrace_768844 : CollatzResearch.WordTrace tailWord_768844 prefixEnd_768844 394786520325495128014157 := by
  unfold tailWord_768844
  simp only [CollatzResearch.WordTrace]
  refine ⟨14021022213308485473168793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18694696284411313964225057 14021022213308485473168793)
  ·
    refine ⟨10515766659981364104876595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14021022213308485473168793 10515766659981364104876595)
    ·
      refine ⟨15773649989972046157314893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10515766659981364104876595 15773649989972046157314893)
      ·
        refine ⟨5915118746239517308993085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15773649989972046157314893 5915118746239517308993085)
        ·
          refine ⟨2218169529839818990872407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5915118746239517308993085 2218169529839818990872407)
          ·
            refine ⟨3327254294759728486308611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218169529839818990872407 3327254294759728486308611)
            ·
              refine ⟨4990881442139592729462917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327254294759728486308611 4990881442139592729462917)
              ·
                refine ⟨935790270401173636774297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4990881442139592729462917 935790270401173636774297)
                ·
                  refine ⟨701842702800880227580723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 935790270401173636774297 701842702800880227580723)
                  ·
                    refine ⟨1052764054201320341371085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 701842702800880227580723 1052764054201320341371085)
                    ·
                      refine ⟨394786520325495128014157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1052764054201320341371085 394786520325495128014157)
                      ·
                        rfl

theorem cell23_768844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_768844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768844 prefixEnd_768844 := by exact prefixLift 768844
  have htrace : WordTrace (prefixWord ++ tailWord_768844) baseStart_768844 baseEnd_768844 := by
    simpa [prefixWord, tailWord_768844, baseEnd_768844] using wordTrace_append hprefix tailTrace_768844
  have hstable : (prefixWord ++ tailWord_768844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768844).length < 2 ^ (prefixWord ++ tailWord_768844).sum := by decide
  have hdescent : baseEnd_768844 < baseStart_768844 := by decide
  rcases family_descends (prefixWord ++ tailWord_768844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768845 : List Nat := [1, 6, 1, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_768845 : Nat := 118140960795 + 768845 * 2 ^ 59
def prefixEnd_768845 : Nat := 4983230072969 + 3 ^ 40 * 768845 * 2
def baseEnd_768845 : Nat := 394787033806149624101653

theorem tailTrace_768845 : CollatzResearch.WordTrace tailWord_768845 prefixEnd_768845 394787033806149624101653 := by
  unfold tailWord_768845
  simp only [CollatzResearch.WordTrace]
  refine ⟨28042080899613348117123989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18694720599742232078082659 28042080899613348117123989)
  ·
    refine ⟨1314472542169375692990187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28042080899613348117123989 1314472542169375692990187)
    ·
      refine ⟨1971708813254063539485281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1314472542169375692990187 1971708813254063539485281)
      ·
        refine ⟨1478781609940547654613961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1971708813254063539485281 1478781609940547654613961)
        ·
          refine ⟨1109086207455410740960471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1478781609940547654613961 1109086207455410740960471)
          ·
            refine ⟨1663629311183116111440707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109086207455410740960471 1663629311183116111440707)
            ·
              refine ⟨2495443966774674167161061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663629311183116111440707 2495443966774674167161061)
              ·
                refine ⟨467895743770251406342699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2495443966774674167161061 467895743770251406342699)
                ·
                  refine ⟨701843615655377109514049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 467895743770251406342699 701843615655377109514049)
                  ·
                    refine ⟨526382711741532832135537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 701843615655377109514049 526382711741532832135537)
                    ·
                      refine ⟨394787033806149624101653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 526382711741532832135537 394787033806149624101653)
                      ·
                        rfl

theorem cell23_768845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_768845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768845 prefixEnd_768845 := by exact prefixLift 768845
  have htrace : WordTrace (prefixWord ++ tailWord_768845) baseStart_768845 baseEnd_768845 := by
    simpa [prefixWord, tailWord_768845, baseEnd_768845] using wordTrace_append hprefix tailTrace_768845
  have hstable : (prefixWord ++ tailWord_768845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768845).length < 2 ^ (prefixWord ++ tailWord_768845).sum := by decide
  have hdescent : baseEnd_768845 < baseStart_768845 := by decide
  rcases family_descends (prefixWord ++ tailWord_768845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768850 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_768850 : Nat := 118140960795 + 768850 * 2 ^ 59
def prefixEnd_768850 : Nat := 4983230072969 + 3 ^ 40 * 768850 * 2
def baseEnd_768850 : Nat := 394789601209422104539129

theorem tailTrace_768850 : CollatzResearch.WordTrace tailWord_768850 prefixEnd_768850 394789601209422104539129 := by
  unfold tailWord_768850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7010565816148808492764001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18694842176396822647370669 7010565816148808492764001)
  ·
    refine ⟨5257924362111606369573001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7010565816148808492764001 5257924362111606369573001)
    ·
      refine ⟨3943443271583704777179751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5257924362111606369573001 3943443271583704777179751)
      ·
        refine ⟨5915164907375557165769627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3943443271583704777179751 5915164907375557165769627)
        ·
          refine ⟨8872747361063335748654441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5915164907375557165769627 8872747361063335748654441)
          ·
            refine ⟨6654560520797501811490831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8872747361063335748654441 6654560520797501811490831)
            ·
              refine ⟨9981840781196252717236247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6654560520797501811490831 9981840781196252717236247)
              ·
                refine ⟨14972761171794379075854371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9981840781196252717236247 14972761171794379075854371)
                ·
                  refine ⟨22459141757691568613781557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14972761171794379075854371 22459141757691568613781557)
                  ·
                    refine ⟨2105544539783584557542021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22459141757691568613781557 2105544539783584557542021)
                    ·
                      refine ⟨394789601209422104539129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2105544539783584557542021 394789601209422104539129)
                      ·
                        rfl

theorem cell23_768850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_768850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768850 prefixEnd_768850 := by exact prefixLift 768850
  have htrace : WordTrace (prefixWord ++ tailWord_768850) baseStart_768850 baseEnd_768850 := by
    simpa [prefixWord, tailWord_768850, baseEnd_768850] using wordTrace_append hprefix tailTrace_768850
  have hstable : (prefixWord ++ tailWord_768850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768850).length < 2 ^ (prefixWord ++ tailWord_768850).sum := by decide
  have hdescent : baseEnd_768850 < baseStart_768850 := by decide
  rcases family_descends (prefixWord ++ tailWord_768850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768901 : List Nat := [1, 3, 1, 1, 3, 3, 3, 2, 2, 2, 2]
def baseStart_768901 : Nat := 118140960795 + 768901 * 2 ^ 59
def prefixEnd_768901 : Nat := 4983230072969 + 3 ^ 40 * 768901 * 2
def baseEnd_768901 : Nat := 394815788722801405001395

theorem tailTrace_768901 : CollatzResearch.WordTrace tailWord_768901 prefixEnd_768901 394815788722801405001395 := by
  unfold tailWord_768901
  simp only [CollatzResearch.WordTrace]
  refine ⟨28044123387410469681162557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18696082258273646454108371 28044123387410469681162557)
  ·
    refine ⟨10516546270278926130435959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28044123387410469681162557 10516546270278926130435959)
    ·
      refine ⟨15774819405418389195653939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10516546270278926130435959 15774819405418389195653939)
      ·
        refine ⟨23662229108127583793480909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15774819405418389195653939 23662229108127583793480909)
        ·
          refine ⟨8873335915547843922555341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23662229108127583793480909 8873335915547843922555341)
          ·
            refine ⟨3327500968330441470958253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8873335915547843922555341 3327500968330441470958253)
            ·
              refine ⟨1247812863123915551609345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3327500968330441470958253 1247812863123915551609345)
              ·
                refine ⟨935859647342936663707009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247812863123915551609345 935859647342936663707009)
                ·
                  refine ⟨701894735507202497780257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 935859647342936663707009 701894735507202497780257)
                  ·
                    refine ⟨526421051630401873335193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 701894735507202497780257 526421051630401873335193)
                    ·
                      refine ⟨394815788722801405001395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 526421051630401873335193 394815788722801405001395)
                      ·
                        rfl

theorem cell23_768901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 2, 2].length) (baseStart_768901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768901 prefixEnd_768901 := by exact prefixLift 768901
  have htrace : WordTrace (prefixWord ++ tailWord_768901) baseStart_768901 baseEnd_768901 := by
    simpa [prefixWord, tailWord_768901, baseEnd_768901] using wordTrace_append hprefix tailTrace_768901
  have hstable : (prefixWord ++ tailWord_768901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768901).length < 2 ^ (prefixWord ++ tailWord_768901).sum := by decide
  have hdescent : baseEnd_768901 < baseStart_768901 := by decide
  rcases family_descends (prefixWord ++ tailWord_768901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768907 : List Nat := [1, 1, 1, 1, 4, 2, 4, 4, 5]
def baseStart_768907 : Nat := 118140960795 + 768907 * 2 ^ 59
def prefixEnd_768907 : Nat := 4983230072969 + 3 ^ 40 * 768907 * 2
def baseEnd_768907 : Nat := 43868763289636486836263

theorem tailTrace_768907 : CollatzResearch.WordTrace tailWord_768907 prefixEnd_768907 43868763289636486836263 := by
  unfold tailWord_768907
  simp only [CollatzResearch.WordTrace]
  refine ⟨28044342225388732705880975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18696228150259155137253983 28044342225388732705880975)
  ·
    refine ⟨42066513338083099058821463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28044342225388732705880975 42066513338083099058821463)
    ·
      refine ⟨63099770007124648588232195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42066513338083099058821463 63099770007124648588232195)
      ·
        refine ⟨94649655010686972882348293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63099770007124648588232195 94649655010686972882348293)
        ·
          refine ⟨17746810314503807415440305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94649655010686972882348293 17746810314503807415440305)
          ·
            refine ⟨13310107735877855561580229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17746810314503807415440305 13310107735877855561580229)
            ·
              refine ⟨2495645200477097917796293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13310107735877855561580229 2495645200477097917796293)
              ·
                refine ⟨467933475089455859586805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2495645200477097917796293 467933475089455859586805)
                ·
                  refine ⟨43868763289636486836263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 467933475089455859586805 43868763289636486836263)
                  ·
                    rfl

theorem cell23_768907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 5].length) (baseStart_768907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768907 prefixEnd_768907 := by exact prefixLift 768907
  have htrace : WordTrace (prefixWord ++ tailWord_768907) baseStart_768907 baseEnd_768907 := by
    simpa [prefixWord, tailWord_768907, baseEnd_768907] using wordTrace_append hprefix tailTrace_768907
  have hstable : (prefixWord ++ tailWord_768907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768907).length < 2 ^ (prefixWord ++ tailWord_768907).sum := by decide
  have hdescent : baseEnd_768907 < baseStart_768907 := by decide
  rcases family_descends (prefixWord ++ tailWord_768907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768917 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_768917 : Nat := 118140960795 + 768917 * 2 ^ 59
def prefixEnd_768917 : Nat := 4983230072969 + 3 ^ 40 * 768917 * 2
def baseEnd_768917 : Nat := 394824004413273342401321

theorem tailTrace_768917 : CollatzResearch.WordTrace tailWord_768917 prefixEnd_768917 394824004413273342401321 := by
  unfold tailWord_768917
  simp only [CollatzResearch.WordTrace]
  refine ⟨28044706955352504413745005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18696471303568336275830003 28044706955352504413745005)
  ·
    refine ⟨10516765108257189155154377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28044706955352504413745005 10516765108257189155154377)
    ·
      refine ⟨7887573831192891866365783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10516765108257189155154377 7887573831192891866365783)
      ·
        refine ⟨11831360746789337799548675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7887573831192891866365783 11831360746789337799548675)
        ·
          refine ⟨17747041120184006699323013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11831360746789337799548675 17747041120184006699323013)
          ·
            refine ⟨3327570210034501256123065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17747041120184006699323013 3327570210034501256123065)
            ·
              refine ⟨2495677657525875942092299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3327570210034501256123065 2495677657525875942092299)
              ·
                refine ⟨3743516486288813913138449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495677657525875942092299 3743516486288813913138449)
                ·
                  refine ⟨2807637364716610434853837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3743516486288813913138449 2807637364716610434853837)
                  ·
                    refine ⟨1052864011768728913070189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2807637364716610434853837 1052864011768728913070189)
                    ·
                      refine ⟨394824004413273342401321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1052864011768728913070189 394824004413273342401321)
                      ·
                        rfl

theorem cell23_768917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_768917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768917 prefixEnd_768917 := by exact prefixLift 768917
  have htrace : WordTrace (prefixWord ++ tailWord_768917) baseStart_768917 baseEnd_768917 := by
    simpa [prefixWord, tailWord_768917, baseEnd_768917] using wordTrace_append hprefix tailTrace_768917
  have hstable : (prefixWord ++ tailWord_768917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768917).length < 2 ^ (prefixWord ++ tailWord_768917).sum := by decide
  have hdescent : baseEnd_768917 < baseStart_768917 := by decide
  rcases family_descends (prefixWord ++ tailWord_768917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768977 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 4, 2, 3]
def baseStart_768977 : Nat := 118140960795 + 768977 * 2 ^ 59
def prefixEnd_768977 : Nat := 4983230072969 + 3 ^ 40 * 768977 * 2
def baseEnd_768977 : Nat := 394854813252543107651045

theorem tailTrace_768977 : CollatzResearch.WordTrace tailWord_768977 prefixEnd_768977 394854813252543107651045 := by
  unfold tailWord_768977
  simp only [CollatzResearch.WordTrace]
  refine ⟨28046895335135134660929185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18697930223423423107286123 28046895335135134660929185)
  ·
    refine ⟨21035171501351350995696889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28046895335135134660929185 21035171501351350995696889)
    ·
      refine ⟨15776378626013513246772667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21035171501351350995696889 15776378626013513246772667)
      ·
        refine ⟨23664567939020269870159001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15776378626013513246772667 23664567939020269870159001)
        ·
          refine ⟨17748425954265202402619251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23664567939020269870159001 17748425954265202402619251)
          ·
            refine ⟨26622638931397803603928877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17748425954265202402619251 26622638931397803603928877)
            ·
              refine ⟨9983489599274176351473329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26622638931397803603928877 9983489599274176351473329)
              ·
                refine ⟨7487617199455632263604997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9983489599274176351473329 7487617199455632263604997)
                ·
                  refine ⟨1403928224897931049425937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7487617199455632263604997 1403928224897931049425937)
                  ·
                    refine ⟨1052946168673448287069453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1403928224897931049425937 1052946168673448287069453)
                    ·
                      refine ⟨394854813252543107651045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1052946168673448287069453 394854813252543107651045)
                      ·
                        rfl

theorem cell23_768977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_768977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_768977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_768977 prefixEnd_768977 := by exact prefixLift 768977
  have htrace : WordTrace (prefixWord ++ tailWord_768977) baseStart_768977 baseEnd_768977 := by
    simpa [prefixWord, tailWord_768977, baseEnd_768977] using wordTrace_append hprefix tailTrace_768977
  have hstable : (prefixWord ++ tailWord_768977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768977).length < 2 ^ (prefixWord ++ tailWord_768977).sum := by decide
  have hdescent : baseEnd_768977 < baseStart_768977 := by decide
  rcases family_descends (prefixWord ++ tailWord_768977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769014 : List Nat := [5, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_769014 : Nat := 118140960795 + 769014 * 2 ^ 59
def prefixEnd_769014 : Nat := 4983230072969 + 3 ^ 40 * 769014 * 2
def baseEnd_769014 : Nat := 43874868004084384765375

theorem tailTrace_769014 : CollatzResearch.WordTrace tailWord_769014 prefixEnd_769014 43874868004084384765375 := by
  unfold tailWord_769014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753015302250068123751631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18698829890667393320017397 1753015302250068123751631)
  ·
    refine ⟨2629522953375102185627447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1753015302250068123751631 2629522953375102185627447)
    ·
      refine ⟨3944284430062653278441171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2629522953375102185627447 3944284430062653278441171)
      ·
        refine ⟨5916426645093979917661757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3944284430062653278441171 5916426645093979917661757)
        ·
          refine ⟨2218659991910242469123159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5916426645093979917661757 2218659991910242469123159)
          ·
            refine ⟨3327989987865363703684739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218659991910242469123159 3327989987865363703684739)
            ·
              refine ⟨4991984981798045555527109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327989987865363703684739 4991984981798045555527109)
              ·
                refine ⟨935997184087133541661333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4991984981798045555527109 935997184087133541661333)
                ·
                  refine ⟨43874868004084384765375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 935997184087133541661333 43874868004084384765375)
                  ·
                    rfl

theorem cell23_769014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_769014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769014 prefixEnd_769014 := by exact prefixLift 769014
  have htrace : WordTrace (prefixWord ++ tailWord_769014) baseStart_769014 baseEnd_769014 := by
    simpa [prefixWord, tailWord_769014, baseEnd_769014] using wordTrace_append hprefix tailTrace_769014
  have hstable : (prefixWord ++ tailWord_769014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769014).length < 2 ^ (prefixWord ++ tailWord_769014).sum := by decide
  have hdescent : baseEnd_769014 < baseStart_769014 := by decide
  rcases family_descends (prefixWord ++ tailWord_769014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769042 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_769042 : Nat := 118140960795 + 769042 * 2 ^ 59
def prefixEnd_769042 : Nat := 4983230072969 + 3 ^ 40 * 769042 * 2
def baseEnd_769042 : Nat := 394888189495085353338247

theorem tailTrace_769042 : CollatzResearch.WordTrace tailWord_769042 prefixEnd_769042 394888189495085353338247 := by
  unfold tailWord_769042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012316519974912690511345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18699510719933100508030253 7012316519974912690511345)
  ·
    refine ⟨5259237389981184517883509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7012316519974912690511345 5259237389981184517883509)
    ·
      refine ⟨493053505310736048551579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5259237389981184517883509 493053505310736048551579)
      ·
        refine ⟨739580257966104072827369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493053505310736048551579 739580257966104072827369)
        ·
          refine ⟨554685193474578054620527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 739580257966104072827369 554685193474578054620527)
          ·
            refine ⟨832027790211867081930791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554685193474578054620527 832027790211867081930791)
            ·
              refine ⟨1248041685317800622896187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832027790211867081930791 1248041685317800622896187)
              ·
                refine ⟨1872062527976700934344281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1248041685317800622896187 1872062527976700934344281)
                ·
                  refine ⟨1404046895982525700758211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1872062527976700934344281 1404046895982525700758211)
                  ·
                    refine ⟨2106070343973788551137317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1404046895982525700758211 2106070343973788551137317)
                    ·
                      refine ⟨394888189495085353338247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2106070343973788551137317 394888189495085353338247)
                      ·
                        rfl

theorem cell23_769042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_769042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769042 prefixEnd_769042 := by exact prefixLift 769042
  have htrace : WordTrace (prefixWord ++ tailWord_769042) baseStart_769042 baseEnd_769042 := by
    simpa [prefixWord, tailWord_769042, baseEnd_769042] using wordTrace_append hprefix tailTrace_769042
  have hstable : (prefixWord ++ tailWord_769042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769042).length < 2 ^ (prefixWord ++ tailWord_769042).sum := by decide
  have hdescent : baseEnd_769042 < baseStart_769042 := by decide
  rcases family_descends (prefixWord ++ tailWord_769042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769058 : List Nat := [3, 3, 1, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_769058 : Nat := 118140960795 + 769058 * 2 ^ 59
def prefixEnd_769058 : Nat := 4983230072969 + 3 ^ 40 * 769058 * 2
def baseEnd_769058 : Nat := 394896405185557290738173

theorem tailTrace_769058 : CollatzResearch.WordTrace tailWord_769058 prefixEnd_769058 394896405185557290738173 := by
  unfold tailWord_769058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012462411960421373656957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18699899765227790329751885 7012462411960421373656957)
  ·
    refine ⟨2629673404485158015121359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7012462411960421373656957 2629673404485158015121359)
    ·
      refine ⟨3944510106727737022682039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2629673404485158015121359 3944510106727737022682039)
      ·
        refine ⟨5916765160091605534023059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3944510106727737022682039 5916765160091605534023059)
        ·
          refine ⟨8875147740137408301034589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5916765160091605534023059 8875147740137408301034589)
          ·
            refine ⟨3328180402551528112887971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8875147740137408301034589 3328180402551528112887971)
            ·
              refine ⟨4992270603827292169331957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328180402551528112887971 4992270603827292169331957)
              ·
                refine ⟨468025369108808640874871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4992270603827292169331957 468025369108808640874871)
                ·
                  refine ⟨702038053663212961312307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468025369108808640874871 702038053663212961312307)
                  ·
                    refine ⟨1053057080494819441968461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 702038053663212961312307 1053057080494819441968461)
                    ·
                      refine ⟨394896405185557290738173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1053057080494819441968461 394896405185557290738173)
                      ·
                        rfl

theorem cell23_769058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_769058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769058 prefixEnd_769058 := by exact prefixLift 769058
  have htrace : WordTrace (prefixWord ++ tailWord_769058) baseStart_769058 baseEnd_769058 := by
    simpa [prefixWord, tailWord_769058, baseEnd_769058] using wordTrace_append hprefix tailTrace_769058
  have hstable : (prefixWord ++ tailWord_769058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769058).length < 2 ^ (prefixWord ++ tailWord_769058).sum := by decide
  have hdescent : baseEnd_769058 < baseStart_769058 := by decide
  rcases family_descends (prefixWord ++ tailWord_769058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769067 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 5]
def baseStart_769067 : Nat := 118140960795 + 769067 * 2 ^ 59
def prefixEnd_769067 : Nat := 4983230072969 + 3 ^ 40 * 769067 * 2
def baseEnd_769067 : Nat := 394901026511447755525631

theorem tailTrace_769067 : CollatzResearch.WordTrace tailWord_769067 prefixEnd_769067 394901026511447755525631 := by
  unfold tailWord_769067
  simp only [CollatzResearch.WordTrace]
  refine ⟨28050177904809080031705455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18700118603206053354470303 28050177904809080031705455)
  ·
    refine ⟨42075266857213620047558183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28050177904809080031705455 42075266857213620047558183)
    ·
      refine ⟨63112900285820430071337275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42075266857213620047558183 63112900285820430071337275)
      ·
        refine ⟨94669350428730645107005913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63112900285820430071337275 94669350428730645107005913)
        ·
          refine ⟨71002012821547983830254435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94669350428730645107005913 71002012821547983830254435)
          ·
            refine ⟨106503019232321975745381653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71002012821547983830254435 106503019232321975745381653)
            ·
              refine ⟨4992329026515092613064765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106503019232321975745381653 4992329026515092613064765)
              ·
                refine ⟨1872123384943159729899287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4992329026515092613064765 1872123384943159729899287)
                ·
                  refine ⟨2808185077414739594848931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872123384943159729899287 2808185077414739594848931)
                  ·
                    refine ⟨4212277616122109392273397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2808185077414739594848931 4212277616122109392273397)
                    ·
                      refine ⟨394901026511447755525631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4212277616122109392273397 394901026511447755525631)
                      ·
                        rfl

theorem cell23_769067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 5].length) (baseStart_769067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769067 prefixEnd_769067 := by exact prefixLift 769067
  have htrace : WordTrace (prefixWord ++ tailWord_769067) baseStart_769067 baseEnd_769067 := by
    simpa [prefixWord, tailWord_769067, baseEnd_769067] using wordTrace_append hprefix tailTrace_769067
  have hstable : (prefixWord ++ tailWord_769067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769067).length < 2 ^ (prefixWord ++ tailWord_769067).sum := by decide
  have hdescent : baseEnd_769067 < baseStart_769067 := by decide
  rcases family_descends (prefixWord ++ tailWord_769067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769074 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_769074 : Nat := 118140960795 + 769074 * 2 ^ 59
def prefixEnd_769074 : Nat := 4983230072969 + 3 ^ 40 * 769074 * 2
def baseEnd_769074 : Nat := 131634873625343076046033

theorem tailTrace_769074 : CollatzResearch.WordTrace tailWord_769074 prefixEnd_769074 131634873625343076046033 := by
  unfold tailWord_769074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012608303945930056802569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18700288810522480151473517 7012608303945930056802569)
  ·
    refine ⟨5259456227959447542601927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7012608303945930056802569 5259456227959447542601927)
    ·
      refine ⟨7889184341939171313902891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5259456227959447542601927 7889184341939171313902891)
      ·
        refine ⟨11833776512908756970854337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7889184341939171313902891 11833776512908756970854337)
        ·
          refine ⟨8875332384681567728140753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11833776512908756970854337 8875332384681567728140753)
          ·
            refine ⟨6656499288511175796105565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8875332384681567728140753 6656499288511175796105565)
            ·
              refine ⟨2496187233191690923539587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6656499288511175796105565 2496187233191690923539587)
              ·
                refine ⟨3744280849787536385309381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496187233191690923539587 3744280849787536385309381)
                ·
                  refine ⟨702052659335163072245509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3744280849787536385309381 702052659335163072245509)
                  ·
                    refine ⟨131634873625343076046033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 702052659335163072245509 131634873625343076046033)
                    ·
                      rfl

theorem cell23_769074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_769074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769074 prefixEnd_769074 := by exact prefixLift 769074
  have htrace : WordTrace (prefixWord ++ tailWord_769074) baseStart_769074 baseEnd_769074 := by
    simpa [prefixWord, tailWord_769074, baseEnd_769074] using wordTrace_append hprefix tailTrace_769074
  have hstable : (prefixWord ++ tailWord_769074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769074).length < 2 ^ (prefixWord ++ tailWord_769074).sum := by decide
  have hdescent : baseEnd_769074 < baseStart_769074 := by decide
  rcases family_descends (prefixWord ++ tailWord_769074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769077 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_769077 : Nat := 118140960795 + 769077 * 2 ^ 59
def prefixEnd_769077 : Nat := 4983230072969 + 3 ^ 40 * 769077 * 2
def baseEnd_769077 : Nat := 394906161317992716400585

theorem tailTrace_769077 : CollatzResearch.WordTrace tailWord_769077 prefixEnd_769077 394906161317992716400585 := by
  unfold tailWord_769077
  simp only [CollatzResearch.WordTrace]
  refine ⟨28050542634772851739569485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18700361756515234493046323 28050542634772851739569485)
  ·
    refine ⟨10518953488039819402338557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28050542634772851739569485 10518953488039819402338557)
    ·
      refine ⟨3944607558014932275876959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10518953488039819402338557 3944607558014932275876959)
      ·
        refine ⟨5916911337022398413815439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3944607558014932275876959 5916911337022398413815439)
        ·
          refine ⟨8875367005533597620723159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5916911337022398413815439 8875367005533597620723159)
          ·
            refine ⟨13313050508300396431084739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8875367005533597620723159 13313050508300396431084739)
            ·
              refine ⟨19969575762450594646627109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13313050508300396431084739 19969575762450594646627109)
              ·
                refine ⟨3744295455459486496242583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19969575762450594646627109 3744295455459486496242583)
                ·
                  refine ⟨5616443183189229744363875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3744295455459486496242583 5616443183189229744363875)
                  ·
                    refine ⟨8424664774783844616545813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5616443183189229744363875 8424664774783844616545813)
                    ·
                      refine ⟨394906161317992716400585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8424664774783844616545813 394906161317992716400585)
                      ·
                        rfl

theorem cell23_769077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_769077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769077 prefixEnd_769077 := by exact prefixLift 769077
  have htrace : WordTrace (prefixWord ++ tailWord_769077) baseStart_769077 baseEnd_769077 := by
    simpa [prefixWord, tailWord_769077, baseEnd_769077] using wordTrace_append hprefix tailTrace_769077
  have hstable : (prefixWord ++ tailWord_769077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769077).length < 2 ^ (prefixWord ++ tailWord_769077).sum := by decide
  have hdescent : baseEnd_769077 < baseStart_769077 := by decide
  rcases family_descends (prefixWord ++ tailWord_769077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769084 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_769084 : Nat := 118140960795 + 769084 * 2 ^ 59
def prefixEnd_769084 : Nat := 4983230072969 + 3 ^ 40 * 769084 * 2
def baseEnd_769084 : Nat := 394909755682574189013053

theorem tailTrace_769084 : CollatzResearch.WordTrace tailWord_769084 prefixEnd_769084 394909755682574189013053 := by
  unfold tailWord_769084
  simp only [CollatzResearch.WordTrace]
  refine ⟨14025398972873745967537153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18700531963831661290049537 14025398972873745967537153)
  ·
    refine ⟨10519049229655309475652865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14025398972873745967537153 10519049229655309475652865)
    ·
      refine ⟨7889286922241482106739649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10519049229655309475652865 7889286922241482106739649)
      ·
        refine ⟨5916965191681111580054737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7889286922241482106739649 5916965191681111580054737)
        ·
          refine ⟨4437723893760833685041053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5916965191681111580054737 4437723893760833685041053)
          ·
            refine ⟨1664146460160312631890395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4437723893760833685041053 1664146460160312631890395)
            ·
              refine ⟨2496219690240468947835593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664146460160312631890395 2496219690240468947835593)
              ·
                refine ⟨1872164767680351710876695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2496219690240468947835593 1872164767680351710876695)
                ·
                  refine ⟨2808247151520527566315043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872164767680351710876695 2808247151520527566315043)
                  ·
                    refine ⟨4212370727280791349472565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2808247151520527566315043 4212370727280791349472565)
                    ·
                      refine ⟨394909755682574189013053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4212370727280791349472565 394909755682574189013053)
                      ·
                        rfl

theorem cell23_769084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_769084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769084 prefixEnd_769084 := by exact prefixLift 769084
  have htrace : WordTrace (prefixWord ++ tailWord_769084) baseStart_769084 baseEnd_769084 := by
    simpa [prefixWord, tailWord_769084, baseEnd_769084] using wordTrace_append hprefix tailTrace_769084
  have hstable : (prefixWord ++ tailWord_769084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769084).length < 2 ^ (prefixWord ++ tailWord_769084).sum := by decide
  have hdescent : baseEnd_769084 < baseStart_769084 := by decide
  rcases family_descends (prefixWord ++ tailWord_769084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769091 : List Nat := [1, 1, 1, 3, 1, 2, 7, 1, 2, 4]
def baseStart_769091 : Nat := 118140960795 + 769091 * 2 ^ 59
def prefixEnd_769091 : Nat := 4983230072969 + 3 ^ 40 * 769091 * 2
def baseEnd_769091 : Nat := 131637783349051887208507

theorem tailTrace_769091 : CollatzResearch.WordTrace tailWord_769091 prefixEnd_769091 131637783349051887208507 := by
  unfold tailWord_769091
  simp only [CollatzResearch.WordTrace]
  refine ⟨28051053256722132130579127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18700702171148088087052751 28051053256722132130579127)
  ·
    refine ⟨42076579885083198195868691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28051053256722132130579127 42076579885083198195868691)
    ·
      refine ⟨63114869827624797293803037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42076579885083198195868691 63114869827624797293803037)
      ·
        refine ⟨23668076185359298985176139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63114869827624797293803037 23668076185359298985176139)
        ·
          refine ⟨35502114278038948477764209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23668076185359298985176139 35502114278038948477764209)
          ·
            refine ⟨26626585708529211358323157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35502114278038948477764209 26626585708529211358323157)
            ·
              refine ⟨624060602543653391210699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26626585708529211358323157 624060602543653391210699)
              ·
                refine ⟨936090903815480086816049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624060602543653391210699 936090903815480086816049)
                ·
                  refine ⟨702068177861610065112037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 936090903815480086816049 702068177861610065112037)
                  ·
                    refine ⟨131637783349051887208507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 702068177861610065112037 131637783349051887208507)
                    ·
                      rfl

theorem cell23_769091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 2, 4].length) (baseStart_769091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769091 prefixEnd_769091 := by exact prefixLift 769091
  have htrace : WordTrace (prefixWord ++ tailWord_769091) baseStart_769091 baseEnd_769091 := by
    simpa [prefixWord, tailWord_769091, baseEnd_769091] using wordTrace_append hprefix tailTrace_769091
  have hstable : (prefixWord ++ tailWord_769091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769091).length < 2 ^ (prefixWord ++ tailWord_769091).sum := by decide
  have hdescent : baseEnd_769091 < baseStart_769091 := by decide
  rcases family_descends (prefixWord ++ tailWord_769091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769118 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_769118 : Nat := 118140960795 + 769118 * 2 ^ 59
def prefixEnd_769118 : Nat := 4983230072969 + 3 ^ 40 * 769118 * 2
def baseEnd_769118 : Nat := 394927214024827055987897

theorem tailTrace_769118 : CollatzResearch.WordTrace tailWord_769118 prefixEnd_769118 394927214024827055987897 := by
  unfold tailWord_769118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3506504753453039467726501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18701358685082877161208005 3506504753453039467726501)
  ·
    refine ⟨657469641272444900198719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3506504753453039467726501 657469641272444900198719)
    ·
      refine ⟨986204461908667350298079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 657469641272444900198719 986204461908667350298079)
      ·
        refine ⟨1479306692863001025447119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 986204461908667350298079 1479306692863001025447119)
        ·
          refine ⟨2218960039294501538170679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1479306692863001025447119 2218960039294501538170679)
          ·
            refine ⟨3328440058941752307256019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218960039294501538170679 3328440058941752307256019)
            ·
              refine ⟨4992660088412628460884029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328440058941752307256019 4992660088412628460884029)
              ·
                refine ⟨1872247533154735672831511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4992660088412628460884029 1872247533154735672831511)
                ·
                  refine ⟨2808371299732103509247267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872247533154735672831511 2808371299732103509247267)
                  ·
                    refine ⟨4212556949598155263870901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2808371299732103509247267 4212556949598155263870901)
                    ·
                      refine ⟨394927214024827055987897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4212556949598155263870901 394927214024827055987897)
                      ·
                        rfl

theorem cell23_769118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_769118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769118 prefixEnd_769118 := by exact prefixLift 769118
  have htrace : WordTrace (prefixWord ++ tailWord_769118) baseStart_769118 baseEnd_769118 := by
    simpa [prefixWord, tailWord_769118, baseEnd_769118] using wordTrace_append hprefix tailTrace_769118
  have hstable : (prefixWord ++ tailWord_769118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769118).length < 2 ^ (prefixWord ++ tailWord_769118).sum := by decide
  have hdescent : baseEnd_769118 < baseStart_769118 := by decide
  rcases family_descends (prefixWord ++ tailWord_769118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769147 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 2, 6]
def baseStart_769147 : Nat := 118140960795 + 769147 * 2 ^ 59
def prefixEnd_769147 : Nat := 4983230072969 + 3 ^ 40 * 769147 * 2
def baseEnd_769147 : Nat := 131647368321269147508421

theorem tailTrace_769147 : CollatzResearch.WordTrace tailWord_769147 prefixEnd_769147 131647368321269147508421 := by
  unfold tailWord_769147
  simp only [CollatzResearch.WordTrace]
  refine ⟨28053095744519253694617695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18702063829679502463078463 28053095744519253694617695)
  ·
    refine ⟨42079643616778880541926543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28053095744519253694617695 42079643616778880541926543)
    ·
      refine ⟨63119465425168320812889815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42079643616778880541926543 63119465425168320812889815)
      ·
        refine ⟨94679198137752481219334723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63119465425168320812889815 94679198137752481219334723)
        ·
          refine ⟨142018797206628721829002085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94679198137752481219334723 142018797206628721829002085)
          ·
            refine ⟨26628524476242885342937891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142018797206628721829002085 26628524476242885342937891)
            ·
              refine ⟨39942786714364328014406837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26628524476242885342937891 39942786714364328014406837)
              ·
                refine ⟨3744636254471655751350641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39942786714364328014406837 3744636254471655751350641)
                ·
                  refine ⟨2808477190853741813512981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3744636254471655751350641 2808477190853741813512981)
                  ·
                    refine ⟨131647368321269147508421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2808477190853741813512981 131647368321269147508421)
                    ·
                      rfl

theorem cell23_769147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 6].length) (baseStart_769147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769147 prefixEnd_769147 := by exact prefixLift 769147
  have htrace : WordTrace (prefixWord ++ tailWord_769147) baseStart_769147 baseEnd_769147 := by
    simpa [prefixWord, tailWord_769147, baseEnd_769147] using wordTrace_append hprefix tailTrace_769147
  have hstable : (prefixWord ++ tailWord_769147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769147).length < 2 ^ (prefixWord ++ tailWord_769147).sum := by decide
  have hdescent : baseEnd_769147 < baseStart_769147 := by decide
  rcases family_descends (prefixWord ++ tailWord_769147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769171 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 6, 2, 2]
def baseStart_769171 : Nat := 118140960795 + 769171 * 2 ^ 59
def prefixEnd_769171 : Nat := 4983230072969 + 3 ^ 40 * 769171 * 2
def baseEnd_769171 : Nat := 394954428499515348625153

theorem tailTrace_769171 : CollatzResearch.WordTrace tailWord_769171 prefixEnd_769171 394954428499515348625153 := by
  unfold tailWord_769171
  simp only [CollatzResearch.WordTrace]
  refine ⟨28053971096432305793491367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18702647397621537195660911 28053971096432305793491367)
  ·
    refine ⟨42080956644648458690237051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28053971096432305793491367 42080956644648458690237051)
    ·
      refine ⟨63121434966972688035355577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42080956644648458690237051 63121434966972688035355577)
      ·
        refine ⟨47341076225229516026516683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63121434966972688035355577 47341076225229516026516683)
        ·
          refine ⟨71011614337844274039775025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47341076225229516026516683 71011614337844274039775025)
          ·
            refine ⟨53258710753383205529831269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71011614337844274039775025 53258710753383205529831269)
            ·
              refine ⟨9986008266259351036843363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53258710753383205529831269 9986008266259351036843363)
              ·
                refine ⟨14979012399389026555265045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9986008266259351036843363 14979012399389026555265045)
                ·
                  refine ⟨702141206221360619778049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14979012399389026555265045 702141206221360619778049)
                  ·
                    refine ⟨526605904666020464833537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 702141206221360619778049 526605904666020464833537)
                    ·
                      refine ⟨394954428499515348625153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 526605904666020464833537 394954428499515348625153)
                      ·
                        rfl

theorem cell23_769171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 2, 2].length) (baseStart_769171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769171 prefixEnd_769171 := by exact prefixLift 769171
  have htrace : WordTrace (prefixWord ++ tailWord_769171) baseStart_769171 baseEnd_769171 := by
    simpa [prefixWord, tailWord_769171, baseEnd_769171] using wordTrace_append hprefix tailTrace_769171
  have hstable : (prefixWord ++ tailWord_769171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769171).length < 2 ^ (prefixWord ++ tailWord_769171).sum := by decide
  have hdescent : baseEnd_769171 < baseStart_769171 := by decide
  rcases family_descends (prefixWord ++ tailWord_769171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769175 : List Nat := [1, 1, 3, 3, 3, 2, 3, 1, 1, 3, 2]
def baseStart_769175 : Nat := 118140960795 + 769175 * 2 ^ 59
def prefixEnd_769175 : Nat := 4983230072969 + 3 ^ 40 * 769175 * 2
def baseEnd_769175 : Nat := 394956482422133332975135

theorem tailTrace_769175 : CollatzResearch.WordTrace tailWord_769175 prefixEnd_769175 394956482422133332975135 := by
  unfold tailWord_769175
  simp only [CollatzResearch.WordTrace]
  refine ⟨28054116988417814476636979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18702744658945209651091319 28054116988417814476636979)
  ·
    refine ⟨42081175482626721714955469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28054116988417814476636979 42081175482626721714955469)
    ·
      refine ⟨15780440805985020643108301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42081175482626721714955469 15780440805985020643108301)
      ·
        refine ⟨5917665302244382741165613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15780440805985020643108301 5917665302244382741165613)
        ·
          refine ⟨2219124488341643527937105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5917665302244382741165613 2219124488341643527937105)
          ·
            refine ⟨1664343366256232645952829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2219124488341643527937105 1664343366256232645952829)
            ·
              refine ⟨624128762346087242232311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1664343366256232645952829 624128762346087242232311)
              ·
                refine ⟨936193143519130863348467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624128762346087242232311 936193143519130863348467)
                ·
                  refine ⟨1404289715278696295022701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 936193143519130863348467 1404289715278696295022701)
                  ·
                    refine ⟨526608643229511110633513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1404289715278696295022701 526608643229511110633513)
                    ·
                      refine ⟨394956482422133332975135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 526608643229511110633513 394956482422133332975135)
                      ·
                        rfl

theorem cell23_769175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_769175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769175 prefixEnd_769175 := by exact prefixLift 769175
  have htrace : WordTrace (prefixWord ++ tailWord_769175) baseStart_769175 baseEnd_769175 := by
    simpa [prefixWord, tailWord_769175, baseEnd_769175] using wordTrace_append hprefix tailTrace_769175
  have hstable : (prefixWord ++ tailWord_769175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769175).length < 2 ^ (prefixWord ++ tailWord_769175).sum := by decide
  have hdescent : baseEnd_769175 < baseStart_769175 := by decide
  rcases family_descends (prefixWord ++ tailWord_769175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769184 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 4]
def baseStart_769184 : Nat := 118140960795 + 769184 * 2 ^ 59
def prefixEnd_769184 : Nat := 4983230072969 + 3 ^ 40 * 769184 * 2
def baseEnd_769184 : Nat := 394961103748023797762593

theorem tailTrace_769184 : CollatzResearch.WordTrace tailWord_769184 prefixEnd_769184 394961103748023797762593 := by
  unfold tailWord_769184
  simp only [CollatzResearch.WordTrace]
  refine ⟨14027222622692604506857303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18702963496923472675809737 14027222622692604506857303)
  ·
    refine ⟨21040833934038906760285955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14027222622692604506857303 21040833934038906760285955)
    ·
      refine ⟨31561250901058360140428933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21040833934038906760285955 31561250901058360140428933)
      ·
        refine ⟨5917734543948442526330425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31561250901058360140428933 5917734543948442526330425)
        ·
          refine ⟨4438300907961331894747819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5917734543948442526330425 4438300907961331894747819)
          ·
            refine ⟨6657451361941997842121729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438300907961331894747819 6657451361941997842121729)
            ·
              refine ⟨4993088521456498381591297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6657451361941997842121729 4993088521456498381591297)
              ·
                refine ⟨3744816391092373786193473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4993088521456498381591297 3744816391092373786193473)
                ·
                  refine ⟨2808612293319280339645105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3744816391092373786193473 2808612293319280339645105)
                  ·
                    refine ⟨2106459219989460254733829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2808612293319280339645105 2106459219989460254733829)
                    ·
                      refine ⟨394961103748023797762593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2106459219989460254733829 394961103748023797762593)
                      ·
                        rfl

theorem cell23_769184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_769184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769184 prefixEnd_769184 := by exact prefixLift 769184
  have htrace : WordTrace (prefixWord ++ tailWord_769184) baseStart_769184 baseEnd_769184 := by
    simpa [prefixWord, tailWord_769184, baseEnd_769184] using wordTrace_append hprefix tailTrace_769184
  have hstable : (prefixWord ++ tailWord_769184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769184).length < 2 ^ (prefixWord ++ tailWord_769184).sum := by decide
  have hdescent : baseEnd_769184 < baseStart_769184 := by decide
  rcases family_descends (prefixWord ++ tailWord_769184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769187 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 7]
def baseStart_769187 : Nat := 118140960795 + 769187 * 2 ^ 59
def prefixEnd_769187 : Nat := 4983230072969 + 3 ^ 40 * 769187 * 2
def baseEnd_769187 : Nat := 394962644189987286025079

theorem tailTrace_769187 : CollatzResearch.WordTrace tailWord_769187 prefixEnd_769187 394962644189987286025079 := by
  unfold tailWord_769187
  simp only [CollatzResearch.WordTrace]
  refine ⟨28054554664374340526073815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18703036442916227017382543 28054554664374340526073815)
  ·
    refine ⟨42081831996561510789110723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28054554664374340526073815 42081831996561510789110723)
    ·
      refine ⟨63122747994842266183666085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42081831996561510789110723 63122747994842266183666085)
      ·
        refine ⟨11835515249032924909437391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63122747994842266183666085 11835515249032924909437391)
        ·
          refine ⟨17753272873549387364156087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11835515249032924909437391 17753272873549387364156087)
          ·
            refine ⟨26629909310324081046234131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17753272873549387364156087 26629909310324081046234131)
            ·
              refine ⟨39944863965486121569351197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26629909310324081046234131 39944863965486121569351197)
              ·
                refine ⟨14979323987057295588506699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39944863965486121569351197 14979323987057295588506699)
                ·
                  refine ⟨22468985980585943382760049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14979323987057295588506699 22468985980585943382760049)
                  ·
                    refine ⟨16851739485439457537070037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22468985980585943382760049 16851739485439457537070037)
                    ·
                      refine ⟨394962644189987286025079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16851739485439457537070037 394962644189987286025079)
                      ·
                        rfl

theorem cell23_769187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_769187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769187 prefixEnd_769187 := by exact prefixLift 769187
  have htrace : WordTrace (prefixWord ++ tailWord_769187) baseStart_769187 baseEnd_769187 := by
    simpa [prefixWord, tailWord_769187, baseEnd_769187] using wordTrace_append hprefix tailTrace_769187
  have hstable : (prefixWord ++ tailWord_769187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769187).length < 2 ^ (prefixWord ++ tailWord_769187).sum := by decide
  have hdescent : baseEnd_769187 < baseStart_769187 := by decide
  rcases family_descends (prefixWord ++ tailWord_769187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769191 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_769191 : Nat := 118140960795 + 769191 * 2 ^ 59
def prefixEnd_769191 : Nat := 4983230072969 + 3 ^ 40 * 769191 * 2
def baseEnd_769191 : Nat := 394964698112605270375061

theorem tailTrace_769191 : CollatzResearch.WordTrace tailWord_769191 prefixEnd_769191 394964698112605270375061 := by
  unfold tailWord_769191
  simp only [CollatzResearch.WordTrace]
  refine ⟨28054700556359849209219427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18703133704239899472812951 28054700556359849209219427)
  ·
    refine ⟨42082050834539773813829141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28054700556359849209219427 42082050834539773813829141)
    ·
      refine ⟨1972596132869051897523241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42082050834539773813829141 1972596132869051897523241)
      ·
        refine ⟨1479447099651788923142431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1972596132869051897523241 1479447099651788923142431)
        ·
          refine ⟨2219170649477683384713647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1479447099651788923142431 2219170649477683384713647)
          ·
            refine ⟨3328755974216525077070471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2219170649477683384713647 3328755974216525077070471)
            ·
              refine ⟨4993133961324787615605707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328755974216525077070471 4993133961324787615605707)
              ·
                refine ⟨7489700941987181423408561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4993133961324787615605707 7489700941987181423408561)
                ·
                  refine ⟨5617275706490386067556421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7489700941987181423408561 5617275706490386067556421)
                  ·
                    refine ⟨1053239194966947387666829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5617275706490386067556421 1053239194966947387666829)
                    ·
                      refine ⟨394964698112605270375061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1053239194966947387666829 394964698112605270375061)
                      ·
                        rfl

theorem cell23_769191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_769191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769191 prefixEnd_769191 := by exact prefixLift 769191
  have htrace : WordTrace (prefixWord ++ tailWord_769191) baseStart_769191 baseEnd_769191 := by
    simpa [prefixWord, tailWord_769191, baseEnd_769191] using wordTrace_append hprefix tailTrace_769191
  have hstable : (prefixWord ++ tailWord_769191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769191).length < 2 ^ (prefixWord ++ tailWord_769191).sum := by decide
  have hdescent : baseEnd_769191 < baseStart_769191 := by decide
  rcases family_descends (prefixWord ++ tailWord_769191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769201 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_769201 : Nat := 118140960795 + 769201 * 2 ^ 59
def prefixEnd_769201 : Nat := 4983230072969 + 3 ^ 40 * 769201 * 2
def baseEnd_769201 : Nat := 394969832919150231250015

theorem tailTrace_769201 : CollatzResearch.WordTrace tailWord_769201 prefixEnd_769201 394969832919150231250015 := by
  unfold tailWord_769201
  simp only [CollatzResearch.WordTrace]
  refine ⟨28055065286323620917083457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18703376857549080611388971 28055065286323620917083457)
  ·
    refine ⟨21041298964742715687812593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28055065286323620917083457 21041298964742715687812593)
    ·
      refine ⟨15780974223557036765859445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21041298964742715687812593 15780974223557036765859445)
      ·
        refine ⟨1479466333458472196799323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15780974223557036765859445 1479466333458472196799323)
        ·
          refine ⟨2219199500187708295198985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1479466333458472196799323 2219199500187708295198985)
          ·
            refine ⟨1664399625140781221399239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2219199500187708295198985 1664399625140781221399239)
            ·
              refine ⟨2496599437711171832098859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664399625140781221399239 2496599437711171832098859)
              ·
                refine ⟨3744899156566757748148289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496599437711171832098859 3744899156566757748148289)
                ·
                  refine ⟨2808674367425068311111217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3744899156566757748148289 2808674367425068311111217)
                  ·
                    refine ⟨2106505775568801233333413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2808674367425068311111217 2106505775568801233333413)
                    ·
                      refine ⟨394969832919150231250015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2106505775568801233333413 394969832919150231250015)
                      ·
                        rfl

theorem cell23_769201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_769201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769201 prefixEnd_769201 := by exact prefixLift 769201
  have htrace : WordTrace (prefixWord ++ tailWord_769201) baseStart_769201 baseEnd_769201 := by
    simpa [prefixWord, tailWord_769201, baseEnd_769201] using wordTrace_append hprefix tailTrace_769201
  have hstable : (prefixWord ++ tailWord_769201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769201).length < 2 ^ (prefixWord ++ tailWord_769201).sum := by decide
  have hdescent : baseEnd_769201 < baseStart_769201 := by decide
  rcases family_descends (prefixWord ++ tailWord_769201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769261 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_769261 : Nat := 118140960795 + 769261 * 2 ^ 59
def prefixEnd_769261 : Nat := 4983230072969 + 3 ^ 40 * 769261 * 2
def baseEnd_769261 : Nat := 395000641758419996499739

theorem tailTrace_769261 : CollatzResearch.WordTrace tailWord_769261 prefixEnd_769261 395000641758419996499739 := by
  unfold tailWord_769261
  simp only [CollatzResearch.WordTrace]
  refine ⟨28057253666106251164267637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18704835777404167442845091 28057253666106251164267637)
  ·
    refine ⟨2630367531197461046650091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28057253666106251164267637 2630367531197461046650091)
    ·
      refine ⟨3945551296796191569975137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2630367531197461046650091 3945551296796191569975137)
      ·
        refine ⟨2959163472597143677481353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3945551296796191569975137 2959163472597143677481353)
        ·
          refine ⟨2219372604447857758111015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2959163472597143677481353 2219372604447857758111015)
          ·
            refine ⟨3329058906671786637166523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2219372604447857758111015 3329058906671786637166523)
            ·
              refine ⟨4993588360007679955749785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3329058906671786637166523 4993588360007679955749785)
              ·
                refine ⟨3745191270005759966812339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4993588360007679955749785 3745191270005759966812339)
                ·
                  refine ⟨5617786905008639950218509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3745191270005759966812339 5617786905008639950218509)
                  ·
                    refine ⟨2106670089378239981331941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5617786905008639950218509 2106670089378239981331941)
                    ·
                      refine ⟨395000641758419996499739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2106670089378239981331941 395000641758419996499739)
                      ·
                        rfl

theorem cell23_769261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_769261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769261 prefixEnd_769261 := by exact prefixLift 769261
  have htrace : WordTrace (prefixWord ++ tailWord_769261) baseStart_769261 baseEnd_769261 := by
    simpa [prefixWord, tailWord_769261, baseEnd_769261] using wordTrace_append hprefix tailTrace_769261
  have hstable : (prefixWord ++ tailWord_769261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769261).length < 2 ^ (prefixWord ++ tailWord_769261).sum := by decide
  have hdescent : baseEnd_769261 < baseStart_769261 := by decide
  rcases family_descends (prefixWord ++ tailWord_769261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769274 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_769274 : Nat := 118140960795 + 769274 * 2 ^ 59
def prefixEnd_769274 : Nat := 4983230072969 + 3 ^ 40 * 769274 * 2
def baseEnd_769274 : Nat := 395007317006928445637179

theorem tailTrace_769274 : CollatzResearch.WordTrace tailWord_769274 prefixEnd_769274 395007317006928445637179 := by
  unfold tailWord_769274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7014431953764788596122719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18705151876706102922993917 7014431953764788596122719)
  ·
    refine ⟨10521647930647182894184079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7014431953764788596122719 10521647930647182894184079)
    ·
      refine ⟨15782471895970774341276119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10521647930647182894184079 15782471895970774341276119)
      ·
        refine ⟨23673707843956161511914179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15782471895970774341276119 23673707843956161511914179)
        ·
          refine ⟨35510561765934242267871269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23673707843956161511914179 35510561765934242267871269)
          ·
            refine ⟨6658230331112670425225863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35510561765934242267871269 6658230331112670425225863)
            ·
              refine ⟨9987345496669005637838795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6658230331112670425225863 9987345496669005637838795)
              ·
                refine ⟨14981018245003508456758193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9987345496669005637838795 14981018245003508456758193)
                ·
                  refine ⟨11235763683752631342568645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14981018245003508456758193 11235763683752631342568645)
                  ·
                    refine ⟨2106705690703618376731621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11235763683752631342568645 2106705690703618376731621)
                    ·
                      refine ⟨395007317006928445637179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2106705690703618376731621 395007317006928445637179)
                      ·
                        rfl

theorem cell23_769274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_769274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769274 prefixEnd_769274 := by exact prefixLift 769274
  have htrace : WordTrace (prefixWord ++ tailWord_769274) baseStart_769274 baseEnd_769274 := by
    simpa [prefixWord, tailWord_769274, baseEnd_769274] using wordTrace_append hprefix tailTrace_769274
  have hstable : (prefixWord ++ tailWord_769274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769274).length < 2 ^ (prefixWord ++ tailWord_769274).sum := by decide
  have hdescent : baseEnd_769274 < baseStart_769274 := by decide
  rcases family_descends (prefixWord ++ tailWord_769274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769281 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_769281 : Nat := 118140960795 + 769281 * 2 ^ 59
def prefixEnd_769281 : Nat := 4983230072969 + 3 ^ 40 * 769281 * 2
def baseEnd_769281 : Nat := 395010911371509918249647

theorem tailTrace_769281 : CollatzResearch.WordTrace tailWord_769281 prefixEnd_769281 395010911371509918249647 := by
  unfold tailWord_769281
  simp only [CollatzResearch.WordTrace]
  refine ⟨28057983126033794579995697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18705322084022529719997131 28057983126033794579995697)
  ·
    refine ⟨21043487344525345934996773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28057983126033794579995697 21043487344525345934996773)
    ·
      refine ⟨3945653877098502362811895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21043487344525345934996773 3945653877098502362811895)
      ·
        refine ⟨5918480815647753544217843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3945653877098502362811895 5918480815647753544217843)
        ·
          refine ⟨8877721223471630316326765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5918480815647753544217843 8877721223471630316326765)
          ·
            refine ⟨3329145458801861368622537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8877721223471630316326765 3329145458801861368622537)
            ·
              refine ⟨2496859094101396026466903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3329145458801861368622537 2496859094101396026466903)
              ·
                refine ⟨3745288641152094039700355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496859094101396026466903 3745288641152094039700355)
                ·
                  refine ⟨5617932961728141059550533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3745288641152094039700355 5617932961728141059550533)
                  ·
                    refine ⟨1053362430324026448665725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5617932961728141059550533 1053362430324026448665725)
                    ·
                      refine ⟨395010911371509918249647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1053362430324026448665725 395010911371509918249647)
                      ·
                        rfl

theorem cell23_769281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_769281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769281 prefixEnd_769281 := by exact prefixLift 769281
  have htrace : WordTrace (prefixWord ++ tailWord_769281) baseStart_769281 baseEnd_769281 := by
    simpa [prefixWord, tailWord_769281, baseEnd_769281] using wordTrace_append hprefix tailTrace_769281
  have hstable : (prefixWord ++ tailWord_769281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769281).length < 2 ^ (prefixWord ++ tailWord_769281).sum := by decide
  have hdescent : baseEnd_769281 < baseStart_769281 := by decide
  rcases family_descends (prefixWord ++ tailWord_769281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769331 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 3, 5]
def baseStart_769331 : Nat := 118140960795 + 769331 * 2 ^ 59
def prefixEnd_769331 : Nat := 4983230072969 + 3 ^ 40 * 769331 * 2
def baseEnd_769331 : Nat := 131678861801411574208139

theorem tailTrace_769331 : CollatzResearch.WordTrace tailWord_769331 prefixEnd_769331 131678861801411574208139 := by
  unfold tailWord_769331
  simp only [CollatzResearch.WordTrace]
  refine ⟨28059806775852653119315847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18706537850568435412877231 28059806775852653119315847)
  ·
    refine ⟨42089710163778979678973771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28059806775852653119315847 42089710163778979678973771)
    ·
      refine ⟨63134565245668469518460657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42089710163778979678973771 63134565245668469518460657)
      ·
        refine ⟨47350923934251352138845493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63134565245668469518460657 47350923934251352138845493)
        ·
          refine ⟨4439149118836064263016765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47350923934251352138845493 4439149118836064263016765)
          ·
            refine ⟨1664680919563524098631287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4439149118836064263016765 1664680919563524098631287)
            ·
              refine ⟨2497021379345286147946931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664680919563524098631287 2497021379345286147946931)
              ·
                refine ⟨3745532069017929221920397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497021379345286147946931 3745532069017929221920397)
                ·
                  refine ⟨1404574525881723458220149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3745532069017929221920397 1404574525881723458220149)
                  ·
                    refine ⟨131678861801411574208139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1404574525881723458220149 131678861801411574208139)
                    ·
                      rfl

theorem cell23_769331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 5].length) (baseStart_769331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769331 prefixEnd_769331 := by exact prefixLift 769331
  have htrace : WordTrace (prefixWord ++ tailWord_769331) baseStart_769331 baseEnd_769331 := by
    simpa [prefixWord, tailWord_769331, baseEnd_769331] using wordTrace_append hprefix tailTrace_769331
  have hstable : (prefixWord ++ tailWord_769331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769331).length < 2 ^ (prefixWord ++ tailWord_769331).sum := by decide
  have hdescent : baseEnd_769331 < baseStart_769331 := by decide
  rcases family_descends (prefixWord ++ tailWord_769331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769378 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_769378 : Nat := 118140960795 + 769378 * 2 ^ 59
def prefixEnd_769378 : Nat := 4983230072969 + 3 ^ 40 * 769378 * 2
def baseEnd_769378 : Nat := 131686906331665346245567

theorem tailTrace_769378 : CollatzResearch.WordTrace tailWord_769378 prefixEnd_769378 131686906331665346245567 := by
  unfold tailWord_769378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7015380251670595036569197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18707680671121586764184525 7015380251670595036569197)
  ·
    refine ⟨2630767594376473138713449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7015380251670595036569197 2630767594376473138713449)
    ·
      refine ⟨1973075695782354854035087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2630767594376473138713449 1973075695782354854035087)
      ·
        refine ⟨2959613543673532281052631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1973075695782354854035087 2959613543673532281052631)
        ·
          refine ⟨4439420315510298421578947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2959613543673532281052631 4439420315510298421578947)
          ·
            refine ⟨6659130473265447632368421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4439420315510298421578947 6659130473265447632368421)
            ·
              refine ⟨1248586963737271431069079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6659130473265447632368421 1248586963737271431069079)
              ·
                refine ⟨1872880445605907146603619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1248586963737271431069079 1872880445605907146603619)
                ·
                  refine ⟨2809320668408860719905429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872880445605907146603619 2809320668408860719905429)
                  ·
                    refine ⟨131686906331665346245567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2809320668408860719905429 131686906331665346245567)
                    ·
                      rfl

theorem cell23_769378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_769378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769378 prefixEnd_769378 := by exact prefixLift 769378
  have htrace : WordTrace (prefixWord ++ tailWord_769378) baseStart_769378 baseEnd_769378 := by
    simpa [prefixWord, tailWord_769378, baseEnd_769378] using wordTrace_append hprefix tailTrace_769378
  have hstable : (prefixWord ++ tailWord_769378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769378).length < 2 ^ (prefixWord ++ tailWord_769378).sum := by decide
  have hdescent : baseEnd_769378 < baseStart_769378 := by decide
  rcases family_descends (prefixWord ++ tailWord_769378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769388 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 3]
def baseStart_769388 : Nat := 118140960795 + 769388 * 2 ^ 59
def prefixEnd_769388 : Nat := 4983230072969 + 3 ^ 40 * 769388 * 2
def baseEnd_769388 : Nat := 395065853801540999611655

theorem tailTrace_769388 : CollatzResearch.WordTrace tailWord_769388 prefixEnd_769388 395065853801540999611655 := by
  unfold tailWord_769388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14030942868323075927070409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18707923824430767902760545 14030942868323075927070409)
  ·
    refine ⟨10523207151242306945302807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14030942868323075927070409 10523207151242306945302807)
    ·
      refine ⟨15784810726863460417954211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10523207151242306945302807 15784810726863460417954211)
      ·
        refine ⟨23677216090295190626931317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15784810726863460417954211 23677216090295190626931317)
        ·
          refine ⟨2219739008465174121274811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23677216090295190626931317 2219739008465174121274811)
          ·
            refine ⟨3329608512697761181912217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2219739008465174121274811 3329608512697761181912217)
            ·
              refine ⟨2497206384523320886434163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3329608512697761181912217 2497206384523320886434163)
              ·
                refine ⟨3745809576784981329651245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497206384523320886434163 3745809576784981329651245)
                ·
                  refine ⟨1404678591294367998619217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3745809576784981329651245 1404678591294367998619217)
                  ·
                    refine ⟨1053508943470775998964413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1404678591294367998619217 1053508943470775998964413)
                    ·
                      refine ⟨395065853801540999611655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1053508943470775998964413 395065853801540999611655)
                      ·
                        rfl

theorem cell23_769388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_769388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769388 prefixEnd_769388 := by exact prefixLift 769388
  have htrace : WordTrace (prefixWord ++ tailWord_769388) baseStart_769388 baseEnd_769388 := by
    simpa [prefixWord, tailWord_769388, baseEnd_769388] using wordTrace_append hprefix tailTrace_769388
  have hstable : (prefixWord ++ tailWord_769388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769388).length < 2 ^ (prefixWord ++ tailWord_769388).sum := by decide
  have hdescent : baseEnd_769388 < baseStart_769388 := by decide
  rcases family_descends (prefixWord ++ tailWord_769388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769391 : List Nat := [1, 1, 2, 1, 3, 1, 7, 7]
def baseStart_769391 : Nat := 118140960795 + 769391 * 2 ^ 59
def prefixEnd_769391 : Nat := 4983230072969 + 3 ^ 40 * 769391 * 2
def baseEnd_769391 : Nat := 14632125712722388439783

theorem tailTrace_769391 : CollatzResearch.WordTrace tailWord_769391 prefixEnd_769391 14632125712722388439783 := by
  unfold tailWord_769391
  simp only [CollatzResearch.WordTrace]
  refine ⟨28061995155635283366500027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18707996770423522244333351 28061995155635283366500027)
  ·
    refine ⟨42092992733452925049750041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28061995155635283366500027 42092992733452925049750041)
    ·
      refine ⟨31569744550089693787312531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42092992733452925049750041 31569744550089693787312531)
      ·
        refine ⟨47354616825134540680968797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31569744550089693787312531 47354616825134540680968797)
        ·
          refine ⟨17757981309425452755363299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47354616825134540680968797 17757981309425452755363299)
          ·
            refine ⟨26636971964138179133044949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17757981309425452755363299 26636971964138179133044949)
            ·
              refine ⟨624304030409488573430741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26636971964138179133044949 624304030409488573430741)
              ·
                refine ⟨14632125712722388439783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 624304030409488573430741 14632125712722388439783)
                ·
                  rfl

theorem cell23_769391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 7].length) (baseStart_769391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769391 prefixEnd_769391 := by exact prefixLift 769391
  have htrace : WordTrace (prefixWord ++ tailWord_769391) baseStart_769391 baseEnd_769391 := by
    simpa [prefixWord, tailWord_769391, baseEnd_769391] using wordTrace_append hprefix tailTrace_769391
  have hstable : (prefixWord ++ tailWord_769391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769391).length < 2 ^ (prefixWord ++ tailWord_769391).sum := by decide
  have hdescent : baseEnd_769391 < baseStart_769391 := by decide
  rcases family_descends (prefixWord ++ tailWord_769391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769432 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 1, 2, 4]
def baseStart_769432 : Nat := 118140960795 + 769432 * 2 ^ 59
def prefixEnd_769432 : Nat := 4983230072969 + 3 ^ 40 * 769432 * 2
def baseEnd_769432 : Nat := 395088446950338827461453

theorem tailTrace_769432 : CollatzResearch.WordTrace tailWord_769432 prefixEnd_769432 395088446950338827461453 := by
  unfold tailWord_769432
  simp only [CollatzResearch.WordTrace]
  refine ⟨14031745274243373684371275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18708993698991164912495033 14031745274243373684371275)
  ·
    refine ⟨21047617911365060526556913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14031745274243373684371275 21047617911365060526556913)
    ·
      refine ⟨15785713433523795394917685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21047617911365060526556913 15785713433523795394917685)
      ·
        refine ⟨1479910634392855818273533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15785713433523795394917685 1479910634392855818273533)
        ·
          refine ⟨554966487897320931852575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1479910634392855818273533 554966487897320931852575)
          ·
            refine ⟨832449731845981397778863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554966487897320931852575 832449731845981397778863)
            ·
              refine ⟨1248674597768972096668295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832449731845981397778863 1248674597768972096668295)
              ·
                refine ⟨1873011896653458145002443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1248674597768972096668295 1873011896653458145002443)
                ·
                  refine ⟨2809517844980187217503665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873011896653458145002443 2809517844980187217503665)
                  ·
                    refine ⟨2107138383735140413127749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2809517844980187217503665 2107138383735140413127749)
                    ·
                      refine ⟨395088446950338827461453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2107138383735140413127749 395088446950338827461453)
                      ·
                        rfl

theorem cell23_769432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_769432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769432 prefixEnd_769432 := by exact prefixLift 769432
  have htrace : WordTrace (prefixWord ++ tailWord_769432) baseStart_769432 baseEnd_769432 := by
    simpa [prefixWord, tailWord_769432, baseEnd_769432] using wordTrace_append hprefix tailTrace_769432
  have hstable : (prefixWord ++ tailWord_769432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769432).length < 2 ^ (prefixWord ++ tailWord_769432).sum := by decide
  have hdescent : baseEnd_769432 < baseStart_769432 := by decide
  rcases family_descends (prefixWord ++ tailWord_769432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769471 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 4]
def baseStart_769471 : Nat := 118140960795 + 769471 * 2 ^ 59
def prefixEnd_769471 : Nat := 4983230072969 + 3 ^ 40 * 769471 * 2
def baseEnd_769471 : Nat := 395108472695864174873773

theorem tailTrace_769471 : CollatzResearch.WordTrace tailWord_769471 prefixEnd_769471 395108472695864174873773 := by
  unfold tailWord_769471
  simp only [CollatzResearch.WordTrace]
  refine ⟨28064912995345457029412267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18709941996896971352941511 28064912995345457029412267)
  ·
    refine ⟨42097369493018185544118401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28064912995345457029412267 42097369493018185544118401)
    ·
      refine ⟨31573027119763639158088801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42097369493018185544118401 31573027119763639158088801)
      ·
        refine ⟨23679770339822729368566601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31573027119763639158088801 23679770339822729368566601)
        ·
          refine ⟨17759827754867047026424951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23679770339822729368566601 17759827754867047026424951)
          ·
            refine ⟨26639741632300570539637427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17759827754867047026424951 26639741632300570539637427)
            ·
              refine ⟨39959612448450855809456141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26639741632300570539637427 39959612448450855809456141)
              ·
                refine ⟨14984854668169070928546053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39959612448450855809456141 14984854668169070928546053)
                ·
                  refine ⟨2809660250281700799102385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14984854668169070928546053 2809660250281700799102385)
                  ·
                    refine ⟨2107245187711275599326789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2809660250281700799102385 2107245187711275599326789)
                    ·
                      refine ⟨395108472695864174873773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2107245187711275599326789 395108472695864174873773)
                      ·
                        rfl

theorem cell23_769471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_769471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769471 prefixEnd_769471 := by exact prefixLift 769471
  have htrace : WordTrace (prefixWord ++ tailWord_769471) baseStart_769471 baseEnd_769471 := by
    simpa [prefixWord, tailWord_769471, baseEnd_769471] using wordTrace_append hprefix tailTrace_769471
  have hstable : (prefixWord ++ tailWord_769471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769471).length < 2 ^ (prefixWord ++ tailWord_769471).sum := by decide
  have hdescent : baseEnd_769471 < baseStart_769471 := by decide
  rcases family_descends (prefixWord ++ tailWord_769471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769475 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 4, 2, 2]
def baseStart_769475 : Nat := 118140960795 + 769475 * 2 ^ 59
def prefixEnd_769475 : Nat := 4983230072969 + 3 ^ 40 * 769475 * 2
def baseEnd_769475 : Nat := 395110526618482159223755

theorem tailTrace_769475 : CollatzResearch.WordTrace tailWord_769475 prefixEnd_769475 395110526618482159223755 := by
  unfold tailWord_769475
  simp only [CollatzResearch.WordTrace]
  refine ⟨28065058887330965712557879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18710039258220643808371919 28065058887330965712557879)
  ·
    refine ⟨42097588330996448568836819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28065058887330965712557879 42097588330996448568836819)
    ·
      refine ⟨63146382496494672853255229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42097588330996448568836819 63146382496494672853255229)
      ·
        refine ⟨23679893436185502319970711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63146382496494672853255229 23679893436185502319970711)
        ·
          refine ⟨35519840154278253479956067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23679893436185502319970711 35519840154278253479956067)
          ·
            refine ⟨53279760231417380219934101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35519840154278253479956067 53279760231417380219934101)
            ·
              refine ⟨2497488760847689697809411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53279760231417380219934101 2497488760847689697809411)
              ·
                refine ⟨3746233141271534546714117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497488760847689697809411 3746233141271534546714117)
                ·
                  refine ⟨702418713988412727508897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3746233141271534546714117 702418713988412727508897)
                  ·
                    refine ⟨526814035491309545631673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 702418713988412727508897 526814035491309545631673)
                    ·
                      refine ⟨395110526618482159223755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 526814035491309545631673 395110526618482159223755)
                      ·
                        rfl

theorem cell23_769475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 2, 2].length) (baseStart_769475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769475 prefixEnd_769475 := by exact prefixLift 769475
  have htrace : WordTrace (prefixWord ++ tailWord_769475) baseStart_769475 baseEnd_769475 := by
    simpa [prefixWord, tailWord_769475, baseEnd_769475] using wordTrace_append hprefix tailTrace_769475
  have hstable : (prefixWord ++ tailWord_769475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769475).length < 2 ^ (prefixWord ++ tailWord_769475).sum := by decide
  have hdescent : baseEnd_769475 < baseStart_769475 := by decide
  rcases family_descends (prefixWord ++ tailWord_769475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769528 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 2, 5]
def baseStart_769528 : Nat := 118140960795 + 769528 * 2 ^ 59
def prefixEnd_769528 : Nat := 4983230072969 + 3 ^ 40 * 769528 * 2
def baseEnd_769528 : Nat := 131712580364390150620337

theorem tailTrace_769528 : CollatzResearch.WordTrace tailWord_769528 prefixEnd_769528 131712580364390150620337 := by
  unfold tailWord_769528
  simp only [CollatzResearch.WordTrace]
  refine ⟨14033495978069477882118619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18711327970759303842824825 14033495978069477882118619)
  ·
    refine ⟨21050243967104216823177929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14033495978069477882118619 21050243967104216823177929)
    ·
      refine ⟨15787682975328162617383447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21050243967104216823177929 15787682975328162617383447)
      ·
        refine ⟨23681524462992243926075171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15787682975328162617383447 23681524462992243926075171)
        ·
          refine ⟨35522286694488365889112757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23681524462992243926075171 35522286694488365889112757)
          ·
            refine ⟨3330214377608284302104321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35522286694488365889112757 3330214377608284302104321)
            ·
              refine ⟨2497660783206213226578241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3330214377608284302104321 2497660783206213226578241)
              ·
                refine ⟨1873245587404659919933681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2497660783206213226578241 1873245587404659919933681)
                ·
                  refine ⟨1404934190553494939950261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1873245587404659919933681 1404934190553494939950261)
                  ·
                    refine ⟨131712580364390150620337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1404934190553494939950261 131712580364390150620337)
                    ·
                      rfl

theorem cell23_769528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_769528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769528 prefixEnd_769528 := by exact prefixLift 769528
  have htrace : WordTrace (prefixWord ++ tailWord_769528) baseStart_769528 baseEnd_769528 := by
    simpa [prefixWord, tailWord_769528, baseEnd_769528] using wordTrace_append hprefix tailTrace_769528
  have hstable : (prefixWord ++ tailWord_769528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769528).length < 2 ^ (prefixWord ++ tailWord_769528).sum := by decide
  have hdescent : baseEnd_769528 < baseStart_769528 := by decide
  rcases family_descends (prefixWord ++ tailWord_769528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769541 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 2, 8]
def baseStart_769541 : Nat := 118140960795 + 769541 * 2 ^ 59
def prefixEnd_769541 : Nat := 4983230072969 + 3 ^ 40 * 769541 * 2
def baseEnd_769541 : Nat := 131714805447226300332817

theorem tailTrace_769541 : CollatzResearch.WordTrace tailWord_769541 prefixEnd_769541 131714805447226300332817 := by
  unfold tailWord_769541
  simp only [CollatzResearch.WordTrace]
  refine ⟨28067466105091858984460477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18711644070061239322973651 28067466105091858984460477)
  ·
    refine ⟨10525299789409447119172679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28067466105091858984460477 10525299789409447119172679)
    ·
      refine ⟨15787949684114170678759019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10525299789409447119172679 15787949684114170678759019)
      ·
        refine ⟨23681924526171256018138529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15787949684114170678759019 23681924526171256018138529)
        ·
          refine ⟨17761443394628442013603897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23681924526171256018138529 17761443394628442013603897)
          ·
            refine ⟨13321082545971331510202923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17761443394628442013603897 13321082545971331510202923)
            ·
              refine ⟨19981623818956997265304385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13321082545971331510202923 19981623818956997265304385)
              ·
                refine ⟨14986217864217747948978289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19981623818956997265304385 14986217864217747948978289)
                ·
                  refine ⟨11239663398163310961733717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14986217864217747948978289 11239663398163310961733717)
                  ·
                    refine ⟨131714805447226300332817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11239663398163310961733717 131714805447226300332817)
                    ·
                      rfl

theorem cell23_769541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_769541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769541 prefixEnd_769541 := by exact prefixLift 769541
  have htrace : WordTrace (prefixWord ++ tailWord_769541) baseStart_769541 baseEnd_769541 := by
    simpa [prefixWord, tailWord_769541, baseEnd_769541] using wordTrace_append hprefix tailTrace_769541
  have hstable : (prefixWord ++ tailWord_769541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769541).length < 2 ^ (prefixWord ++ tailWord_769541).sum := by decide
  have hdescent : baseEnd_769541 < baseStart_769541 := by decide
  rcases family_descends (prefixWord ++ tailWord_769541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769551 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 5]
def baseStart_769551 : Nat := 118140960795 + 769551 * 2 ^ 59
def prefixEnd_769551 : Nat := 4983230072969 + 3 ^ 40 * 769551 * 2
def baseEnd_769551 : Nat := 395149551148223861873405

theorem tailTrace_769551 : CollatzResearch.WordTrace tailWord_769551 prefixEnd_769551 395149551148223861873405 := by
  unfold tailWord_769551
  simp only [CollatzResearch.WordTrace]
  refine ⟨28067830835055630692324507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18711887223370420461549671 28067830835055630692324507)
  ·
    refine ⟨42101746252583446038486761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28067830835055630692324507 42101746252583446038486761)
    ·
      refine ⟨31576309689437584528865071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42101746252583446038486761 31576309689437584528865071)
      ·
        refine ⟨47364464534156376793297607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31576309689437584528865071 47364464534156376793297607)
        ·
          refine ⟨71046696801234565189946411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47364464534156376793297607 71046696801234565189946411)
          ·
            refine ⟨106570045201851847784919617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71046696801234565189946411 106570045201851847784919617)
            ·
              refine ⟨79927533901388885838689713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106570045201851847784919617 79927533901388885838689713)
              ·
                refine ⟨59945650426041664379017285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79927533901388885838689713 59945650426041664379017285)
                ·
                  refine ⟨11239809454882812071065741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59945650426041664379017285 11239809454882812071065741)
                  ·
                    refine ⟨4214928545581054526649653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11239809454882812071065741 4214928545581054526649653)
                    ·
                      refine ⟨395149551148223861873405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4214928545581054526649653 395149551148223861873405)
                      ·
                        rfl

theorem cell23_769551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_769551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769551 prefixEnd_769551 := by exact prefixLift 769551
  have htrace : WordTrace (prefixWord ++ tailWord_769551) baseStart_769551 baseEnd_769551 := by
    simpa [prefixWord, tailWord_769551, baseEnd_769551] using wordTrace_append hprefix tailTrace_769551
  have hstable : (prefixWord ++ tailWord_769551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769551).length < 2 ^ (prefixWord ++ tailWord_769551).sum := by decide
  have hdescent : baseEnd_769551 < baseStart_769551 := by decide
  rcases family_descends (prefixWord ++ tailWord_769551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769561 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 6]
def baseStart_769561 : Nat := 118140960795 + 769561 * 2 ^ 59
def prefixEnd_769561 : Nat := 4983230072969 + 3 ^ 40 * 769561 * 2
def baseEnd_769561 : Nat := 395154685954768822748359

theorem tailTrace_769561 : CollatzResearch.WordTrace tailWord_769561 prefixEnd_769561 395154685954768822748359 := by
  unfold tailWord_769561
  simp only [CollatzResearch.WordTrace]
  refine ⟨28068195565019402400188537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18712130376679601600125691 28068195565019402400188537)
  ·
    refine ⟨21051146673764551800141403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28068195565019402400188537 21051146673764551800141403)
    ·
      refine ⟨31576720010646827700212105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21051146673764551800141403 31576720010646827700212105)
      ·
        refine ⟨23682540007985120775159079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31576720010646827700212105 23682540007985120775159079)
        ·
          refine ⟨35523810011977681162738619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23682540007985120775159079 35523810011977681162738619)
          ·
            refine ⟨53285715017966521744107929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35523810011977681162738619 53285715017966521744107929)
            ·
              refine ⟨39964286263474891308080947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53285715017966521744107929 39964286263474891308080947)
              ·
                refine ⟨59946429395212336962121421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39964286263474891308080947 59946429395212336962121421)
                ·
                  refine ⟨22479911023204626360795533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59946429395212336962121421 22479911023204626360795533)
                  ·
                    refine ⟨8429966633701734885298325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22479911023204626360795533 8429966633701734885298325)
                    ·
                      refine ⟨395154685954768822748359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8429966633701734885298325 395154685954768822748359)
                      ·
                        rfl

theorem cell23_769561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_769561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769561 prefixEnd_769561 := by exact prefixLift 769561
  have htrace : WordTrace (prefixWord ++ tailWord_769561) baseStart_769561 baseEnd_769561 := by
    simpa [prefixWord, tailWord_769561, baseEnd_769561] using wordTrace_append hprefix tailTrace_769561
  have hstable : (prefixWord ++ tailWord_769561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769561).length < 2 ^ (prefixWord ++ tailWord_769561).sum := by decide
  have hdescent : baseEnd_769561 < baseStart_769561 := by decide
  rcases family_descends (prefixWord ++ tailWord_769561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769565 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_769565 : Nat := 118140960795 + 769565 * 2 ^ 59
def prefixEnd_769565 : Nat := 4983230072969 + 3 ^ 40 * 769565 * 2
def baseEnd_769565 : Nat := 395156739877386807098341

theorem tailTrace_769565 : CollatzResearch.WordTrace tailWord_769565 prefixEnd_769565 395156739877386807098341 := by
  unfold tailWord_769565
  simp only [CollatzResearch.WordTrace]
  refine ⟨28068341457004911083334149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18712227638003274055556099 28068341457004911083334149)
  ·
    refine ⟨5262814023188420828125153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28068341457004911083334149 5262814023188420828125153)
    ·
      refine ⟨3947110517391315621093865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5262814023188420828125153 3947110517391315621093865)
      ·
        refine ⟨2960332888043486715820399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3947110517391315621093865 2960332888043486715820399)
        ·
          refine ⟨4440499332065230073730599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2960332888043486715820399 4440499332065230073730599)
          ·
            refine ⟨6660748998097845110595899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4440499332065230073730599 6660748998097845110595899)
            ·
              refine ⟨9991123497146767665893849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6660748998097845110595899 9991123497146767665893849)
              ·
                refine ⟨7493342622860075749420387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9991123497146767665893849 7493342622860075749420387)
                ·
                  refine ⟨11240013934290113624130581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7493342622860075749420387 11240013934290113624130581)
                  ·
                    refine ⟨526875653169849076131121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11240013934290113624130581 526875653169849076131121)
                    ·
                      refine ⟨395156739877386807098341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 526875653169849076131121 395156739877386807098341)
                      ·
                        rfl

theorem cell23_769565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_769565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769565 prefixEnd_769565 := by exact prefixLift 769565
  have htrace : WordTrace (prefixWord ++ tailWord_769565) baseStart_769565 baseEnd_769565 := by
    simpa [prefixWord, tailWord_769565, baseEnd_769565] using wordTrace_append hprefix tailTrace_769565
  have hstable : (prefixWord ++ tailWord_769565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769565).length < 2 ^ (prefixWord ++ tailWord_769565).sum := by decide
  have hdescent : baseEnd_769565 < baseStart_769565 := by decide
  rcases family_descends (prefixWord ++ tailWord_769565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769578 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_769578 : Nat := 118140960795 + 769578 * 2 ^ 59
def prefixEnd_769578 : Nat := 4983230072969 + 3 ^ 40 * 769578 * 2
def baseEnd_769578 : Nat := 395163415125895256235781

theorem tailTrace_769578 : CollatzResearch.WordTrace tailWord_769578 prefixEnd_769578 395163415125895256235781 := by
  unfold tailWord_769578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7017203901489453575889347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18712543737305209535704925 7017203901489453575889347)
  ·
    refine ⟨10525805852234180363834021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7017203901489453575889347 10525805852234180363834021)
    ·
      refine ⟨1973588597293908818218879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10525805852234180363834021 1973588597293908818218879)
      ·
        refine ⟨2960382895940863227328319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1973588597293908818218879 2960382895940863227328319)
        ·
          refine ⟨4440574343911294840992479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2960382895940863227328319 4440574343911294840992479)
          ·
            refine ⟨6660861515866942261488719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4440574343911294840992479 6660861515866942261488719)
            ·
              refine ⟨9991292273800413392233079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6660861515866942261488719 9991292273800413392233079)
              ·
                refine ⟨14986938410700620088349619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9991292273800413392233079 14986938410700620088349619)
                ·
                  refine ⟨22480407616050930132524429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14986938410700620088349619 22480407616050930132524429)
                  ·
                    refine ⟨8430152856019098799696661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22480407616050930132524429 8430152856019098799696661)
                    ·
                      refine ⟨395163415125895256235781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8430152856019098799696661 395163415125895256235781)
                      ·
                        rfl

theorem cell23_769578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_769578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769578 prefixEnd_769578 := by exact prefixLift 769578
  have htrace : WordTrace (prefixWord ++ tailWord_769578) baseStart_769578 baseEnd_769578 := by
    simpa [prefixWord, tailWord_769578, baseEnd_769578] using wordTrace_append hprefix tailTrace_769578
  have hstable : (prefixWord ++ tailWord_769578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769578).length < 2 ^ (prefixWord ++ tailWord_769578).sum := by decide
  have hdescent : baseEnd_769578 < baseStart_769578 := by decide
  rcases family_descends (prefixWord ++ tailWord_769578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769582 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_769582 : Nat := 118140960795 + 769582 * 2 ^ 59
def prefixEnd_769582 : Nat := 4983230072969 + 3 ^ 40 * 769582 * 2
def baseEnd_769582 : Nat := 395165469048513240585763

theorem tailTrace_769582 : CollatzResearch.WordTrace tailWord_769582 prefixEnd_769582 395165469048513240585763 := by
  unfold tailWord_769582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3508620187242915373337875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18712640998628881991135333 3508620187242915373337875)
  ·
    refine ⟨5262930280864373060006813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3508620187242915373337875 5262930280864373060006813)
    ·
      refine ⟨1973598855324139897502555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5262930280864373060006813 1973598855324139897502555)
      ·
        refine ⟨2960398282986209846253833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1973598855324139897502555 2960398282986209846253833)
        ·
          refine ⟨2220298712239657384690375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2960398282986209846253833 2220298712239657384690375)
          ·
            refine ⟨3330448068359486077035563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2220298712239657384690375 3330448068359486077035563)
            ·
              refine ⟨4995672102539229115553345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3330448068359486077035563 4995672102539229115553345)
              ·
                refine ⟨3746754076904421836665009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4995672102539229115553345 3746754076904421836665009)
                ·
                  refine ⟨2810065557678316377498757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3746754076904421836665009 2810065557678316377498757)
                  ·
                    refine ⟨526887292064684320781017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2810065557678316377498757 526887292064684320781017)
                    ·
                      refine ⟨395165469048513240585763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 526887292064684320781017 395165469048513240585763)
                      ·
                        rfl

theorem cell23_769582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_769582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769582 prefixEnd_769582 := by exact prefixLift 769582
  have htrace : WordTrace (prefixWord ++ tailWord_769582) baseStart_769582 baseEnd_769582 := by
    simpa [prefixWord, tailWord_769582, baseEnd_769582] using wordTrace_append hprefix tailTrace_769582
  have hstable : (prefixWord ++ tailWord_769582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769582).length < 2 ^ (prefixWord ++ tailWord_769582).sum := by decide
  have hdescent : baseEnd_769582 < baseStart_769582 := by decide
  rcases family_descends (prefixWord ++ tailWord_769582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769592 : List Nat := [2, 1, 2, 1, 4, 2, 2, 4, 1, 4]
def baseStart_769592 : Nat := 118140960795 + 769592 * 2 ^ 59
def prefixEnd_769592 : Nat := 4983230072969 + 3 ^ 40 * 769592 * 2
def baseEnd_769592 : Nat := 131723534618352733820239

theorem tailTrace_769592 : CollatzResearch.WordTrace tailWord_769592 prefixEnd_769592 131723534618352733820239 := by
  unfold tailWord_769592
  simp only [CollatzResearch.WordTrace]
  refine ⟨14034663113953547347283515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18712884151938063129711353 14034663113953547347283515)
  ·
    refine ⟨21051994670930321020925273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14034663113953547347283515 21051994670930321020925273)
    ·
      refine ⟨15788996003197740765693955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21051994670930321020925273 15788996003197740765693955)
      ·
        refine ⟨23683494004796611148540933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15788996003197740765693955 23683494004796611148540933)
        ·
          refine ⟨4440655125899364590351425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23683494004796611148540933 4440655125899364590351425)
          ·
            refine ⟨3330491344424523442763569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4440655125899364590351425 3330491344424523442763569)
            ·
              refine ⟨2497868508318392582072677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3330491344424523442763569 2497868508318392582072677)
              ·
                refine ⟨468350345309698609138627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2497868508318392582072677 468350345309698609138627)
                ·
                  refine ⟨702525517964547913707941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468350345309698609138627 702525517964547913707941)
                  ·
                    refine ⟨131723534618352733820239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 702525517964547913707941 131723534618352733820239)
                    ·
                      rfl

theorem cell23_769592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_769592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769592 prefixEnd_769592 := by exact prefixLift 769592
  have htrace : WordTrace (prefixWord ++ tailWord_769592) baseStart_769592 baseEnd_769592 := by
    simpa [prefixWord, tailWord_769592, baseEnd_769592] using wordTrace_append hprefix tailTrace_769592
  have hstable : (prefixWord ++ tailWord_769592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769592).length < 2 ^ (prefixWord ++ tailWord_769592).sum := by decide
  have hdescent : baseEnd_769592 < baseStart_769592 := by decide
  rcases family_descends (prefixWord ++ tailWord_769592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769605 : List Nat := [1, 3, 1, 1, 1, 4, 5, 1, 6]
def baseStart_769605 : Nat := 118140960795 + 769605 * 2 ^ 59
def prefixEnd_769605 : Nat := 4983230072969 + 3 ^ 40 * 769605 * 2
def baseEnd_769605 : Nat := 43908586567062961177573

theorem tailTrace_769605 : CollatzResearch.WordTrace tailWord_769605 prefixEnd_769605 43908586567062961177573 := by
  unfold tailWord_769605
  simp only [CollatzResearch.WordTrace]
  refine ⟨28069800376859997914790269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18713200251239998609860179 28069800376859997914790269)
  ·
    refine ⟨10526175141322499218046351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28069800376859997914790269 10526175141322499218046351)
    ·
      refine ⟨15789262711983748827069527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10526175141322499218046351 15789262711983748827069527)
      ·
        refine ⟨23683894067975623240604291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15789262711983748827069527 23683894067975623240604291)
        ·
          refine ⟨35525841101963434860906437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23683894067975623240604291 35525841101963434860906437)
          ·
            refine ⟨6661095206618144036419957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35525841101963434860906437 6661095206618144036419957)
            ·
              refine ⟨624477675620451003414371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6661095206618144036419957 624477675620451003414371)
              ·
                refine ⟨936716513430676505121557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624477675620451003414371 936716513430676505121557)
                ·
                  refine ⟨43908586567062961177573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 936716513430676505121557 43908586567062961177573)
                  ·
                    rfl

theorem cell23_769605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 6].length) (baseStart_769605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769605 prefixEnd_769605 := by exact prefixLift 769605
  have htrace : WordTrace (prefixWord ++ tailWord_769605) baseStart_769605 baseEnd_769605 := by
    simpa [prefixWord, tailWord_769605, baseEnd_769605] using wordTrace_append hprefix tailTrace_769605
  have hstable : (prefixWord ++ tailWord_769605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769605).length < 2 ^ (prefixWord ++ tailWord_769605).sum := by decide
  have hdescent : baseEnd_769605 < baseStart_769605 := by decide
  rcases family_descends (prefixWord ++ tailWord_769605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769625 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 6, 3, 2]
def baseStart_769625 : Nat := 118140960795 + 769625 * 2 ^ 59
def prefixEnd_769625 : Nat := 4983230072969 + 3 ^ 40 * 769625 * 2
def baseEnd_769625 : Nat := 395187548716656572348065

theorem tailTrace_769625 : CollatzResearch.WordTrace tailWord_769625 prefixEnd_769625 395187548716656572348065 := by
  unfold tailWord_769625
  simp only [CollatzResearch.WordTrace]
  refine ⟨28070529836787541330518329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18713686557858360887012219 28070529836787541330518329)
  ·
    refine ⟨21052897377590655997888747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28070529836787541330518329 21052897377590655997888747)
    ·
      refine ⟨31579346066385983996833121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21052897377590655997888747 31579346066385983996833121)
      ·
        refine ⟨23684509549789487997624841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31579346066385983996833121 23684509549789487997624841)
        ·
          refine ⟨17763382162342115998218631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23684509549789487997624841 17763382162342115998218631)
          ·
            refine ⟨26645073243513173997327947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17763382162342115998218631 26645073243513173997327947)
            ·
              refine ⟨39967609865269760995991921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26645073243513173997327947 39967609865269760995991921)
              ·
                refine ⟨29975707398952320746993941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39967609865269760995991921 29975707398952320746993941)
                ·
                  refine ⟨1405111284325890035015341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29975707398952320746993941 1405111284325890035015341)
                  ·
                    refine ⟨526916731622208763130753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1405111284325890035015341 526916731622208763130753)
                    ·
                      refine ⟨395187548716656572348065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 526916731622208763130753 395187548716656572348065)
                      ·
                        rfl

theorem cell23_769625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 3, 2].length) (baseStart_769625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769625 prefixEnd_769625 := by exact prefixLift 769625
  have htrace : WordTrace (prefixWord ++ tailWord_769625) baseStart_769625 baseEnd_769625 := by
    simpa [prefixWord, tailWord_769625, baseEnd_769625] using wordTrace_append hprefix tailTrace_769625
  have hstable : (prefixWord ++ tailWord_769625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769625).length < 2 ^ (prefixWord ++ tailWord_769625).sum := by decide
  have hdescent : baseEnd_769625 < baseStart_769625 := by decide
  rcases family_descends (prefixWord ++ tailWord_769625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769635 : List Nat := [1, 1, 1, 5, 1, 3, 2, 3, 1, 5]
def baseStart_769635 : Nat := 118140960795 + 769635 * 2 ^ 59
def prefixEnd_769635 : Nat := 4983230072969 + 3 ^ 40 * 769635 * 2
def baseEnd_769635 : Nat := 131730894507733844407673

theorem tailTrace_769635 : CollatzResearch.WordTrace tailWord_769635 prefixEnd_769635 131730894507733844407673 := by
  unfold tailWord_769635
  simp only [CollatzResearch.WordTrace]
  refine ⟨28070894566751313038382359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18713929711167542025588239 28070894566751313038382359)
  ·
    refine ⟨42106341850126969557573539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28070894566751313038382359 42106341850126969557573539)
    ·
      refine ⟨63159512775190454336360309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42106341850126969557573539 63159512775190454336360309)
      ·
        refine ⟨5921204322674105094033779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63159512775190454336360309 5921204322674105094033779)
        ·
          refine ⟨8881806484011157641050669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5921204322674105094033779 8881806484011157641050669)
          ·
            refine ⟨3330677431504184115394001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8881806484011157641050669 3330677431504184115394001)
            ·
              refine ⟨2498008073628138086545501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3330677431504184115394001 2498008073628138086545501)
              ·
                refine ⟨936753027610551782454563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2498008073628138086545501 936753027610551782454563)
                ·
                  refine ⟨1405129541415827673681845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 936753027610551782454563 1405129541415827673681845)
                  ·
                    refine ⟨131730894507733844407673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1405129541415827673681845 131730894507733844407673)
                    ·
                      rfl

theorem cell23_769635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 5].length) (baseStart_769635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769635 prefixEnd_769635 := by exact prefixLift 769635
  have htrace : WordTrace (prefixWord ++ tailWord_769635) baseStart_769635 baseEnd_769635 := by
    simpa [prefixWord, tailWord_769635, baseEnd_769635] using wordTrace_append hprefix tailTrace_769635
  have hstable : (prefixWord ++ tailWord_769635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769635).length < 2 ^ (prefixWord ++ tailWord_769635).sum := by decide
  have hdescent : baseEnd_769635 < baseStart_769635 := by decide
  rcases family_descends (prefixWord ++ tailWord_769635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769642 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_769642 : Nat := 118140960795 + 769642 * 2 ^ 59
def prefixEnd_769642 : Nat := 4983230072969 + 3 ^ 40 * 769642 * 2
def baseEnd_769642 : Nat := 395196277887783005835487

theorem tailTrace_769642 : CollatzResearch.WordTrace tailWord_769642 prefixEnd_769642 395196277887783005835487 := by
  unfold tailWord_769642
  simp only [CollatzResearch.WordTrace]
  refine ⟨7017787469431488308471795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18714099918483968822591453 7017787469431488308471795)
  ·
    refine ⟨10526681204147232462707693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7017787469431488308471795 10526681204147232462707693)
    ·
      refine ⟨3947505451555212173515385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10526681204147232462707693 3947505451555212173515385)
      ·
        refine ⟨2960629088666409130136539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3947505451555212173515385 2960629088666409130136539)
        ·
          refine ⟨4440943632999613695204809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2960629088666409130136539 4440943632999613695204809)
          ·
            refine ⟨3330707724749710271403607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4440943632999613695204809 3330707724749710271403607)
            ·
              refine ⟨4996061587124565407105411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3330707724749710271403607 4996061587124565407105411)
              ·
                refine ⟨7494092380686848110658117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4996061587124565407105411 7494092380686848110658117)
                ·
                  refine ⟨1405142321378784020748397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7494092380686848110658117 1405142321378784020748397)
                  ·
                    refine ⟨526928370517044007780649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1405142321378784020748397 526928370517044007780649)
                    ·
                      refine ⟨395196277887783005835487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 526928370517044007780649 395196277887783005835487)
                      ·
                        rfl

theorem cell23_769642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_769642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769642 prefixEnd_769642 := by exact prefixLift 769642
  have htrace : WordTrace (prefixWord ++ tailWord_769642) baseStart_769642 baseEnd_769642 := by
    simpa [prefixWord, tailWord_769642, baseEnd_769642] using wordTrace_append hprefix tailTrace_769642
  have hstable : (prefixWord ++ tailWord_769642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769642).length < 2 ^ (prefixWord ++ tailWord_769642).sum := by decide
  have hdescent : baseEnd_769642 < baseStart_769642 := by decide
  rcases family_descends (prefixWord ++ tailWord_769642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769658 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_769658 : Nat := 118140960795 + 769658 * 2 ^ 59
def prefixEnd_769658 : Nat := 4983230072969 + 3 ^ 40 * 769658 * 2
def baseEnd_769658 : Nat := 395204493578254943235413

theorem tailTrace_769658 : CollatzResearch.WordTrace tailWord_769658 prefixEnd_769658 395204493578254943235413 := by
  unfold tailWord_769658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7017933361416996991617407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18714488963778658644313085 7017933361416996991617407)
  ·
    refine ⟨10526900042125495487426111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7017933361416996991617407 10526900042125495487426111)
    ·
      refine ⟨15790350063188243231139167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10526900042125495487426111 15790350063188243231139167)
      ·
        refine ⟨23685525094782364846708751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15790350063188243231139167 23685525094782364846708751)
        ·
          refine ⟨35528287642173547270063127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23685525094782364846708751 35528287642173547270063127)
          ·
            refine ⟨53292431463260320905094691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35528287642173547270063127 53292431463260320905094691)
            ·
              refine ⟨79938647194890481357642037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53292431463260320905094691 79938647194890481357642037)
              ·
                refine ⟨7494248174520982627278941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79938647194890481357642037 7494248174520982627278941)
                ·
                  refine ⟨2810343065445368485229603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7494248174520982627278941 2810343065445368485229603)
                  ·
                    refine ⟨4215514598168052727844405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2810343065445368485229603 4215514598168052727844405)
                    ·
                      refine ⟨395204493578254943235413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4215514598168052727844405 395204493578254943235413)
                      ·
                        rfl

theorem cell23_769658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_769658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769658 prefixEnd_769658 := by exact prefixLift 769658
  have htrace : WordTrace (prefixWord ++ tailWord_769658) baseStart_769658 baseEnd_769658 := by
    simpa [prefixWord, tailWord_769658, baseEnd_769658] using wordTrace_append hprefix tailTrace_769658
  have hstable : (prefixWord ++ tailWord_769658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769658).length < 2 ^ (prefixWord ++ tailWord_769658).sum := by decide
  have hdescent : baseEnd_769658 < baseStart_769658 := by decide
  rcases family_descends (prefixWord ++ tailWord_769658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769675 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 3]
def baseStart_769675 : Nat := 118140960795 + 769675 * 2 ^ 59
def prefixEnd_769675 : Nat := 4983230072969 + 3 ^ 40 * 769675 * 2
def baseEnd_769675 : Nat := 395213222749381376722835

theorem tailTrace_769675 : CollatzResearch.WordTrace tailWord_769675 prefixEnd_769675 395213222749381376722835 := by
  unfold tailWord_769675
  simp only [CollatzResearch.WordTrace]
  refine ⟨28072353486606399869838479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18714902324404266579892319 28072353486606399869838479)
  ·
    refine ⟨42108530229909599804757719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28072353486606399869838479 42108530229909599804757719)
    ·
      refine ⟨63162795344864399707136579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42108530229909599804757719 63162795344864399707136579)
      ·
        refine ⟨94744193017296599560704869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63162795344864399707136579 94744193017296599560704869)
        ·
          refine ⟨17764536190743112417632163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94744193017296599560704869 17764536190743112417632163)
          ·
            refine ⟨26646804286114668626448245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17764536190743112417632163 26646804286114668626448245)
            ·
              refine ⟨2498137901823250183729523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26646804286114668626448245 2498137901823250183729523)
              ·
                refine ⟨3747206852734875275594285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498137901823250183729523 3747206852734875275594285)
                ·
                  refine ⟨1405202569775578228347857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3747206852734875275594285 1405202569775578228347857)
                  ·
                    refine ⟨1053901927331683671260893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1405202569775578228347857 1053901927331683671260893)
                    ·
                      refine ⟨395213222749381376722835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1053901927331683671260893 395213222749381376722835)
                      ·
                        rfl

theorem cell23_769675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 3].length) (baseStart_769675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769675 prefixEnd_769675 := by exact prefixLift 769675
  have htrace : WordTrace (prefixWord ++ tailWord_769675) baseStart_769675 baseEnd_769675 := by
    simpa [prefixWord, tailWord_769675, baseEnd_769675] using wordTrace_append hprefix tailTrace_769675
  have hstable : (prefixWord ++ tailWord_769675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769675).length < 2 ^ (prefixWord ++ tailWord_769675).sum := by decide
  have hdescent : baseEnd_769675 < baseStart_769675 := by decide
  rcases family_descends (prefixWord ++ tailWord_769675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769682 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_769682 : Nat := 118140960795 + 769682 * 2 ^ 59
def prefixEnd_769682 : Nat := 4983230072969 + 3 ^ 40 * 769682 * 2
def baseEnd_769682 : Nat := 131738939037987616445101

theorem tailTrace_769682 : CollatzResearch.WordTrace tailWord_769682 prefixEnd_769682 131738939037987616445101 := by
  unfold tailWord_769682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018152199395260016335825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18715072531720693376895533 7018152199395260016335825)
  ·
    refine ⟨5263614149546445012251869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7018152199395260016335825 5263614149546445012251869)
    ·
      refine ⟨1973855306079916879594451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5263614149546445012251869 1973855306079916879594451)
      ·
        refine ⟨2960782959119875319391677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1973855306079916879594451 2960782959119875319391677)
        ·
          refine ⟨1110293609669953244771879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2960782959119875319391677 1110293609669953244771879)
          ·
            refine ⟨1665440414504929867157819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110293609669953244771879 1665440414504929867157819)
            ·
              refine ⟨2498160621757394800736729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1665440414504929867157819 2498160621757394800736729)
              ·
                refine ⟨1873620466318046100552547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2498160621757394800736729 1873620466318046100552547)
                ·
                  refine ⟨2810430699477069150828821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873620466318046100552547 2810430699477069150828821)
                  ·
                    refine ⟨131738939037987616445101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2810430699477069150828821 131738939037987616445101)
                    ·
                      rfl

theorem cell23_769682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_769682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769682 prefixEnd_769682 := by exact prefixLift 769682
  have htrace : WordTrace (prefixWord ++ tailWord_769682) baseStart_769682 baseEnd_769682 := by
    simpa [prefixWord, tailWord_769682, baseEnd_769682] using wordTrace_append hprefix tailTrace_769682
  have hstable : (prefixWord ++ tailWord_769682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769682).length < 2 ^ (prefixWord ++ tailWord_769682).sum := by decide
  have hdescent : baseEnd_769682 < baseStart_769682 := by decide
  rcases family_descends (prefixWord ++ tailWord_769682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769695 : List Nat := [1, 1, 2, 7, 1, 11]
def baseStart_769695 : Nat := 118140960795 + 769695 * 2 ^ 59
def prefixEnd_769695 : Nat := 4983230072969 + 3 ^ 40 * 769695 * 2
def baseEnd_769695 : Nat := 1626434124948441557501

theorem tailTrace_769695 : CollatzResearch.WordTrace tailWord_769695 prefixEnd_769695 1626434124948441557501 := by
  unfold tailWord_769695
  simp only [CollatzResearch.WordTrace]
  refine ⟨28073082946533943285566539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18715388631022628857044359 28073082946533943285566539)
  ·
    refine ⟨42109624419800914928349809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28073082946533943285566539 42109624419800914928349809)
    ·
      refine ⟨31582218314850686196262357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42109624419800914928349809 31582218314850686196262357)
      ·
        refine ⟨740208241754312957724899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 31582218314850686196262357 740208241754312957724899)
        ·
          refine ⟨1110312362631469436587349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740208241754312957724899 1110312362631469436587349)
          ·
            refine ⟨1626434124948441557501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1110312362631469436587349 1626434124948441557501)
            ·
              rfl

theorem cell23_769695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 11].length) (baseStart_769695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769695 prefixEnd_769695 := by exact prefixLift 769695
  have htrace : WordTrace (prefixWord ++ tailWord_769695) baseStart_769695 baseEnd_769695 := by
    simpa [prefixWord, tailWord_769695, baseEnd_769695] using wordTrace_append hprefix tailTrace_769695
  have hstable : (prefixWord ++ tailWord_769695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769695).length < 2 ^ (prefixWord ++ tailWord_769695).sum := by decide
  have hdescent : baseEnd_769695 < baseStart_769695 := by decide
  rcases family_descends (prefixWord ++ tailWord_769695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769722 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3]
def baseStart_769722 : Nat := 118140960795 + 769722 * 2 ^ 59
def prefixEnd_769722 : Nat := 4983230072969 + 3 ^ 40 * 769722 * 2
def baseEnd_769722 : Nat := 395237356340142692835119

theorem tailTrace_769722 : CollatzResearch.WordTrace tailWord_769722 prefixEnd_769722 395237356340142692835119 := by
  unfold tailWord_769722
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018516929359031724199855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18716045144957417931199613 7018516929359031724199855)
  ·
    refine ⟨10527775394038547586299783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7018516929359031724199855 10527775394038547586299783)
    ·
      refine ⟨15791663091057821379449675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10527775394038547586299783 15791663091057821379449675)
      ·
        refine ⟨23687494636586732069174513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15791663091057821379449675 23687494636586732069174513)
        ·
          refine ⟨17765620977440049051880885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23687494636586732069174513 17765620977440049051880885)
          ·
            refine ⟨1665526966635004598613833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17765620977440049051880885 1665526966635004598613833)
            ·
              refine ⟨1249145224976253448960375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1665526966635004598613833 1249145224976253448960375)
              ·
                refine ⟨1873717837464380173440563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249145224976253448960375 1873717837464380173440563)
                ·
                  refine ⟨2810576756196570260160845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873717837464380173440563 2810576756196570260160845)
                  ·
                    refine ⟨1053966283573713847560317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2810576756196570260160845 1053966283573713847560317)
                    ·
                      refine ⟨395237356340142692835119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1053966283573713847560317 395237356340142692835119)
                      ·
                        rfl

theorem cell23_769722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_769722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769722 prefixEnd_769722 := by exact prefixLift 769722
  have htrace : WordTrace (prefixWord ++ tailWord_769722) baseStart_769722 baseEnd_769722 := by
    simpa [prefixWord, tailWord_769722, baseEnd_769722] using wordTrace_append hprefix tailTrace_769722
  have hstable : (prefixWord ++ tailWord_769722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769722).length < 2 ^ (prefixWord ++ tailWord_769722).sum := by decide
  have hdescent : baseEnd_769722 < baseStart_769722 := by decide
  rcases family_descends (prefixWord ++ tailWord_769722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769750 : List Nat := [5, 2, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_769750 : Nat := 118140960795 + 769750 * 2 ^ 59
def prefixEnd_769750 : Nat := 4983230072969 + 3 ^ 40 * 769750 * 2
def baseEnd_769750 : Nat := 131750577932822861094997

theorem tailTrace_769750 : CollatzResearch.WordTrace tailWord_769750 prefixEnd_769750 131750577932822861094997 := by
  unfold tailWord_769750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1754693060083417979926169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18716725974223125119212469 1754693060083417979926169)
  ·
    refine ⟨1316019795062563484944627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1754693060083417979926169 1316019795062563484944627)
    ·
      refine ⟨1974029692593845227416941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1316019795062563484944627 1974029692593845227416941)
      ·
        refine ⟨740261134722691960281353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1974029692593845227416941 740261134722691960281353)
        ·
          refine ⟨555195851042018970211015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 740261134722691960281353 555195851042018970211015)
          ·
            refine ⟨832793776563028455316523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555195851042018970211015 832793776563028455316523)
            ·
              refine ⟨1249190664844542682974785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832793776563028455316523 1249190664844542682974785)
              ·
                refine ⟨936892998633407012231089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1249190664844542682974785 936892998633407012231089)
                ·
                  refine ⟨702669748975055259173317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 936892998633407012231089 702669748975055259173317)
                  ·
                    refine ⟨131750577932822861094997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 702669748975055259173317 131750577932822861094997)
                    ·
                      rfl

theorem cell23_769750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_769750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769750 prefixEnd_769750 := by exact prefixLift 769750
  have htrace : WordTrace (prefixWord ++ tailWord_769750) baseStart_769750 baseEnd_769750 := by
    simpa [prefixWord, tailWord_769750, baseEnd_769750] using wordTrace_append hprefix tailTrace_769750
  have hstable : (prefixWord ++ tailWord_769750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769750).length < 2 ^ (prefixWord ++ tailWord_769750).sum := by decide
  have hdescent : baseEnd_769750 < baseStart_769750 := by decide
  rcases family_descends (prefixWord ++ tailWord_769750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
