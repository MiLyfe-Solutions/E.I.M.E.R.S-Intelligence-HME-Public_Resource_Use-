import V185TrunkScan21Chunk137

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1682563 : List Nat := [1, 1, 1, 3, 3, 2, 2, 8]
def baseStart_1682563 : Nat := 118140960795 + 1682563 * 2 ^ 59
def prefixEnd_1682563 : Nat := 4983230072969 + 3 ^ 40 * 1682563 * 2
def baseEnd_1682563 : Nat := 127994600069778621959191

theorem tailTrace_1682563 : CollatzResearch.WordTrace tailWord_1682563 prefixEnd_1682563 127994600069778621959191 := by
  unfold tailWord_1682563
  simp only [CollatzResearch.WordTrace]
  refine ⟨61368114203369084727700343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40912076135579389818466895 61368114203369084727700343)
  ·
    refine ⟨92052171305053627091550515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61368114203369084727700343 92052171305053627091550515)
    ·
      refine ⟨138078256957580440637325773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92052171305053627091550515 138078256957580440637325773)
      ·
        refine ⟨51779346359092665238997165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138078256957580440637325773 51779346359092665238997165)
        ·
          refine ⟨19417254884659749464623937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51779346359092665238997165 19417254884659749464623937)
          ·
            refine ⟨14562941163494812098467953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19417254884659749464623937 14562941163494812098467953)
            ·
              refine ⟨10922205872621109073850965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14562941163494812098467953 10922205872621109073850965)
              ·
                refine ⟨127994600069778621959191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10922205872621109073850965 127994600069778621959191)
                ·
                  rfl

theorem cell21_1682563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 8].length) (baseStart_1682563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682563 prefixEnd_1682563 := by exact prefixLift 1682563
  have htrace : WordTrace (prefixWord ++ tailWord_1682563) baseStart_1682563 baseEnd_1682563 := by
    simpa [prefixWord, tailWord_1682563, baseEnd_1682563] using wordTrace_append hprefix tailTrace_1682563
  have hstable : (prefixWord ++ tailWord_1682563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682563).length < 2 ^ (prefixWord ++ tailWord_1682563).sum := by decide
  have hdescent : baseEnd_1682563 < baseStart_1682563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682611 : List Nat := [1, 1, 1, 2, 3, 2, 2, 6, 3]
def baseStart_1682611 : Nat := 118140960795 + 1682611 * 2 ^ 59
def prefixEnd_1682611 : Nat := 4983230072969 + 3 ^ 40 * 1682611 * 2
def baseEnd_1682611 : Nat := 383994754463298449077475

theorem tailTrace_1682611 : CollatzResearch.WordTrace tailWord_1682611 prefixEnd_1682611 383994754463298449077475 := by
  unfold tailWord_1682611
  simp only [CollatzResearch.WordTrace]
  refine ⟨61369864907195188925447687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40913243271463459283631791 61369864907195188925447687)
  ·
    refine ⟨92054797360792783388171531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61369864907195188925447687 92054797360792783388171531)
    ·
      refine ⟨138082196041189175082257297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92054797360792783388171531 138082196041189175082257297)
      ·
        refine ⟨103561647030891881311692973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138082196041189175082257297 103561647030891881311692973)
        ·
          refine ⟨38835617636584455491884865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103561647030891881311692973 38835617636584455491884865)
          ·
            refine ⟨29126713227438341618913649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38835617636584455491884865 29126713227438341618913649)
            ·
              refine ⟨21845034920578756214185237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29126713227438341618913649 21845034920578756214185237)
              ·
                refine ⟨1023986011902129197539933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21845034920578756214185237 1023986011902129197539933)
                ·
                  refine ⟨383994754463298449077475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023986011902129197539933 383994754463298449077475)
                  ·
                    rfl

theorem cell21_1682611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 3].length) (baseStart_1682611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682611 prefixEnd_1682611 := by exact prefixLift 1682611
  have htrace : WordTrace (prefixWord ++ tailWord_1682611) baseStart_1682611 baseEnd_1682611 := by
    simpa [prefixWord, tailWord_1682611, baseEnd_1682611] using wordTrace_append hprefix tailTrace_1682611
  have hstable : (prefixWord ++ tailWord_1682611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682611).length < 2 ^ (prefixWord ++ tailWord_1682611).sum := by decide
  have hdescent : baseEnd_1682611 < baseStart_1682611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682690 : List Nat := [3, 4, 1, 1, 3, 1, 3, 5]
def baseStart_1682690 : Nat := 118140960795 + 1682690 * 2 ^ 59
def prefixEnd_1682690 : Nat := 4983230072969 + 3 ^ 40 * 1682690 * 2
def baseEnd_1682690 : Nat := 128004261113203955753549

theorem tailTrace_1682690 : CollatzResearch.WordTrace tailWord_1682690 prefixEnd_1682690 128004261113203955753549 := by
  unfold tailWord_1682690
  simp only [CollatzResearch.WordTrace]
  refine ⟨15343186568477246354393381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40915164182605990278382349 15343186568477246354393381)
  ·
    refine ⟨2876847481589483691448759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15343186568477246354393381 2876847481589483691448759)
    ·
      refine ⟨4315271222384225537173139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2876847481589483691448759 4315271222384225537173139)
      ·
        refine ⟨6472906833576338305759709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4315271222384225537173139 6472906833576338305759709)
        ·
          refine ⟨2427340062591126864659891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6472906833576338305759709 2427340062591126864659891)
          ·
            refine ⟨3641010093886690296989837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427340062591126864659891 3641010093886690296989837)
            ·
              refine ⟨1365378785207508861371189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3641010093886690296989837 1365378785207508861371189)
              ·
                refine ⟨128004261113203955753549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1365378785207508861371189 128004261113203955753549)
                ·
                  rfl

theorem cell21_1682690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_1682690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682690 prefixEnd_1682690 := by exact prefixLift 1682690
  have htrace : WordTrace (prefixWord ++ tailWord_1682690) baseStart_1682690 baseEnd_1682690 := by
    simpa [prefixWord, tailWord_1682690, baseEnd_1682690] using wordTrace_append hprefix tailTrace_1682690
  have hstable : (prefixWord ++ tailWord_1682690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682690).length < 2 ^ (prefixWord ++ tailWord_1682690).sum := by decide
  have hdescent : baseEnd_1682690 < baseStart_1682690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682746 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_1682746 : Nat := 118140960795 + 1682746 * 2 ^ 59
def prefixEnd_1682746 : Nat := 4983230072969 + 3 ^ 40 * 1682746 * 2
def baseEnd_1682746 : Nat := 384025563302568214327199

theorem tailTrace_1682746 : CollatzResearch.WordTrace tailWord_1682746 prefixEnd_1682746 384025563302568214327199 := by
  unfold tailWord_1682746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15343697190426526745403023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40916525841137404654408061 15343697190426526745403023)
  ·
    refine ⟨23015545785639790118104535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15343697190426526745403023 23015545785639790118104535)
    ·
      refine ⟨34523318678459685177156803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23015545785639790118104535 34523318678459685177156803)
      ·
        refine ⟨51784978017689527765735205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34523318678459685177156803 51784978017689527765735205)
        ·
          refine ⟨9709683378316786456075351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51784978017689527765735205 9709683378316786456075351)
          ·
            refine ⟨14564525067475179684113027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9709683378316786456075351 14564525067475179684113027)
            ·
              refine ⟨21846787601212769526169541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14564525067475179684113027 21846787601212769526169541)
              ·
                refine ⟨4096272675227394286156789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21846787601212769526169541 4096272675227394286156789)
                ·
                  refine ⟨384025563302568214327199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4096272675227394286156789 384025563302568214327199)
                  ·
                    rfl

theorem cell21_1682746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_1682746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682746 prefixEnd_1682746 := by exact prefixLift 1682746
  have htrace : WordTrace (prefixWord ++ tailWord_1682746) baseStart_1682746 baseEnd_1682746 := by
    simpa [prefixWord, tailWord_1682746, baseEnd_1682746] using wordTrace_append hprefix tailTrace_1682746
  have hstable : (prefixWord ++ tailWord_1682746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682746).length < 2 ^ (prefixWord ++ tailWord_1682746).sum := by decide
  have hdescent : baseEnd_1682746 < baseStart_1682746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682749 : List Nat := [1, 4, 1, 5, 1, 1, 1, 7]
def baseStart_1682749 : Nat := 118140960795 + 1682749 * 2 ^ 59
def prefixEnd_1682749 : Nat := 4983230072969 + 3 ^ 40 * 1682749 * 2
def baseEnd_1682749 : Nat := 128008749314480291925731

theorem tailTrace_1682749 : CollatzResearch.WordTrace tailWord_1682749 prefixEnd_1682749 128008749314480291925731 := by
  unfold tailWord_1682749
  simp only [CollatzResearch.WordTrace]
  refine ⟨61374898180695238493971301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40916598787130158995980867 61374898180695238493971301)
  ·
    refine ⟨11507793408880357217619619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61374898180695238493971301 11507793408880357217619619)
    ·
      refine ⟨17261690113320535826429429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11507793408880357217619619 17261690113320535826429429)
      ·
        refine ⟨1618283448123800233727759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17261690113320535826429429 1618283448123800233727759)
        ·
          refine ⟨2427425172185700350591639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618283448123800233727759 2427425172185700350591639)
          ·
            refine ⟨3641137758278550525887459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427425172185700350591639 3641137758278550525887459)
            ·
              refine ⟨5461706637417825788831189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3641137758278550525887459 5461706637417825788831189)
              ·
                refine ⟨128008749314480291925731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5461706637417825788831189 128008749314480291925731)
                ·
                  rfl

theorem cell21_1682749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 7].length) (baseStart_1682749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682749 prefixEnd_1682749 := by exact prefixLift 1682749
  have htrace : WordTrace (prefixWord ++ tailWord_1682749) baseStart_1682749 baseEnd_1682749 := by
    simpa [prefixWord, tailWord_1682749, baseEnd_1682749] using wordTrace_append hprefix tailTrace_1682749
  have hstable : (prefixWord ++ tailWord_1682749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682749).length < 2 ^ (prefixWord ++ tailWord_1682749).sum := by decide
  have hdescent : baseEnd_1682749 < baseStart_1682749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682856 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 5]
def baseStart_1682856 : Nat := 118140960795 + 1682856 * 2 ^ 59
def prefixEnd_1682856 : Nat := 4983230072969 + 3 ^ 40 * 1682856 * 2
def baseEnd_1682856 : Nat := 384050666801232467493641

theorem tailTrace_1682856 : CollatzResearch.WordTrace tailWord_1682856 prefixEnd_1682856 384050666801232467493641 := by
  unfold tailWord_1682856
  simp only [CollatzResearch.WordTrace]
  refine ⟨30689400395653797884058211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40919200527538397178744281 30689400395653797884058211)
  ·
    refine ⟨46034100593480696826087317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30689400395653797884058211 46034100593480696826087317)
    ·
      refine ⟨2157848465319407663722843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46034100593480696826087317 2157848465319407663722843)
      ·
        refine ⟨3236772697979111495584265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2157848465319407663722843 3236772697979111495584265)
        ·
          refine ⟨2427579523484333621688199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3236772697979111495584265 2427579523484333621688199)
          ·
            refine ⟨3641369285226500432532299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427579523484333621688199 3641369285226500432532299)
            ·
              refine ⟨5462053927839750648798449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3641369285226500432532299 5462053927839750648798449)
              ·
                refine ⟨4096540445879812986598837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5462053927839750648798449 4096540445879812986598837)
                ·
                  refine ⟨384050666801232467493641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4096540445879812986598837 384050666801232467493641)
                  ·
                    rfl

theorem cell21_1682856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_1682856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682856 prefixEnd_1682856 := by exact prefixLift 1682856
  have htrace : WordTrace (prefixWord ++ tailWord_1682856) baseStart_1682856 baseEnd_1682856 := by
    simpa [prefixWord, tailWord_1682856, baseEnd_1682856] using wordTrace_append hprefix tailTrace_1682856
  have hstable : (prefixWord ++ tailWord_1682856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682856).length < 2 ^ (prefixWord ++ tailWord_1682856).sum := by decide
  have hdescent : baseEnd_1682856 < baseStart_1682856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682884 : List Nat := [2, 3, 3, 2, 1, 2, 8]
def baseStart_1682884 : Nat := 118140960795 + 1682884 * 2 ^ 59
def prefixEnd_1682884 : Nat := 4983230072969 + 3 ^ 40 * 1682884 * 2
def baseEnd_1682884 : Nat := 42673006309190071225213

theorem tailTrace_1682884 : CollatzResearch.WordTrace tailWord_1682884 prefixEnd_1682884 42673006309190071225213 := by
  unfold tailWord_1682884
  simp only [CollatzResearch.WordTrace]
  refine ⟨30689911017603078275067853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40919881356804104366757137 30689911017603078275067853)
  ·
    refine ⟨11508716631601154353150445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30689911017603078275067853 11508716631601154353150445)
    ·
      refine ⟨4315768736850432882431417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11508716631601154353150445 4315768736850432882431417)
      ·
        refine ⟨3236826552637824661823563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4315768736850432882431417 3236826552637824661823563)
        ·
          refine ⟨4855239828956736992735345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236826552637824661823563 4855239828956736992735345)
          ·
            refine ⟨3641429871717552744551509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4855239828956736992735345 3641429871717552744551509)
            ·
              refine ⟨42673006309190071225213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3641429871717552744551509 42673006309190071225213)
              ·
                rfl

theorem cell21_1682884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 8].length) (baseStart_1682884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682884 prefixEnd_1682884 := by exact prefixLift 1682884
  have htrace : WordTrace (prefixWord ++ tailWord_1682884) baseStart_1682884 baseEnd_1682884 := by
    simpa [prefixWord, tailWord_1682884, baseEnd_1682884] using wordTrace_append hprefix tailTrace_1682884
  have hstable : (prefixWord ++ tailWord_1682884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682884).length < 2 ^ (prefixWord ++ tailWord_1682884).sum := by decide
  have hdescent : baseEnd_1682884 < baseStart_1682884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682946 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1682946 : Nat := 118140960795 + 1682946 * 2 ^ 59
def prefixEnd_1682946 : Nat := 4983230072969 + 3 ^ 40 * 1682946 * 2
def baseEnd_1682946 : Nat := 384071206027412310993457

theorem tailTrace_1682946 : CollatzResearch.WordTrace tailWord_1682946 prefixEnd_1682946 384071206027412310993457 := by
  unfold tailWord_1682946
  simp only [CollatzResearch.WordTrace]
  refine ⟨15345520840245385284723173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40921388907321027425928461 15345520840245385284723173)
  ·
    refine ⟨2877285157546009740885595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15345520840245385284723173 2877285157546009740885595)
    ·
      refine ⟨4315927736319014611328393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2877285157546009740885595 4315927736319014611328393)
      ·
        refine ⟨3236945802239260958496295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4315927736319014611328393 3236945802239260958496295)
        ·
          refine ⟨4855418703358891437744443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236945802239260958496295 4855418703358891437744443)
          ·
            refine ⟨7283128055038337156616665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4855418703358891437744443 7283128055038337156616665)
            ·
              refine ⟨5462346041278752867462499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7283128055038337156616665 5462346041278752867462499)
              ·
                refine ⟨8193519061918129301193749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5462346041278752867462499 8193519061918129301193749)
                ·
                  refine ⟨384071206027412310993457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8193519061918129301193749 384071206027412310993457)
                  ·
                    rfl

theorem cell21_1682946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1682946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682946 prefixEnd_1682946 := by exact prefixLift 1682946
  have htrace : WordTrace (prefixWord ++ tailWord_1682946) baseStart_1682946 baseEnd_1682946 := by
    simpa [prefixWord, tailWord_1682946, baseEnd_1682946] using wordTrace_append hprefix tailTrace_1682946
  have hstable : (prefixWord ++ tailWord_1682946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682946).length < 2 ^ (prefixWord ++ tailWord_1682946).sum := by decide
  have hdescent : baseEnd_1682946 < baseStart_1682946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683095 : List Nat := [1, 1, 3, 3, 2, 3, 1, 7]
def baseStart_1683095 : Nat := 118140960795 + 1683095 * 2 ^ 59
def prefixEnd_1683095 : Nat := 4983230072969 + 3 ^ 40 * 1683095 * 2
def baseEnd_1683095 : Nat := 128035069952473721003273

theorem tailTrace_1683095 : CollatzResearch.WordTrace tailWord_1683095 prefixEnd_1683095 128035069952473721003273 := by
  unfold tailWord_1683095
  simp only [CollatzResearch.WordTrace]
  refine ⟨61387517837441739586066739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40925011891627826390711159 61387517837441739586066739)
  ·
    refine ⟨92081276756162609379100109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61387517837441739586066739 92081276756162609379100109)
    ·
      refine ⟨34530478783560978517162541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92081276756162609379100109 34530478783560978517162541)
      ·
        refine ⟨12948929543835366943935953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34530478783560978517162541 12948929543835366943935953)
        ·
          refine ⟨9711697157876525207951965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12948929543835366943935953 9711697157876525207951965)
          ·
            refine ⟨3641886434203696952981987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9711697157876525207951965 3641886434203696952981987)
            ·
              refine ⟨5462829651305545429472981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3641886434203696952981987 5462829651305545429472981)
              ·
                refine ⟨128035069952473721003273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5462829651305545429472981 128035069952473721003273)
                ·
                  rfl

theorem cell21_1683095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 7].length) (baseStart_1683095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683095 prefixEnd_1683095 := by exact prefixLift 1683095
  have htrace : WordTrace (prefixWord ++ tailWord_1683095) baseStart_1683095 baseEnd_1683095 := by
    simpa [prefixWord, tailWord_1683095, baseEnd_1683095] using wordTrace_append hprefix tailTrace_1683095
  have hstable : (prefixWord ++ tailWord_1683095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683095).length < 2 ^ (prefixWord ++ tailWord_1683095).sum := by decide
  have hdescent : baseEnd_1683095 < baseStart_1683095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683109 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 7]
def baseStart_1683109 : Nat := 118140960795 + 1683109 * 2 ^ 59
def prefixEnd_1683109 : Nat := 4983230072969 + 3 ^ 40 * 1683109 * 2
def baseEnd_1683109 : Nat := 384108404848160249776457

theorem tailTrace_1683109 : CollatzResearch.WordTrace tailWord_1683109 prefixEnd_1683109 384108404848160249776457 := by
  unfold tailWord_1683109
  simp only [CollatzResearch.WordTrace]
  refine ⟨61388028459391019977076381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40925352306260679984717587 61388028459391019977076381)
  ·
    refine ⟨23020510672271632491403643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61388028459391019977076381 23020510672271632491403643)
    ·
      refine ⟨34530766008407448737105465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23020510672271632491403643 34530766008407448737105465)
      ·
        refine ⟨25898074506305586552829099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34530766008407448737105465 25898074506305586552829099)
        ·
          refine ⟨38847111759458379829243649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25898074506305586552829099 38847111759458379829243649)
          ·
            refine ⟨29135333819593784871932737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38847111759458379829243649 29135333819593784871932737)
            ·
              refine ⟨21851500364695338653949553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29135333819593784871932737 21851500364695338653949553)
              ·
                refine ⟨16388625273521503990462165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21851500364695338653949553 16388625273521503990462165)
                ·
                  refine ⟨384108404848160249776457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16388625273521503990462165 384108404848160249776457)
                  ·
                    rfl

theorem cell21_1683109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_1683109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683109 prefixEnd_1683109 := by exact prefixLift 1683109
  have htrace : WordTrace (prefixWord ++ tailWord_1683109) baseStart_1683109 baseEnd_1683109 := by
    simpa [prefixWord, tailWord_1683109, baseEnd_1683109] using wordTrace_append hprefix tailTrace_1683109
  have hstable : (prefixWord ++ tailWord_1683109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683109).length < 2 ^ (prefixWord ++ tailWord_1683109).sum := by decide
  have hdescent : baseEnd_1683109 < baseStart_1683109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683118 : List Nat := [4, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_1683118 : Nat := 118140960795 + 1683118 * 2 ^ 59
def prefixEnd_1683118 : Nat := 4983230072969 + 3 ^ 40 * 1683118 * 2
def baseEnd_1683118 : Nat := 384110458770778234126439

theorem tailTrace_1683118 : CollatzResearch.WordTrace tailWord_1683118 prefixEnd_1683118 384110458770778234126439 := by
  unfold tailWord_1683118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7673544589544801814269251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40925571144238943009436005 7673544589544801814269251)
  ·
    refine ⟨11510316884317202721403877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7673544589544801814269251 11510316884317202721403877)
    ·
      refine ⟨2158184415809475510263227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11510316884317202721403877 2158184415809475510263227)
      ·
        refine ⟨3237276623714213265394841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2158184415809475510263227 3237276623714213265394841)
        ·
          refine ⟨2427957467785659949046131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3237276623714213265394841 2427957467785659949046131)
          ·
            refine ⟨3641936201678489923569197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427957467785659949046131 3641936201678489923569197)
            ·
              refine ⟨1365726075629433721338449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3641936201678489923569197 1365726075629433721338449)
              ·
                refine ⟨1024294556722075291003837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1365726075629433721338449 1024294556722075291003837)
                ·
                  refine ⟨384110458770778234126439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1024294556722075291003837 384110458770778234126439)
                  ·
                    rfl

theorem cell21_1683118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_1683118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683118 prefixEnd_1683118 := by exact prefixLift 1683118
  have htrace : WordTrace (prefixWord ++ tailWord_1683118) baseStart_1683118 baseEnd_1683118 := by
    simpa [prefixWord, tailWord_1683118, baseEnd_1683118] using wordTrace_append hprefix tailTrace_1683118
  have hstable : (prefixWord ++ tailWord_1683118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683118).length < 2 ^ (prefixWord ++ tailWord_1683118).sum := by decide
  have hdescent : baseEnd_1683118 < baseStart_1683118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683171 : List Nat := [1, 1, 1, 7, 2, 9]
def baseStart_1683171 : Nat := 118140960795 + 1683171 * 2 ^ 59
def prefixEnd_1683171 : Nat := 4983230072969 + 3 ^ 40 * 1683171 * 2
def baseEnd_1683171 : Nat := 14226761262698589620111

theorem tailTrace_1683171 : CollatzResearch.WordTrace tailWord_1683171 prefixEnd_1683171 14226761262698589620111 := by
  unfold tailWord_1683171
  simp only [CollatzResearch.WordTrace]
  refine ⟨61390289785166404565833367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40926859856777603043888911 61390289785166404565833367)
  ·
    refine ⟨92085434677749606848750051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61390289785166404565833367 92085434677749606848750051)
    ·
      refine ⟨138128152016624410273125077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92085434677749606848750051 138128152016624410273125077)
      ·
        refine ⟨3237378562889634615776369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 138128152016624410273125077 3237378562889634615776369)
        ·
          refine ⟨2428033922167225961832277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3237378562889634615776369 2428033922167225961832277)
          ·
            refine ⟨14226761262698589620111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2428033922167225961832277 14226761262698589620111)
            ·
              rfl

theorem cell21_1683171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 9].length) (baseStart_1683171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683171 prefixEnd_1683171 := by exact prefixLift 1683171
  have htrace : WordTrace (prefixWord ++ tailWord_1683171) baseStart_1683171 baseEnd_1683171 := by
    simpa [prefixWord, tailWord_1683171, baseEnd_1683171] using wordTrace_append hprefix tailTrace_1683171
  have hstable : (prefixWord ++ tailWord_1683171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683171).length < 2 ^ (prefixWord ++ tailWord_1683171).sum := by decide
  have hdescent : baseEnd_1683171 < baseStart_1683171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683233 : List Nat := [1, 2, 3, 2, 1, 3, 3, 2, 4]
def baseStart_1683233 : Nat := 118140960795 + 1683233 * 2 ^ 59
def prefixEnd_1683233 : Nat := 4983230072969 + 3 ^ 40 * 1683233 * 2
def baseEnd_1683233 : Nat := 384136703337563589709537

theorem tailTrace_1683233 : CollatzResearch.WordTrace tailWord_1683233 prefixEnd_1683233 384136703337563589709537 := by
  unfold tailWord_1683233
  simp only [CollatzResearch.WordTrace]
  refine ⟨61392551110941789154590353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40928367407294526103060235 61392551110941789154590353)
  ·
    refine ⟨46044413333206341865942765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61392551110941789154590353 46044413333206341865942765)
    ·
      refine ⟨17266654999952378199728537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46044413333206341865942765 17266654999952378199728537)
      ·
        refine ⟨12949991249964283649796403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17266654999952378199728537 12949991249964283649796403)
        ·
          refine ⟨19424986874946425474694605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12949991249964283649796403 19424986874946425474694605)
          ·
            refine ⟨7284370078104909553010477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19424986874946425474694605 7284370078104909553010477)
            ·
              refine ⟨2731638779289341082378929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7284370078104909553010477 2731638779289341082378929)
              ·
                refine ⟨2048729084467005811784197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2731638779289341082378929 2048729084467005811784197)
                ·
                  refine ⟨384136703337563589709537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2048729084467005811784197 384136703337563589709537)
                  ·
                    rfl

theorem cell21_1683233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_1683233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683233 prefixEnd_1683233 := by exact prefixLift 1683233
  have htrace : WordTrace (prefixWord ++ tailWord_1683233) baseStart_1683233 baseEnd_1683233 := by
    simpa [prefixWord, tailWord_1683233, baseEnd_1683233] using wordTrace_append hprefix tailTrace_1683233
  have hstable : (prefixWord ++ tailWord_1683233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683233).length < 2 ^ (prefixWord ++ tailWord_1683233).sum := by decide
  have hdescent : baseEnd_1683233 < baseStart_1683233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683250 : List Nat := [3, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_1683250 : Nat := 118140960795 + 1683250 * 2 ^ 59
def prefixEnd_1683250 : Nat := 4983230072969 + 3 ^ 40 * 1683250 * 2
def baseEnd_1683250 : Nat := 384140582969175337926169

theorem tailTrace_1683250 : CollatzResearch.WordTrace tailWord_1683250 prefixEnd_1683250 384140582969175337926169 := by
  unfold tailWord_1683250
  simp only [CollatzResearch.WordTrace]
  refine ⟨15348292787970050264489801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40928780767920134038639469 15348292787970050264489801)
  ·
    refine ⟨11511219590977537698367351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15348292787970050264489801 11511219590977537698367351)
    ·
      refine ⟨17266829386466306547551027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11511219590977537698367351 17266829386466306547551027)
      ·
        refine ⟨25900244079699459821326541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17266829386466306547551027 25900244079699459821326541)
        ·
          refine ⟨9712591529887297432997453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25900244079699459821326541 9712591529887297432997453)
          ·
            refine ⟨3642221823707736537374045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9712591529887297432997453 3642221823707736537374045)
            ·
              refine ⟨1365833183890401201515267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3642221823707736537374045 1365833183890401201515267)
              ·
                refine ⟨2048749775835601802272901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365833183890401201515267 2048749775835601802272901)
                ·
                  refine ⟨384140582969175337926169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2048749775835601802272901 384140582969175337926169)
                  ·
                    rfl

theorem cell21_1683250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_1683250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683250 prefixEnd_1683250 := by exact prefixLift 1683250
  have htrace : WordTrace (prefixWord ++ tailWord_1683250) baseStart_1683250 baseEnd_1683250 := by
    simpa [prefixWord, tailWord_1683250, baseEnd_1683250] using wordTrace_append hprefix tailTrace_1683250
  have hstable : (prefixWord ++ tailWord_1683250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683250).length < 2 ^ (prefixWord ++ tailWord_1683250).sum := by decide
  have hdescent : baseEnd_1683250 < baseStart_1683250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683270 : List Nat := [6, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1683270 : Nat := 118140960795 + 1683270 * 2 ^ 59
def prefixEnd_1683270 : Nat := 4983230072969 + 3 ^ 40 * 1683270 * 2
def baseEnd_1683270 : Nat := 384145147241659747592795

theorem tailTrace_1683270 : CollatzResearch.WordTrace tailWord_1683270 prefixEnd_1683270 384145147241659747592795 := by
  unfold tailWord_1683270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1918559394118992014802727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40929267074538496315791509 1918559394118992014802727)
  ·
    refine ⟨2877839091178488022204091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1918559394118992014802727 2877839091178488022204091)
    ·
      refine ⟨4316758636767732033306137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2877839091178488022204091 4316758636767732033306137)
      ·
        refine ⟨3237568977575799024979603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4316758636767732033306137 3237568977575799024979603)
        ·
          refine ⟨4856353466363698537469405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3237568977575799024979603 4856353466363698537469405)
          ·
            refine ⟨1821132549886386951551027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4856353466363698537469405 1821132549886386951551027)
            ·
              refine ⟨2731698824829580427326541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1821132549886386951551027 2731698824829580427326541)
              ·
                refine ⟨1024387059311092660247453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2731698824829580427326541 1024387059311092660247453)
                ·
                  refine ⟨384145147241659747592795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1024387059311092660247453 384145147241659747592795)
                  ·
                    rfl

theorem cell21_1683270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1683270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683270 prefixEnd_1683270 := by exact prefixLift 1683270
  have htrace : WordTrace (prefixWord ++ tailWord_1683270) baseStart_1683270 baseEnd_1683270 := by
    simpa [prefixWord, tailWord_1683270, baseEnd_1683270] using wordTrace_append hprefix tailTrace_1683270
  have hstable : (prefixWord ++ tailWord_1683270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683270).length < 2 ^ (prefixWord ++ tailWord_1683270).sum := by decide
  have hdescent : baseEnd_1683270 < baseStart_1683270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683503 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 6]
def baseStart_1683503 : Nat := 118140960795 + 1683503 * 2 ^ 59
def prefixEnd_1683503 : Nat := 4983230072969 + 3 ^ 40 * 1683503 * 2
def baseEnd_1683503 : Nat := 384198321016103120208985

theorem tailTrace_1683503 : CollatzResearch.WordTrace tailWord_1683503 prefixEnd_1683503 384198321016103120208985 := by
  unfold tailWord_1683503
  simp only [CollatzResearch.WordTrace]
  refine ⟨61402398819963625266919163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40934932546642416844612775 61402398819963625266919163)
  ·
    refine ⟨92103598229945437900378745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61402398819963625266919163 92103598229945437900378745)
    ·
      refine ⟨69077698672459078425284059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92103598229945437900378745 69077698672459078425284059)
      ·
        refine ⟨103616548008688617637926089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69077698672459078425284059 103616548008688617637926089)
        ·
          refine ⟨77712411006516463228444567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103616548008688617637926089 77712411006516463228444567)
          ·
            refine ⟨116568616509774694842666851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77712411006516463228444567 116568616509774694842666851)
            ·
              refine ⟨174852924764662042264000277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116568616509774694842666851 174852924764662042264000277)
              ·
                refine ⟨8196230848343533231125013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 174852924764662042264000277 8196230848343533231125013)
                ·
                  refine ⟨384198321016103120208985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8196230848343533231125013 384198321016103120208985)
                  ·
                    rfl

theorem cell21_1683503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_1683503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683503 prefixEnd_1683503 := by exact prefixLift 1683503
  have htrace : WordTrace (prefixWord ++ tailWord_1683503) baseStart_1683503 baseEnd_1683503 := by
    simpa [prefixWord, tailWord_1683503, baseEnd_1683503] using wordTrace_append hprefix tailTrace_1683503
  have hstable : (prefixWord ++ tailWord_1683503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683503).length < 2 ^ (prefixWord ++ tailWord_1683503).sum := by decide
  have hdescent : baseEnd_1683503 < baseStart_1683503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683520 : List Nat := [2, 1, 1, 2, 2, 4, 1, 4, 4]
def baseStart_1683520 : Nat := 118140960795 + 1683520 * 2 ^ 59
def prefixEnd_1683520 : Nat := 4983230072969 + 3 ^ 40 * 1683520 * 2
def baseEnd_1683520 : Nat := 384202200647714868425617

theorem tailTrace_1683520 : CollatzResearch.WordTrace tailWord_1683520 prefixEnd_1683520 384202200647714868425617 := by
  unfold tailWord_1683520
  simp only [CollatzResearch.WordTrace]
  refine ⟨30701509430451018585144007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40935345907268024780192009 30701509430451018585144007)
  ·
    refine ⟨46052264145676527877716011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30701509430451018585144007 46052264145676527877716011)
    ·
      refine ⟨69078396218514791816574017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46052264145676527877716011 69078396218514791816574017)
      ·
        refine ⟨51808797163886093862430513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69078396218514791816574017 51808797163886093862430513)
        ·
          refine ⟨38856597872914570396822885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51808797163886093862430513 38856597872914570396822885)
          ·
            refine ⟨7285612101171481949404291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38856597872914570396822885 7285612101171481949404291)
            ·
              refine ⟨10928418151757222924106437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7285612101171481949404291 10928418151757222924106437)
              ·
                refine ⟨2049078403454479298269957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10928418151757222924106437 2049078403454479298269957)
                ·
                  refine ⟨384202200647714868425617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049078403454479298269957 384202200647714868425617)
                  ·
                    rfl

theorem cell21_1683520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_1683520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683520 prefixEnd_1683520 := by exact prefixLift 1683520
  have htrace : WordTrace (prefixWord ++ tailWord_1683520) baseStart_1683520 baseEnd_1683520 := by
    simpa [prefixWord, tailWord_1683520, baseEnd_1683520] using wordTrace_append hprefix tailTrace_1683520
  have hstable : (prefixWord ++ tailWord_1683520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683520).length < 2 ^ (prefixWord ++ tailWord_1683520).sum := by decide
  have hdescent : baseEnd_1683520 < baseStart_1683520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683565 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1683565 : Nat := 118140960795 + 1683565 * 2 ^ 59
def prefixEnd_1683565 : Nat := 4983230072969 + 3 ^ 40 * 1683565 * 2
def baseEnd_1683565 : Nat := 384212470260804790175525

theorem tailTrace_1683565 : CollatzResearch.WordTrace tailWord_1683565 prefixEnd_1683565 384212470260804790175525 := by
  unfold tailWord_1683565
  simp only [CollatzResearch.WordTrace]
  refine ⟨61404660145739009855676149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40936440097159339903784099 61404660145739009855676149)
  ·
    refine ⟨5756686888663032173969639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61404660145739009855676149 5756686888663032173969639)
    ·
      refine ⟨8635030332994548260954459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5756686888663032173969639 8635030332994548260954459)
      ·
        refine ⟨12952545499491822391431689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8635030332994548260954459 12952545499491822391431689)
        ·
          refine ⟨9714409124618866793573767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12952545499491822391431689 9714409124618866793573767)
          ·
            refine ⟨14571613686928300190360651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9714409124618866793573767 14571613686928300190360651)
            ·
              refine ⟨21857420530392450285540977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14571613686928300190360651 21857420530392450285540977)
              ·
                refine ⟨16393065397794337714155733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21857420530392450285540977 16393065397794337714155733)
                ·
                  refine ⟨384212470260804790175525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16393065397794337714155733 384212470260804790175525)
                  ·
                    rfl

theorem cell21_1683565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1683565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683565 prefixEnd_1683565 := by exact prefixLift 1683565
  have htrace : WordTrace (prefixWord ++ tailWord_1683565) baseStart_1683565 baseEnd_1683565 := by
    simpa [prefixWord, tailWord_1683565, baseEnd_1683565] using wordTrace_append hprefix tailTrace_1683565
  have hstable : (prefixWord ++ tailWord_1683565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683565).length < 2 ^ (prefixWord ++ tailWord_1683565).sum := by decide
  have hdescent : baseEnd_1683565 < baseStart_1683565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683748 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 6]
def baseStart_1683748 : Nat := 118140960795 + 1683748 * 2 ^ 59
def prefixEnd_1683748 : Nat := 4983230072969 + 3 ^ 40 * 1683748 * 2
def baseEnd_1683748 : Nat := 384254233354037138625151

theorem tailTrace_1683748 : CollatzResearch.WordTrace tailWord_1683748 prefixEnd_1683748 384254233354037138625151 := by
  unfold tailWord_1683748
  simp only [CollatzResearch.WordTrace]
  refine ⟨30705667352038016054793949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40940889802717354739725265 30705667352038016054793949)
  ·
    refine ⟨11514625257014256020547731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30705667352038016054793949 11514625257014256020547731)
    ·
      refine ⟨17271937885521384030821597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11514625257014256020547731 17271937885521384030821597)
      ·
        refine ⟨6476976707070519011558099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17271937885521384030821597 6476976707070519011558099)
        ·
          refine ⟨9715465060605778517337149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6476976707070519011558099 9715465060605778517337149)
          ·
            refine ⟨3643299397727166944001431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9715465060605778517337149 3643299397727166944001431)
            ·
              refine ⟨5464949096590750416002147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643299397727166944001431 5464949096590750416002147)
              ·
                refine ⟨8197423644886125624003221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5464949096590750416002147 8197423644886125624003221)
                ·
                  refine ⟨384254233354037138625151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8197423644886125624003221 384254233354037138625151)
                  ·
                    rfl

theorem cell21_1683748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_1683748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683748 prefixEnd_1683748 := by exact prefixLift 1683748
  have htrace : WordTrace (prefixWord ++ tailWord_1683748) baseStart_1683748 baseEnd_1683748 := by
    simpa [prefixWord, tailWord_1683748, baseEnd_1683748] using wordTrace_append hprefix tailTrace_1683748
  have hstable : (prefixWord ++ tailWord_1683748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683748).length < 2 ^ (prefixWord ++ tailWord_1683748).sum := by decide
  have hdescent : baseEnd_1683748 < baseStart_1683748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683765 : List Nat := [1, 3, 3, 1, 2, 1, 5, 1, 4]
def baseStart_1683765 : Nat := 118140960795 + 1683765 * 2 ^ 59
def prefixEnd_1683765 : Nat := 4983230072969 + 3 ^ 40 * 1683765 * 2
def baseEnd_1683765 : Nat := 384258112985648886841783

theorem tailTrace_1683765 : CollatzResearch.WordTrace tailWord_1683765 prefixEnd_1683765 384258112985648886841783 := by
  unfold tailWord_1683765
  simp only [CollatzResearch.WordTrace]
  refine ⟨61411954745014444012956749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40941303163342962675304499 61411954745014444012956749)
  ·
    refine ⟨23029483029380416504858781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61411954745014444012956749 23029483029380416504858781)
    ·
      refine ⟨8636056136017656189322043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23029483029380416504858781 8636056136017656189322043)
      ·
        refine ⟨12954084204026484283983065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8636056136017656189322043 12954084204026484283983065)
        ·
          refine ⟨9715563153019863212987299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12954084204026484283983065 9715563153019863212987299)
          ·
            refine ⟨14573344729529794819480949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9715563153019863212987299 14573344729529794819480949)
            ·
              refine ⟨1366251068393418264326339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14573344729529794819480949 1366251068393418264326339)
              ·
                refine ⟨2049376602590127396489509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366251068393418264326339 2049376602590127396489509)
                ·
                  refine ⟨384258112985648886841783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049376602590127396489509 384258112985648886841783)
                  ·
                    rfl

theorem cell21_1683765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_1683765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683765 prefixEnd_1683765 := by exact prefixLift 1683765
  have htrace : WordTrace (prefixWord ++ tailWord_1683765) baseStart_1683765 baseEnd_1683765 := by
    simpa [prefixWord, tailWord_1683765, baseEnd_1683765] using wordTrace_append hprefix tailTrace_1683765
  have hstable : (prefixWord ++ tailWord_1683765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683765).length < 2 ^ (prefixWord ++ tailWord_1683765).sum := by decide
  have hdescent : baseEnd_1683765 < baseStart_1683765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683776 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 7]
def baseStart_1683776 : Nat := 118140960795 + 1683776 * 2 ^ 59
def prefixEnd_1683776 : Nat := 4983230072969 + 3 ^ 40 * 1683776 * 2
def baseEnd_1683776 : Nat := 384260623335515312158427

theorem tailTrace_1683776 : CollatzResearch.WordTrace tailWord_1683776 prefixEnd_1683776 384260623335515312158427 := by
  unfold tailWord_1683776
  simp only [CollatzResearch.WordTrace]
  refine ⟨30706177973987296445803591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40941570631983061927738121 30706177973987296445803591)
  ·
    refine ⟨46059266960980944668705387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30706177973987296445803591 46059266960980944668705387)
    ·
      refine ⟨69088900441471417003058081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46059266960980944668705387 69088900441471417003058081)
      ·
        refine ⟨51816675331103562752293561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69088900441471417003058081 51816675331103562752293561)
        ·
          refine ⟨38862506498327672064220171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51816675331103562752293561 38862506498327672064220171)
          ·
            refine ⟨58293759747491508096330257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38862506498327672064220171 58293759747491508096330257)
            ·
              refine ⟨43720319810618631072247693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58293759747491508096330257 43720319810618631072247693)
              ·
                refine ⟨16395119928981986652092885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43720319810618631072247693 16395119928981986652092885)
                ·
                  refine ⟨384260623335515312158427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16395119928981986652092885 384260623335515312158427)
                  ·
                    rfl

theorem cell21_1683776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_1683776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683776 prefixEnd_1683776 := by exact prefixLift 1683776
  have htrace : WordTrace (prefixWord ++ tailWord_1683776) baseStart_1683776 baseEnd_1683776 := by
    simpa [prefixWord, tailWord_1683776, baseEnd_1683776] using wordTrace_append hprefix tailTrace_1683776
  have hstable : (prefixWord ++ tailWord_1683776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683776).length < 2 ^ (prefixWord ++ tailWord_1683776).sum := by decide
  have hdescent : baseEnd_1683776 < baseStart_1683776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683807 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 6]
def baseStart_1683807 : Nat := 118140960795 + 1683807 * 2 ^ 59
def prefixEnd_1683807 : Nat := 4983230072969 + 3 ^ 40 * 1683807 * 2
def baseEnd_1683807 : Nat := 384267697957866147141697

theorem tailTrace_1683807 : CollatzResearch.WordTrace tailWord_1683807 prefixEnd_1683807 384267697957866147141697 := by
  unfold tailWord_1683807
  simp only [CollatzResearch.WordTrace]
  refine ⟨61413486610862285185985675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40942324407241523457323783 61413486610862285185985675)
  ·
    refine ⟨92120229916293427778978513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61413486610862285185985675 92120229916293427778978513)
    ·
      refine ⟨69090172437220070834233885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92120229916293427778978513 69090172437220070834233885)
      ·
        refine ⟨25908814663957526562837707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69090172437220070834233885 25908814663957526562837707)
        ·
          refine ⟨38863221995936289844256561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25908814663957526562837707 38863221995936289844256561)
          ·
            refine ⟨29147416496952217383192421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38863221995936289844256561 29147416496952217383192421)
            ·
              refine ⟨5465140593178540759348579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29147416496952217383192421 5465140593178540759348579)
              ·
                refine ⟨8197710889767811139022869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5465140593178540759348579 8197710889767811139022869)
                ·
                  refine ⟨384267697957866147141697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8197710889767811139022869 384267697957866147141697)
                  ·
                    rfl

theorem cell21_1683807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 6].length) (baseStart_1683807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683807 prefixEnd_1683807 := by exact prefixLift 1683807
  have htrace : WordTrace (prefixWord ++ tailWord_1683807) baseStart_1683807 baseEnd_1683807 := by
    simpa [prefixWord, tailWord_1683807, baseEnd_1683807] using wordTrace_append hprefix tailTrace_1683807
  have hstable : (prefixWord ++ tailWord_1683807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683807).length < 2 ^ (prefixWord ++ tailWord_1683807).sum := by decide
  have hdescent : baseEnd_1683807 < baseStart_1683807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683810 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1683810 : Nat := 118140960795 + 1683810 * 2 ^ 59
def prefixEnd_1683810 : Nat := 4983230072969 + 3 ^ 40 * 1683810 * 2
def baseEnd_1683810 : Nat := 384268382598738808591691

theorem tailTrace_1683810 : CollatzResearch.WordTrace tailWord_1683810 prefixEnd_1683810 384268382598738808591691 := by
  unfold tailWord_1683810
  simp only [CollatzResearch.WordTrace]
  refine ⟨15353399007462854174586221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40942397353234277798896589 15353399007462854174586221)
  ·
    refine ⟨5757524627798570315469833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15353399007462854174586221 5757524627798570315469833)
    ·
      refine ⟨4318143470848927736602375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5757524627798570315469833 4318143470848927736602375)
      ·
        refine ⟨6477215206273391604903563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4318143470848927736602375 6477215206273391604903563)
        ·
          refine ⟨9715822809410087407355345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6477215206273391604903563 9715822809410087407355345)
          ·
            refine ⟨7286867107057565555516509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9715822809410087407355345 7286867107057565555516509)
            ·
              refine ⟨2732575165146587083318691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7286867107057565555516509 2732575165146587083318691)
              ·
                refine ⟨4098862747719880624978037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2732575165146587083318691 4098862747719880624978037)
                ·
                  refine ⟨384268382598738808591691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4098862747719880624978037 384268382598738808591691)
                  ·
                    rfl

theorem cell21_1683810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1683810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683810 prefixEnd_1683810 := by exact prefixLift 1683810
  have htrace : WordTrace (prefixWord ++ tailWord_1683810) baseStart_1683810 baseEnd_1683810 := by
    simpa [prefixWord, tailWord_1683810, baseEnd_1683810] using wordTrace_append hprefix tailTrace_1683810
  have hstable : (prefixWord ++ tailWord_1683810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683810).length < 2 ^ (prefixWord ++ tailWord_1683810).sum := by decide
  have hdescent : baseEnd_1683810 < baseStart_1683810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683824 : List Nat := [2, 1, 1, 1, 4, 4, 1, 3, 4]
def baseStart_1683824 : Nat := 118140960795 + 1683824 * 2 ^ 59
def prefixEnd_1683824 : Nat := 4983230072969 + 3 ^ 40 * 1683824 * 2
def baseEnd_1683824 : Nat := 384271577589477895358329

theorem tailTrace_1683824 : CollatzResearch.WordTrace tailWord_1683824 prefixEnd_1683824 384271577589477895358329 := by
  unfold tailWord_1683824
  simp only [CollatzResearch.WordTrace]
  refine ⟨30707053325900348544677263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40942737767867131392903017 30707053325900348544677263)
  ·
    refine ⟨46060579988850522817015895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30707053325900348544677263 46060579988850522817015895)
    ·
      refine ⟨69090869983275784225523843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46060579988850522817015895 69090869983275784225523843)
      ·
        refine ⟨103636304974913676338285765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69090869983275784225523843 103636304974913676338285765)
        ·
          refine ⟨19431807182796314313428581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103636304974913676338285765 19431807182796314313428581)
          ·
            refine ⟨3643463846774308933767859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19431807182796314313428581 3643463846774308933767859)
            ·
              refine ⟨5465195770161463400651789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643463846774308933767859 5465195770161463400651789)
              ·
                refine ⟨2049448413810548775244421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5465195770161463400651789 2049448413810548775244421)
                ·
                  refine ⟨384271577589477895358329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049448413810548775244421 384271577589477895358329)
                  ·
                    rfl

theorem cell21_1683824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_1683824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683824 prefixEnd_1683824 := by exact prefixLift 1683824
  have htrace : WordTrace (prefixWord ++ tailWord_1683824) baseStart_1683824 baseEnd_1683824 := by
    simpa [prefixWord, tailWord_1683824, baseEnd_1683824] using wordTrace_append hprefix tailTrace_1683824
  have hstable : (prefixWord ++ tailWord_1683824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683824).length < 2 ^ (prefixWord ++ tailWord_1683824).sum := by decide
  have hdescent : baseEnd_1683824 < baseStart_1683824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683973 : List Nat := [1, 3, 1, 1, 2, 2, 11]
def baseStart_1683973 : Nat := 118140960795 + 1683973 * 2 ^ 59
def prefixEnd_1683973 : Nat := 4983230072969 + 3 ^ 40 * 1683973 * 2
def baseEnd_1683973 : Nat := 42700620157720749708299

theorem tailTrace_1683973 : CollatzResearch.WordTrace tailWord_1683973 prefixEnd_1683973 42700620157720749708299 := by
  unfold tailWord_1683973
  simp only [CollatzResearch.WordTrace]
  refine ⟨61419541128260895536528573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40946360752173930357685715 61419541128260895536528573)
  ·
    refine ⟨23032327923097835826198215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61419541128260895536528573 23032327923097835826198215)
    ·
      refine ⟨34548491884646753739297323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23032327923097835826198215 34548491884646753739297323)
      ·
        refine ⟨51822737826970130608945985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34548491884646753739297323 51822737826970130608945985)
        ·
          refine ⟨38867053370227597956709489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51822737826970130608945985 38867053370227597956709489)
          ·
            refine ⟨29150290027670698467532117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38867053370227597956709489 29150290027670698467532117)
            ·
              refine ⟨42700620157720749708299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29150290027670698467532117 42700620157720749708299)
              ·
                rfl

theorem cell21_1683973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 11].length) (baseStart_1683973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683973 prefixEnd_1683973 := by exact prefixLift 1683973
  have htrace : WordTrace (prefixWord ++ tailWord_1683973) baseStart_1683973 baseEnd_1683973 := by
    simpa [prefixWord, tailWord_1683973, baseEnd_1683973] using wordTrace_append hprefix tailTrace_1683973
  have hstable : (prefixWord ++ tailWord_1683973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683973).length < 2 ^ (prefixWord ++ tailWord_1683973).sum := by decide
  have hdescent : baseEnd_1683973 < baseStart_1683973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683979 : List Nat := [1, 1, 1, 1, 7, 2, 3, 2, 3]
def baseStart_1683979 : Nat := 118140960795 + 1683979 * 2 ^ 59
def prefixEnd_1683979 : Nat := 4983230072969 + 3 ^ 40 * 1683979 * 2
def baseEnd_1683979 : Nat := 384306950701232070274679

theorem tailTrace_1683979 : CollatzResearch.WordTrace tailWord_1683979 prefixEnd_1683979 384306950701232070274679 := by
  unfold tailWord_1683979
  simp only [CollatzResearch.WordTrace]
  refine ⟨61419759966239158561246991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40946506644159439040831327 61419759966239158561246991)
  ·
    refine ⟨92129639949358737841870487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61419759966239158561246991 92129639949358737841870487)
    ·
      refine ⟨138194459924038106762805731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92129639949358737841870487 138194459924038106762805731)
      ·
        refine ⟨207291689886057160144208597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138194459924038106762805731 207291689886057160144208597)
        ·
          refine ⟨4858398981704464690879889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 207291689886057160144208597 4858398981704464690879889)
          ·
            refine ⟨3643799236278348518159917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4858398981704464690879889 3643799236278348518159917)
            ·
              refine ⟨1366424713604380694309969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3643799236278348518159917 1366424713604380694309969)
              ·
                refine ⟨1024818535203285520732477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366424713604380694309969 1024818535203285520732477)
                ·
                  refine ⟨384306950701232070274679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1024818535203285520732477 384306950701232070274679)
                  ·
                    rfl

theorem cell21_1683979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 3].length) (baseStart_1683979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1683979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1683979 prefixEnd_1683979 := by exact prefixLift 1683979
  have htrace : WordTrace (prefixWord ++ tailWord_1683979) baseStart_1683979 baseEnd_1683979 := by
    simpa [prefixWord, tailWord_1683979, baseEnd_1683979] using wordTrace_append hprefix tailTrace_1683979
  have hstable : (prefixWord ++ tailWord_1683979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683979).length < 2 ^ (prefixWord ++ tailWord_1683979).sum := by decide
  have hdescent : baseEnd_1683979 < baseStart_1683979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684030 : List Nat := [4, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_1684030 : Nat := 118140960795 + 1684030 * 2 ^ 59
def prefixEnd_1684030 : Nat := 4983230072969 + 3 ^ 40 * 1684030 * 2
def baseEnd_1684030 : Nat := 384318589596067314924575

theorem tailTrace_1684030 : CollatzResearch.WordTrace tailWord_1684030 prefixEnd_1684030 384318589596067314924575 := by
  unfold tailWord_1684030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7677702511131799283919193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40947746726036262847569029 7677702511131799283919193)
  ·
    refine ⟨5758276883348849462939395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7677702511131799283919193 5758276883348849462939395)
    ·
      refine ⟨8637415325023274194409093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5758276883348849462939395 8637415325023274194409093)
      ·
        refine ⟨1619515373441863911451705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8637415325023274194409093 1619515373441863911451705)
        ·
          refine ⟨1214636530081397933588779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1619515373441863911451705 1214636530081397933588779)
          ·
            refine ⟨1821954795122096900383169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214636530081397933588779 1821954795122096900383169)
            ·
              refine ⟨1366466096341572675287377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1821954795122096900383169 1366466096341572675287377)
              ·
                refine ⟨1024849572256179506465533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366466096341572675287377 1024849572256179506465533)
                ·
                  refine ⟨384318589596067314924575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1024849572256179506465533 384318589596067314924575)
                  ·
                    rfl

theorem cell21_1684030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_1684030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684030 prefixEnd_1684030 := by exact prefixLift 1684030
  have htrace : WordTrace (prefixWord ++ tailWord_1684030) baseStart_1684030 baseEnd_1684030 := by
    simpa [prefixWord, tailWord_1684030, baseEnd_1684030] using wordTrace_append hprefix tailTrace_1684030
  have hstable : (prefixWord ++ tailWord_1684030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684030).length < 2 ^ (prefixWord ++ tailWord_1684030).sum := by decide
  have hdescent : baseEnd_1684030 < baseStart_1684030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684052 : List Nat := [2, 4, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1684052 : Nat := 118140960795 + 1684052 * 2 ^ 59
def prefixEnd_1684052 : Nat := 4983230072969 + 3 ^ 40 * 1684052 * 2
def baseEnd_1684052 : Nat := 384323610295800165557863

theorem tailTrace_1684052 : CollatzResearch.WordTrace tailWord_1684052 prefixEnd_1684052 384323610295800165557863 := by
  unfold tailWord_1684052
  simp only [CollatzResearch.WordTrace]
  refine ⟨30711211247487346014327205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40948281663316461352436273 30711211247487346014327205)
  ·
    refine ⟨5758352108903877377686351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30711211247487346014327205 5758352108903877377686351)
    ·
      refine ⟨8637528163355816066529527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5758352108903877377686351 8637528163355816066529527)
      ·
        refine ⟨12956292245033724099794291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8637528163355816066529527 12956292245033724099794291)
        ·
          refine ⟨19434438367550586149691437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12956292245033724099794291 19434438367550586149691437)
          ·
            refine ⟨7287914387831469806134289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19434438367550586149691437 7287914387831469806134289)
            ·
              refine ⟨5465935790873602354600717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7287914387831469806134289 5465935790873602354600717)
              ·
                refine ⟨2049725921577600882975269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5465935790873602354600717 2049725921577600882975269)
                ·
                  refine ⟨384323610295800165557863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049725921577600882975269 384323610295800165557863)
                  ·
                    rfl

theorem cell21_1684052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1684052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684052 prefixEnd_1684052 := by exact prefixLift 1684052
  have htrace : WordTrace (prefixWord ++ tailWord_1684052) baseStart_1684052 baseEnd_1684052 := by
    simpa [prefixWord, tailWord_1684052, baseEnd_1684052] using wordTrace_append hprefix tailTrace_1684052
  have hstable : (prefixWord ++ tailWord_1684052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684052).length < 2 ^ (prefixWord ++ tailWord_1684052).sum := by decide
  have hdescent : baseEnd_1684052 < baseStart_1684052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684086 : List Nat := [5, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1684086 : Nat := 118140960795 + 1684086 * 2 ^ 59
def prefixEnd_1684086 : Nat := 4983230072969 + 3 ^ 40 * 1684086 * 2
def baseEnd_1684086 : Nat := 384331369559023661991127

theorem tailTrace_1684086 : CollatzResearch.WordTrace tailWord_1684086 prefixEnd_1684086 384331369559023661991127 := by
  unfold tailWord_1684086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3838978911053219739712007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40949108384567677223594741 3838978911053219739712007)
  ·
    refine ⟨5758468366579829609568011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3838978911053219739712007 5758468366579829609568011)
    ·
      refine ⟨8637702549869744414352017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5758468366579829609568011 8637702549869744414352017)
      ·
        refine ⟨6478276912402308310764013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8637702549869744414352017 6478276912402308310764013)
        ·
          refine ⟨2429353842150865616536505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6478276912402308310764013 2429353842150865616536505)
          ·
            refine ⟨1822015381613149212402379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2429353842150865616536505 1822015381613149212402379)
            ·
              refine ⟨2733023072419723818603569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822015381613149212402379 2733023072419723818603569)
              ·
                refine ⟨2049767304314792863952677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2733023072419723818603569 2049767304314792863952677)
                ·
                  refine ⟨384331369559023661991127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049767304314792863952677 384331369559023661991127)
                  ·
                    rfl

theorem cell21_1684086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1684086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684086 prefixEnd_1684086 := by exact prefixLift 1684086
  have htrace : WordTrace (prefixWord ++ tailWord_1684086) baseStart_1684086 baseEnd_1684086 := by
    simpa [prefixWord, tailWord_1684086, baseEnd_1684086] using wordTrace_append hprefix tailTrace_1684086
  have hstable : (prefixWord ++ tailWord_1684086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684086).length < 2 ^ (prefixWord ++ tailWord_1684086).sum := by decide
  have hdescent : baseEnd_1684086 < baseStart_1684086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684097 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 5]
def baseStart_1684097 : Nat := 118140960795 + 1684097 * 2 ^ 59
def prefixEnd_1684097 : Nat := 4983230072969 + 3 ^ 40 * 1684097 * 2
def baseEnd_1684097 : Nat := 384333879908890087307771

theorem tailTrace_1684097 : CollatzResearch.WordTrace tailWord_1684097 prefixEnd_1684097 384333879908890087307771 := by
  unfold tailWord_1684097
  simp only [CollatzResearch.WordTrace]
  refine ⟨61424063779811664714042545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40949375853207776476028363 61424063779811664714042545)
  ·
    refine ⟨46068047834858748535531909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61424063779811664714042545 46068047834858748535531909)
    ·
      refine ⟨8637758969036015350412233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46068047834858748535531909 8637758969036015350412233)
      ·
        refine ⟨6478319226777011512809175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8637758969036015350412233 6478319226777011512809175)
        ·
          refine ⟨9717478840165517269213763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6478319226777011512809175 9717478840165517269213763)
          ·
            refine ⟨14576218260248275903820645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9717478840165517269213763 14576218260248275903820645)
            ·
              refine ⟨2733040923796551731966371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14576218260248275903820645 2733040923796551731966371)
              ·
                refine ⟨4099561385694827597949557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733040923796551731966371 4099561385694827597949557)
                ·
                  refine ⟨384333879908890087307771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4099561385694827597949557 384333879908890087307771)
                  ·
                    rfl

theorem cell21_1684097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_1684097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684097 prefixEnd_1684097 := by exact prefixLift 1684097
  have htrace : WordTrace (prefixWord ++ tailWord_1684097) baseStart_1684097 baseEnd_1684097 := by
    simpa [prefixWord, tailWord_1684097, baseEnd_1684097] using wordTrace_append hprefix tailTrace_1684097
  have hstable : (prefixWord ++ tailWord_1684097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684097).length < 2 ^ (prefixWord ++ tailWord_1684097).sum := by decide
  have hdescent : baseEnd_1684097 < baseStart_1684097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684207 : List Nat := [1, 1, 2, 1, 5, 4, 2, 2, 3]
def baseStart_1684207 : Nat := 118140960795 + 1684207 * 2 ^ 59
def prefixEnd_1684207 : Nat := 4983230072969 + 3 ^ 40 * 1684207 * 2
def baseEnd_1684207 : Nat := 384358983407554340474213

theorem tailTrace_1684207 : CollatzResearch.WordTrace tailWord_1684207 prefixEnd_1684207 384358983407554340474213 := by
  unfold tailWord_1684207
  simp only [CollatzResearch.WordTrace]
  refine ⟨61428075809413153500546875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40952050539608769000364583 61428075809413153500546875)
  ·
    refine ⟨92142113714119730250820313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61428075809413153500546875 92142113714119730250820313)
    ·
      refine ⟨69106585285589797688115235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92142113714119730250820313 69106585285589797688115235)
      ·
        refine ⟨103659877928384696532172853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69106585285589797688115235 103659877928384696532172853)
        ·
          refine ⟨9718113555786065299891205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103659877928384696532172853 9718113555786065299891205)
          ·
            refine ⟨1822146291709887243729601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9718113555786065299891205 1822146291709887243729601)
            ·
              refine ⟨1366609718782415432797201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1822146291709887243729601 1366609718782415432797201)
              ·
                refine ⟨1024957289086811574597901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366609718782415432797201 1024957289086811574597901)
                ·
                  refine ⟨384358983407554340474213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1024957289086811574597901 384358983407554340474213)
                  ·
                    rfl

theorem cell21_1684207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 3].length) (baseStart_1684207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684207 prefixEnd_1684207 := by exact prefixLift 1684207
  have htrace : WordTrace (prefixWord ++ tailWord_1684207) baseStart_1684207 baseEnd_1684207 := by
    simpa [prefixWord, tailWord_1684207, baseEnd_1684207] using wordTrace_append hprefix tailTrace_1684207
  have hstable : (prefixWord ++ tailWord_1684207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684207).length < 2 ^ (prefixWord ++ tailWord_1684207).sum := by decide
  have hdescent : baseEnd_1684207 < baseStart_1684207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684232 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 7]
def baseStart_1684232 : Nat := 118140960795 + 1684232 * 2 ^ 59
def prefixEnd_1684232 : Nat := 4983230072969 + 3 ^ 40 * 1684232 * 2
def baseEnd_1684232 : Nat := 384364688748159852557495

theorem tailTrace_1684232 : CollatzResearch.WordTrace tailWord_1684232 prefixEnd_1684232 384364688748159852557495 := by
  unfold tailWord_1684232
  simp only [CollatzResearch.WordTrace]
  refine ⟨30714493817161291385103475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40952658422881721846804633 30714493817161291385103475)
  ·
    refine ⟨46071740725741937077655213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30714493817161291385103475 46071740725741937077655213)
    ·
      refine ⟨17276902772153226404120705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46071740725741937077655213 17276902772153226404120705)
      ·
        refine ⟨12957677079114919803090529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17276902772153226404120705 12957677079114919803090529)
        ·
          refine ⟨9718257809336189852317897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12957677079114919803090529 9718257809336189852317897)
          ·
            refine ⟨7288693357002142389238423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9718257809336189852317897 7288693357002142389238423)
            ·
              refine ⟨10933040035503213583857635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7288693357002142389238423 10933040035503213583857635)
              ·
                refine ⟨16399560053254820375786453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10933040035503213583857635 16399560053254820375786453)
                ·
                  refine ⟨384364688748159852557495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16399560053254820375786453 384364688748159852557495)
                  ·
                    rfl

theorem cell21_1684232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_1684232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684232 prefixEnd_1684232 := by exact prefixLift 1684232
  have htrace : WordTrace (prefixWord ++ tailWord_1684232) baseStart_1684232 baseEnd_1684232 := by
    simpa [prefixWord, tailWord_1684232, baseEnd_1684232] using wordTrace_append hprefix tailTrace_1684232
  have hstable : (prefixWord ++ tailWord_1684232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684232).length < 2 ^ (prefixWord ++ tailWord_1684232).sum := by decide
  have hdescent : baseEnd_1684232 < baseStart_1684232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684280 : List Nat := [2, 1, 2, 1, 3, 2, 5, 1, 4]
def baseStart_1684280 : Nat := 118140960795 + 1684280 * 2 ^ 59
def prefixEnd_1684280 : Nat := 4983230072969 + 3 ^ 40 * 1684280 * 2
def baseEnd_1684280 : Nat := 384375643002122435757397

theorem tailTrace_1684280 : CollatzResearch.WordTrace tailWord_1684280 prefixEnd_1684280 384375643002122435757397 := by
  unfold tailWord_1684280
  simp only [CollatzResearch.WordTrace]
  refine ⟨30715369169074343483977147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40953825558765791311969529 30715369169074343483977147)
  ·
    refine ⟨46073053753611515225965721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30715369169074343483977147 46073053753611515225965721)
    ·
      refine ⟨34554790315208636419474291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46073053753611515225965721 34554790315208636419474291)
      ·
        refine ⟨51832185472812954629211437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34554790315208636419474291 51832185472812954629211437)
        ·
          refine ⟨19437069552304857985954289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51832185472812954629211437 19437069552304857985954289)
          ·
            refine ⟨14577802164228643489465717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19437069552304857985954289 14577802164228643489465717)
            ·
              refine ⟨1366668952896435327137411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14577802164228643489465717 1366668952896435327137411)
              ·
                refine ⟨2050003429344652990706117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366668952896435327137411 2050003429344652990706117)
                ·
                  refine ⟨384375643002122435757397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050003429344652990706117 384375643002122435757397)
                  ·
                    rfl

theorem cell21_1684280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_1684280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684280 prefixEnd_1684280 := by exact prefixLift 1684280
  have htrace : WordTrace (prefixWord ++ tailWord_1684280) baseStart_1684280 baseEnd_1684280 := by
    simpa [prefixWord, tailWord_1684280, baseEnd_1684280] using wordTrace_append hprefix tailTrace_1684280
  have hstable : (prefixWord ++ tailWord_1684280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684280).length < 2 ^ (prefixWord ++ tailWord_1684280).sum := by decide
  have hdescent : baseEnd_1684280 < baseStart_1684280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684325 : List Nat := [1, 3, 1, 3, 1, 1, 2, 6, 3]
def baseStart_1684325 : Nat := 118140960795 + 1684325 * 2 ^ 59
def prefixEnd_1684325 : Nat := 4983230072969 + 3 ^ 40 * 1684325 * 2
def baseEnd_1684325 : Nat := 384385912615212357507305

theorem tailTrace_1684325 : CollatzResearch.WordTrace tailWord_1684325 prefixEnd_1684325 384385912615212357507305 := by
  unfold tailWord_1684325
  simp only [CollatzResearch.WordTrace]
  refine ⟨61432379622985659653342429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40954919748657106435561619 61432379622985659653342429)
  ·
    refine ⟨23037142358619622370003411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61432379622985659653342429 23037142358619622370003411)
    ·
      refine ⟨34555713537929433555005117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23037142358619622370003411 34555713537929433555005117)
      ·
        refine ⟨12958392576723537583126919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34555713537929433555005117 12958392576723537583126919)
        ·
          refine ⟨19437588865085306374690379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12958392576723537583126919 19437588865085306374690379)
          ·
            refine ⟨29156383297627959562035569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19437588865085306374690379 29156383297627959562035569)
            ·
              refine ⟨21867287473220969671526677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29156383297627959562035569 21867287473220969671526677)
              ·
                refine ⟨1025029100307232953352813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21867287473220969671526677 1025029100307232953352813)
                ·
                  refine ⟨384385912615212357507305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025029100307232953352813 384385912615212357507305)
                  ·
                    rfl

theorem cell21_1684325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_1684325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684325 prefixEnd_1684325 := by exact prefixLift 1684325
  have htrace : WordTrace (prefixWord ++ tailWord_1684325) baseStart_1684325 baseEnd_1684325 := by
    simpa [prefixWord, tailWord_1684325, baseEnd_1684325] using wordTrace_append hprefix tailTrace_1684325
  have hstable : (prefixWord ++ tailWord_1684325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684325).length < 2 ^ (prefixWord ++ tailWord_1684325).sum := by decide
  have hdescent : baseEnd_1684325 < baseStart_1684325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684370 : List Nat := [3, 2, 3, 2, 2, 9]
def baseStart_1684370 : Nat := 118140960795 + 1684370 * 2 ^ 59
def prefixEnd_1684370 : Nat := 4983230072969 + 3 ^ 40 * 1684370 * 2
def baseEnd_1684370 : Nat := 14236895638085269602119

theorem tailTrace_1684370 : CollatzResearch.WordTrace tailWord_1684370 prefixEnd_1684370 14236895638085269602119 := by
  unfold tailWord_1684370
  simp only [CollatzResearch.WordTrace]
  refine ⟨15358505226955658084682641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40956013938548421559153709 15358505226955658084682641)
  ·
    refine ⟨11518878920216743563511981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15358505226955658084682641 11518878920216743563511981)
    ·
      refine ⟨4319579595081278836316993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11518878920216743563511981 4319579595081278836316993)
      ·
        refine ⟨3239684696310959127237745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4319579595081278836316993 3239684696310959127237745)
        ·
          refine ⟨2429763522233219345428309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3239684696310959127237745 2429763522233219345428309)
          ·
            refine ⟨14236895638085269602119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2429763522233219345428309 14236895638085269602119)
            ·
              rfl

theorem cell21_1684370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 9].length) (baseStart_1684370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684370 prefixEnd_1684370 := by exact prefixLift 1684370
  have htrace : WordTrace (prefixWord ++ tailWord_1684370) baseStart_1684370 baseEnd_1684370 := by
    simpa [prefixWord, tailWord_1684370, baseEnd_1684370] using wordTrace_append hprefix tailTrace_1684370
  have hstable : (prefixWord ++ tailWord_1684370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684370).length < 2 ^ (prefixWord ++ tailWord_1684370).sum := by decide
  have hdescent : baseEnd_1684370 < baseStart_1684370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684401 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 5]
def baseStart_1684401 : Nat := 118140960795 + 1684401 * 2 ^ 59
def prefixEnd_1684401 : Nat := 4983230072969 + 3 ^ 40 * 1684401 * 2
def baseEnd_1684401 : Nat := 384403256850653114240483

theorem tailTrace_1684401 : CollatzResearch.WordTrace tailWord_1684401 prefixEnd_1684401 384403256850653114240483 := by
  unfold tailWord_1684401
  simp only [CollatzResearch.WordTrace]
  refine ⟨61435151570710324633109057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40956767713806883088739371 61435151570710324633109057)
  ·
    refine ⟨46076363678032743474831793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61435151570710324633109057 46076363678032743474831793)
    ·
      refine ⟨34557272758524557606123845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46076363678032743474831793 34557272758524557606123845)
      ·
        refine ⟨6479488642223354551148221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34557272758524557606123845 6479488642223354551148221)
        ·
          refine ⟨2429808240833757956680583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6479488642223354551148221 2429808240833757956680583)
          ·
            refine ⟨3644712361250636935020875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429808240833757956680583 3644712361250636935020875)
            ·
              refine ⟨5467068541875955402531313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3644712361250636935020875 5467068541875955402531313)
              ·
                refine ⟨4100301406406966551898485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5467068541875955402531313 4100301406406966551898485)
                ·
                  refine ⟨384403256850653114240483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4100301406406966551898485 384403256850653114240483)
                  ·
                    rfl

theorem cell21_1684401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_1684401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684401 prefixEnd_1684401 := by exact prefixLift 1684401
  have htrace : WordTrace (prefixWord ++ tailWord_1684401) baseStart_1684401 baseEnd_1684401 := by
    simpa [prefixWord, tailWord_1684401, baseEnd_1684401] using wordTrace_append hprefix tailTrace_1684401
  have hstable : (prefixWord ++ tailWord_1684401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684401).length < 2 ^ (prefixWord ++ tailWord_1684401).sum := by decide
  have hdescent : baseEnd_1684401 < baseStart_1684401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684404 : List Nat := [2, 5, 2, 1, 1, 2, 3, 5]
def baseStart_1684404 : Nat := 118140960795 + 1684404 * 2 ^ 59
def prefixEnd_1684404 : Nat := 4983230072969 + 3 ^ 40 * 1684404 * 2
def baseEnd_1684404 : Nat := 128134647163841925230159

theorem tailTrace_1684404 : CollatzResearch.WordTrace tailWord_1684404 prefixEnd_1684404 128134647163841925230159 := by
  unfold tailWord_1684404
  simp only [CollatzResearch.WordTrace]
  refine ⟨30717630494849728072734133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40956840659799637430312177 30717630494849728072734133)
  ·
    refine ⟨2879777858892162006818825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30717630494849728072734133 2879777858892162006818825)
    ·
      refine ⟨2159833394169121505114119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2879777858892162006818825 2159833394169121505114119)
      ·
        refine ⟨3239750091253682257671179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2159833394169121505114119 3239750091253682257671179)
        ·
          refine ⟨4859625136880523386506769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3239750091253682257671179 4859625136880523386506769)
          ·
            refine ⟨3644718852660392539880077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4859625136880523386506769 3644718852660392539880077)
            ·
              refine ⟨1366769569747647202455029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3644718852660392539880077 1366769569747647202455029)
              ·
                refine ⟨128134647163841925230159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1366769569747647202455029 128134647163841925230159)
                ·
                  rfl

theorem cell21_1684404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 5].length) (baseStart_1684404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684404 prefixEnd_1684404 := by exact prefixLift 1684404
  have htrace : WordTrace (prefixWord ++ tailWord_1684404) baseStart_1684404 baseEnd_1684404 := by
    simpa [prefixWord, tailWord_1684404, baseEnd_1684404] using wordTrace_append hprefix tailTrace_1684404
  have hstable : (prefixWord ++ tailWord_1684404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684404).length < 2 ^ (prefixWord ++ tailWord_1684404).sum := by decide
  have hdescent : baseEnd_1684404 < baseStart_1684404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684469 : List Nat := [1, 3, 5, 2, 2, 1, 1, 3, 3]
def baseStart_1684469 : Nat := 118140960795 + 1684469 * 2 ^ 59
def prefixEnd_1684469 : Nat := 4983230072969 + 3 ^ 40 * 1684469 * 2
def baseEnd_1684469 : Nat := 384418775377100107107011

theorem tailTrace_1684469 : CollatzResearch.WordTrace tailWord_1684469 prefixEnd_1684469 384418775377100107107011 := by
  unfold tailWord_1684469
  simp only [CollatzResearch.WordTrace]
  refine ⟨61437631734463972246584461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40958421156309314831056307 61437631734463972246584461)
  ·
    refine ⟨23039111900423989592469173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61437631734463972246584461 23039111900423989592469173)
    ·
      refine ⟨2159916740664749024293985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23039111900423989592469173 2159916740664749024293985)
      ·
        refine ⟨1619937555498561768220489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2159916740664749024293985 1619937555498561768220489)
        ·
          refine ⟨1214953166623921326165367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1619937555498561768220489 1214953166623921326165367)
          ·
            refine ⟨1822429749935881989248051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214953166623921326165367 1822429749935881989248051)
            ·
              refine ⟨2733644624903822983872077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822429749935881989248051 2733644624903822983872077)
              ·
                refine ⟨1025116734338933618952029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2733644624903822983872077 1025116734338933618952029)
                ·
                  refine ⟨384418775377100107107011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025116734338933618952029 384418775377100107107011)
                  ·
                    rfl

theorem cell21_1684469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_1684469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684469 prefixEnd_1684469 := by exact prefixLift 1684469
  have htrace : WordTrace (prefixWord ++ tailWord_1684469) baseStart_1684469 baseEnd_1684469 := by
    simpa [prefixWord, tailWord_1684469, baseEnd_1684469] using wordTrace_append hprefix tailTrace_1684469
  have hstable : (prefixWord ++ tailWord_1684469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684469).length < 2 ^ (prefixWord ++ tailWord_1684469).sum := by decide
  have hdescent : baseEnd_1684469 < baseStart_1684469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684508 : List Nat := [2, 2, 3, 1, 4, 1, 1, 3, 4]
def baseStart_1684508 : Nat := 118140960795 + 1684508 * 2 ^ 59
def prefixEnd_1684508 : Nat := 4983230072969 + 3 ^ 40 * 1684508 * 2
def baseEnd_1684508 : Nat := 384427675708444705956931

theorem tailTrace_1684508 : CollatzResearch.WordTrace tailWord_1684508 prefixEnd_1684508 384427675708444705956931 := by
  unfold tailWord_1684508
  simp only [CollatzResearch.WordTrace]
  refine ⟨30719527090661340953627089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40959369454215121271502785 30719527090661340953627089)
  ·
    refine ⟨23039645317996005715220317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30719527090661340953627089 23039645317996005715220317)
    ·
      refine ⟨8639866994248502143207619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23039645317996005715220317 8639866994248502143207619)
      ·
        refine ⟨12959800491372753214811429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8639866994248502143207619 12959800491372753214811429)
        ·
          refine ⟨2429962592132391227777143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12959800491372753214811429 2429962592132391227777143)
          ·
            refine ⟨3644943888198586841665715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429962592132391227777143 3644943888198586841665715)
            ·
              refine ⟨5467415832297880262498573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3644943888198586841665715 5467415832297880262498573)
              ·
                refine ⟨2050280937111705098436965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5467415832297880262498573 2050280937111705098436965)
                ·
                  refine ⟨384427675708444705956931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050280937111705098436965 384427675708444705956931)
                  ·
                    rfl

theorem cell21_1684508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_1684508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684508 prefixEnd_1684508 := by exact prefixLift 1684508
  have htrace : WordTrace (prefixWord ++ tailWord_1684508) baseStart_1684508 baseEnd_1684508 := by
    simpa [prefixWord, tailWord_1684508, baseEnd_1684508] using wordTrace_append hprefix tailTrace_1684508
  have hstable : (prefixWord ++ tailWord_1684508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684508).length < 2 ^ (prefixWord ++ tailWord_1684508).sum := by decide
  have hdescent : baseEnd_1684508 < baseStart_1684508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684601 : List Nat := [1, 2, 1, 3, 6, 1, 1, 2, 4]
def baseStart_1684601 : Nat := 118140960795 + 1684601 * 2 ^ 59
def prefixEnd_1684601 : Nat := 4983230072969 + 3 ^ 40 * 1684601 * 2
def baseEnd_1684601 : Nat := 384448899575497210906741

theorem tailTrace_1684601 : CollatzResearch.WordTrace tailWord_1684601 prefixEnd_1684601 384448899575497210906741 := by
  unfold tailWord_1684601
  simp only [CollatzResearch.WordTrace]
  refine ⟨61442446169985758790389657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40961630779990505860259771 61442446169985758790389657)
  ·
    refine ⟨46081834627489319092792243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61442446169985758790389657 46081834627489319092792243)
    ·
      refine ⟨69122751941233978639188365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46081834627489319092792243 69122751941233978639188365)
      ·
        refine ⟨25921031977962741989695637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69122751941233978639188365 25921031977962741989695637)
        ·
          refine ⟨1215048373967003530766983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25921031977962741989695637 1215048373967003530766983)
          ·
            refine ⟨1822572560950505296150475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215048373967003530766983 1822572560950505296150475)
            ·
              refine ⟨2733858841425757944225713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822572560950505296150475 2733858841425757944225713)
              ·
                refine ⟨2050394131069318458169285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2733858841425757944225713 2050394131069318458169285)
                ·
                  refine ⟨384448899575497210906741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050394131069318458169285 384448899575497210906741)
                  ·
                    rfl

theorem cell21_1684601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 4].length) (baseStart_1684601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684601 prefixEnd_1684601 := by exact prefixLift 1684601
  have htrace : WordTrace (prefixWord ++ tailWord_1684601) baseStart_1684601 baseEnd_1684601 := by
    simpa [prefixWord, tailWord_1684601, baseEnd_1684601] using wordTrace_append hprefix tailTrace_1684601
  have hstable : (prefixWord ++ tailWord_1684601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684601).length < 2 ^ (prefixWord ++ tailWord_1684601).sum := by decide
  have hdescent : baseEnd_1684601 < baseStart_1684601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684612 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 5]
def baseStart_1684612 : Nat := 118140960795 + 1684612 * 2 ^ 59
def prefixEnd_1684612 : Nat := 4983230072969 + 3 ^ 40 * 1684612 * 2
def baseEnd_1684612 : Nat := 384451409925363636223385

theorem tailTrace_1684612 : CollatzResearch.WordTrace tailWord_1684612 prefixEnd_1684612 384451409925363636223385 := by
  unfold tailWord_1684612
  simp only [CollatzResearch.WordTrace]
  refine ⟨30721423686472953834520045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40961898248630605112693393 30721423686472953834520045)
  ·
    refine ⟨11520533882427357687945017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30721423686472953834520045 11520533882427357687945017)
    ·
      refine ⟨8640400411820518265958763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11520533882427357687945017 8640400411820518265958763)
      ·
        refine ⟨12960600617730777398938145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8640400411820518265958763 12960600617730777398938145)
        ·
          refine ⟨9720450463298083049203609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12960600617730777398938145 9720450463298083049203609)
          ·
            refine ⟨7290337847473562286902707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9720450463298083049203609 7290337847473562286902707)
            ·
              refine ⟨10935506771210343430354061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7290337847473562286902707 10935506771210343430354061)
              ·
                refine ⟨4100815039203878786382773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10935506771210343430354061 4100815039203878786382773)
                ·
                  refine ⟨384451409925363636223385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4100815039203878786382773 384451409925363636223385)
                  ·
                    rfl

theorem cell21_1684612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_1684612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684612 prefixEnd_1684612 := by exact prefixLift 1684612
  have htrace : WordTrace (prefixWord ++ tailWord_1684612) baseStart_1684612 baseEnd_1684612 := by
    simpa [prefixWord, tailWord_1684612, baseEnd_1684612] using wordTrace_append hprefix tailTrace_1684612
  have hstable : (prefixWord ++ tailWord_1684612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684612).length < 2 ^ (prefixWord ++ tailWord_1684612).sum := by decide
  have hdescent : baseEnd_1684612 < baseStart_1684612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684657 : List Nat := [1, 2, 2, 5, 1, 1, 9]
def baseStart_1684657 : Nat := 118140960795 + 1684657 * 2 ^ 59
def prefixEnd_1684657 : Nat := 4983230072969 + 3 ^ 40 * 1684657 * 2
def baseEnd_1684657 : Nat := 42717964393161506441477

theorem tailTrace_1684657 : CollatzResearch.WordTrace tailWord_1684657 prefixEnd_1684657 42717964393161506441477 := by
  unfold tailWord_1684657
  simp only [CollatzResearch.WordTrace]
  refine ⟨61444488657782880354428225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40962992438521920236285483 61444488657782880354428225)
  ·
    refine ⟨46083366493337160265821169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61444488657782880354428225 46083366493337160265821169)
    ·
      refine ⟨34562524870002870199365877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46083366493337160265821169 34562524870002870199365877)
      ·
        refine ⟨3240236706562769081190551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34562524870002870199365877 3240236706562769081190551)
        ·
          refine ⟨4860355059844153621785827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240236706562769081190551 4860355059844153621785827)
          ·
            refine ⟨7290532589766230432678741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860355059844153621785827 7290532589766230432678741)
            ·
              refine ⟨42717964393161506441477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7290532589766230432678741 42717964393161506441477)
              ·
                rfl

theorem cell21_1684657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 9].length) (baseStart_1684657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684657 prefixEnd_1684657 := by exact prefixLift 1684657
  have htrace : WordTrace (prefixWord ++ tailWord_1684657) baseStart_1684657 baseEnd_1684657 := by
    simpa [prefixWord, tailWord_1684657, baseEnd_1684657] using wordTrace_append hprefix tailTrace_1684657
  have hstable : (prefixWord ++ tailWord_1684657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684657).length < 2 ^ (prefixWord ++ tailWord_1684657).sum := by decide
  have hdescent : baseEnd_1684657 < baseStart_1684657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684716 : List Nat := [2, 2, 1, 1, 2, 13]
def baseStart_1684716 : Nat := 118140960795 + 1684716 * 2 ^ 59
def prefixEnd_1684716 : Nat := 4983230072969 + 3 ^ 40 * 1684716 * 2
def baseEnd_1684716 : Nat := 14239820153417872832957

theorem tailTrace_1684716 : CollatzResearch.WordTrace tailWord_1684716 prefixEnd_1684716 14239820153417872832957 := by
  unfold tailWord_1684716
  simp only [CollatzResearch.WordTrace]
  refine ⟨30723320282284566715413001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40964427043046088953884001 30723320282284566715413001)
  ·
    refine ⟨23042490211713425036559751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30723320282284566715413001 23042490211713425036559751)
    ·
      refine ⟨34563735317570137554839627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23042490211713425036559751 34563735317570137554839627)
      ·
        refine ⟨51845602976355206332259441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34563735317570137554839627 51845602976355206332259441)
        ·
          refine ⟨38884202232266404749194581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51845602976355206332259441 38884202232266404749194581)
          ·
            refine ⟨14239820153417872832957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 38884202232266404749194581 14239820153417872832957)
            ·
              rfl

theorem cell21_1684716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 13].length) (baseStart_1684716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684716 prefixEnd_1684716 := by exact prefixLift 1684716
  have htrace : WordTrace (prefixWord ++ tailWord_1684716) baseStart_1684716 baseEnd_1684716 := by
    simpa [prefixWord, tailWord_1684716, baseEnd_1684716] using wordTrace_append hprefix tailTrace_1684716
  have hstable : (prefixWord ++ tailWord_1684716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684716).length < 2 ^ (prefixWord ++ tailWord_1684716).sum := by decide
  have hdescent : baseEnd_1684716 < baseStart_1684716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684722 : List Nat := [3, 2, 1, 3, 3, 1, 1, 4, 3]
def baseStart_1684722 : Nat := 118140960795 + 1684722 * 2 ^ 59
def prefixEnd_1684722 : Nat := 4983230072969 + 3 ^ 40 * 1684722 * 2
def baseEnd_1684722 : Nat := 384476513424027889389827

theorem tailTrace_1684722 : CollatzResearch.WordTrace tailWord_1684722 prefixEnd_1684722 384476513424027889389827 := by
  unfold tailWord_1684722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15361714850636849113886105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40964572935031597637029613 15361714850636849113886105)
  ·
    refine ⟨11521286137977636835414579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15361714850636849113886105 11521286137977636835414579)
    ·
      refine ⟨17281929206966455253121869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11521286137977636835414579 17281929206966455253121869)
      ·
        refine ⟨6480723452612420719920701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17281929206966455253121869 6480723452612420719920701)
        ·
          refine ⟨2430271294729657769970263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6480723452612420719920701 2430271294729657769970263)
          ·
            refine ⟨3645406942094486654955395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2430271294729657769970263 3645406942094486654955395)
            ·
              refine ⟨5468110413141729982433093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3645406942094486654955395 5468110413141729982433093)
              ·
                refine ⟨1025270702464074371706205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5468110413141729982433093 1025270702464074371706205)
                ·
                  refine ⟨384476513424027889389827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025270702464074371706205 384476513424027889389827)
                  ·
                    rfl

theorem cell21_1684722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_1684722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684722 prefixEnd_1684722 := by exact prefixLift 1684722
  have htrace : WordTrace (prefixWord ++ tailWord_1684722) baseStart_1684722 baseEnd_1684722 := by
    simpa [prefixWord, tailWord_1684722, baseEnd_1684722] using wordTrace_append hprefix tailTrace_1684722
  have hstable : (prefixWord ++ tailWord_1684722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684722).length < 2 ^ (prefixWord ++ tailWord_1684722).sum := by decide
  have hdescent : baseEnd_1684722 < baseStart_1684722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684747 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 7]
def baseStart_1684747 : Nat := 118140960795 + 1684747 * 2 ^ 59
def prefixEnd_1684747 : Nat := 4983230072969 + 3 ^ 40 * 1684747 * 2
def baseEnd_1684747 : Nat := 384482218764633401473109

theorem tailTrace_1684747 : CollatzResearch.WordTrace tailWord_1684747 prefixEnd_1684747 384482218764633401473109 := by
  unfold tailWord_1684747
  simp only [CollatzResearch.WordTrace]
  refine ⟨61447771227456825725204495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40965180818304550483469663 61447771227456825725204495)
  ·
    refine ⟨92171656841185238587806743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61447771227456825725204495 92171656841185238587806743)
    ·
      refine ⟨138257485261777857881710115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92171656841185238587806743 138257485261777857881710115)
      ·
        refine ⟨207386227892666786822565173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138257485261777857881710115 207386227892666786822565173)
        ·
          refine ⟨19442458864937511264615485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 207386227892666786822565173 19442458864937511264615485)
          ·
            refine ⟨7290922074351566724230807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19442458864937511264615485 7290922074351566724230807)
            ·
              refine ⟨10936383111527350086346211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7290922074351566724230807 10936383111527350086346211)
              ·
                refine ⟨16404574667291025129519317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10936383111527350086346211 16404574667291025129519317)
                ·
                  refine ⟨384482218764633401473109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16404574667291025129519317 384482218764633401473109)
                  ·
                    rfl

theorem cell21_1684747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_1684747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684747 prefixEnd_1684747 := by exact prefixLift 1684747
  have htrace : WordTrace (prefixWord ++ tailWord_1684747) baseStart_1684747 baseEnd_1684747 := by
    simpa [prefixWord, tailWord_1684747, baseEnd_1684747] using wordTrace_append hprefix tailTrace_1684747
  have hstable : (prefixWord ++ tailWord_1684747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684747).length < 2 ^ (prefixWord ++ tailWord_1684747).sum := by decide
  have hdescent : baseEnd_1684747 < baseStart_1684747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684750 : List Nat := [4, 1, 1, 2, 1, 4, 3, 5]
def baseStart_1684750 : Nat := 118140960795 + 1684750 * 2 ^ 59
def prefixEnd_1684750 : Nat := 4983230072969 + 3 ^ 40 * 1684750 * 2
def baseEnd_1684750 : Nat := 128160967801835354307701

theorem tailTrace_1684750 : CollatzResearch.WordTrace tailWord_1684750 prefixEnd_1684750 128160967801835354307701 := by
  unfold tailWord_1684750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7680985080805744654695463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40965253764297304825042469 7680985080805744654695463)
  ·
    refine ⟨11521477621208616982043195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7680985080805744654695463 11521477621208616982043195)
    ·
      refine ⟨17282216431812925473064793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11521477621208616982043195 17282216431812925473064793)
      ·
        refine ⟨12961662323859694104798595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17282216431812925473064793 12961662323859694104798595)
        ·
          refine ⟨19442493485789541157197893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12961662323859694104798595 19442493485789541157197893)
          ·
            refine ⟨3645467528585538966974605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19442493485789541157197893 3645467528585538966974605)
            ·
              refine ⟨1367050323219577112615477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3645467528585538966974605 1367050323219577112615477)
              ·
                refine ⟨128160967801835354307701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1367050323219577112615477 128160967801835354307701)
                ·
                  rfl

theorem cell21_1684750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_1684750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684750 prefixEnd_1684750 := by exact prefixLift 1684750
  have htrace : WordTrace (prefixWord ++ tailWord_1684750) baseStart_1684750 baseEnd_1684750 := by
    simpa [prefixWord, tailWord_1684750, baseEnd_1684750] using wordTrace_append hprefix tailTrace_1684750
  have hstable : (prefixWord ++ tailWord_1684750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684750).length < 2 ^ (prefixWord ++ tailWord_1684750).sum := by decide
  have hdescent : baseEnd_1684750 < baseStart_1684750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684781 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 5]
def baseStart_1684781 : Nat := 118140960795 + 1684781 * 2 ^ 59
def prefixEnd_1684781 : Nat := 4983230072969 + 3 ^ 40 * 1684781 * 2
def baseEnd_1684781 : Nat := 384489978027856897906373

theorem tailTrace_1684781 : CollatzResearch.WordTrace tailWord_1684781 prefixEnd_1684781 384489978027856897906373 := by
  unfold tailWord_1684781
  simp only [CollatzResearch.WordTrace]
  refine ⟨61449011309333649531942197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40966007539555766354628131 61449011309333649531942197)
  ·
    refine ⟨5760844810250029643619581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61449011309333649531942197 5760844810250029643619581)
    ·
      refine ⟨2160316803843761116357343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5760844810250029643619581 2160316803843761116357343)
      ·
        refine ⟨3240475205765641674536015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2160316803843761116357343 3240475205765641674536015)
        ·
          refine ⟨4860712808648462511804023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240475205765641674536015 4860712808648462511804023)
          ·
            refine ⟨7291069212972693767706035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860712808648462511804023 7291069212972693767706035)
            ·
              refine ⟨10936603819459040651559053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291069212972693767706035 10936603819459040651559053)
              ·
                refine ⟨4101226432297140244334645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10936603819459040651559053 4101226432297140244334645)
                ·
                  refine ⟨384489978027856897906373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4101226432297140244334645 384489978027856897906373)
                  ·
                    rfl

theorem cell21_1684781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_1684781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684781 prefixEnd_1684781 := by exact prefixLift 1684781
  have htrace : WordTrace (prefixWord ++ tailWord_1684781) baseStart_1684781 baseEnd_1684781 := by
    simpa [prefixWord, tailWord_1684781, baseEnd_1684781] using wordTrace_append hprefix tailTrace_1684781
  have hstable : (prefixWord ++ tailWord_1684781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684781).length < 2 ^ (prefixWord ++ tailWord_1684781).sum := by decide
  have hdescent : baseEnd_1684781 < baseStart_1684781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684792 : List Nat := [2, 1, 2, 1, 3, 1, 1, 10]
def baseStart_1684792 : Nat := 118140960795 + 1684792 * 2 ^ 59
def prefixEnd_1684792 : Nat := 4983230072969 + 3 ^ 40 * 1684792 * 2
def baseEnd_1684792 : Nat := 128164162792574441074339

theorem tailTrace_1684792 : CollatzResearch.WordTrace tailWord_1684792 prefixEnd_1684792 128164162792574441074339 := by
  unfold tailWord_1684792
  simp only [CollatzResearch.WordTrace]
  refine ⟨30724706256146899205296315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40966275008195865607061753 30724706256146899205296315)
  ·
    refine ⟨46087059384220348807944473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30724706256146899205296315 46087059384220348807944473)
    ·
      refine ⟨34565294538165261605958355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46087059384220348807944473 34565294538165261605958355)
      ·
        refine ⟨51847941807247892408937533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34565294538165261605958355 51847941807247892408937533)
        ·
          refine ⟨19442978177717959653351575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51847941807247892408937533 19442978177717959653351575)
          ·
            refine ⟨29164467266576939480027363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19442978177717959653351575 29164467266576939480027363)
            ·
              refine ⟨43746700899865409220041045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29164467266576939480027363 43746700899865409220041045)
              ·
                refine ⟨128164162792574441074339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43746700899865409220041045 128164162792574441074339)
                ·
                  rfl

theorem cell21_1684792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_1684792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684792 prefixEnd_1684792 := by exact prefixLift 1684792
  have htrace : WordTrace (prefixWord ++ tailWord_1684792) baseStart_1684792 baseEnd_1684792 := by
    simpa [prefixWord, tailWord_1684792, baseEnd_1684792] using wordTrace_append hprefix tailTrace_1684792
  have hstable : (prefixWord ++ tailWord_1684792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684792).length < 2 ^ (prefixWord ++ tailWord_1684792).sum := by decide
  have hdescent : baseEnd_1684792 < baseStart_1684792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684809 : List Nat := [1, 2, 1, 1, 2, 3, 6, 5]
def baseStart_1684809 : Nat := 118140960795 + 1684809 * 2 ^ 59
def prefixEnd_1684809 : Nat := 4983230072969 + 3 ^ 40 * 1684809 * 2
def baseEnd_1684809 : Nat := 128165456003111690479883

theorem tailTrace_1684809 : CollatzResearch.WordTrace tailWord_1684809 prefixEnd_1684809 128165456003111690479883 := by
  unfold tailWord_1684809
  simp only [CollatzResearch.WordTrace]
  refine ⟨61450032553232210313961481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40966688368821473542640987 61450032553232210313961481)
  ·
    refine ⟨46087524414924157735471111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61450032553232210313961481 46087524414924157735471111)
    ·
      refine ⟨69131286622386236603206667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46087524414924157735471111 69131286622386236603206667)
      ·
        refine ⟨103696929933579354904810001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69131286622386236603206667 103696929933579354904810001)
        ·
          refine ⟨77772697450184516178607501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103696929933579354904810001 77772697450184516178607501)
          ·
            refine ⟨29164761543819193566977813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77772697450184516178607501 29164761543819193566977813)
            ·
              refine ⟨1367098197366524698452085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29164761543819193566977813 1367098197366524698452085)
              ·
                refine ⟨128165456003111690479883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1367098197366524698452085 128165456003111690479883)
                ·
                  rfl

theorem cell21_1684809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 5].length) (baseStart_1684809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684809 prefixEnd_1684809 := by exact prefixLift 1684809
  have htrace : WordTrace (prefixWord ++ tailWord_1684809) baseStart_1684809 baseEnd_1684809 := by
    simpa [prefixWord, tailWord_1684809, baseEnd_1684809] using wordTrace_append hprefix tailTrace_1684809
  have hstable : (prefixWord ++ tailWord_1684809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684809).length < 2 ^ (prefixWord ++ tailWord_1684809).sum := by decide
  have hdescent : baseEnd_1684809 < baseStart_1684809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684846 : List Nat := [4, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_1684846 : Nat := 118140960795 + 1684846 * 2 ^ 59
def prefixEnd_1684846 : Nat := 4983230072969 + 3 ^ 40 * 1684846 * 2
def baseEnd_1684846 : Nat := 384504811913431229322907

theorem tailTrace_1684846 : CollatzResearch.WordTrace tailWord_1684846 prefixEnd_1684846 384504811913431229322907 := by
  unfold tailWord_1684846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7681422756762270704132299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40967588036065443755372261 7681422756762270704132299)
  ·
    refine ⟨11522134135143406056198449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7681422756762270704132299 11522134135143406056198449)
    ·
      refine ⟨8641600601357554542148837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11522134135143406056198449 8641600601357554542148837)
      ·
        refine ⟨1620300112754541476652907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8641600601357554542148837 1620300112754541476652907)
        ·
          refine ⟨2430450169131812214979361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1620300112754541476652907 2430450169131812214979361)
          ·
            refine ⟨1822837626848859161234521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2430450169131812214979361 1822837626848859161234521)
            ·
              refine ⟨1367128220136644370925891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1822837626848859161234521 1367128220136644370925891)
              ·
                refine ⟨2050692330204966556388837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367128220136644370925891 2050692330204966556388837)
                ·
                  refine ⟨384504811913431229322907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050692330204966556388837 384504811913431229322907)
                  ·
                    rfl

theorem cell21_1684846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_1684846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684846 prefixEnd_1684846 := by exact prefixLift 1684846
  have htrace : WordTrace (prefixWord ++ tailWord_1684846) baseStart_1684846 baseEnd_1684846 := by
    simpa [prefixWord, tailWord_1684846, baseEnd_1684846] using wordTrace_append hprefix tailTrace_1684846
  have hstable : (prefixWord ++ tailWord_1684846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684846).length < 2 ^ (prefixWord ++ tailWord_1684846).sum := by decide
  have hdescent : baseEnd_1684846 < baseStart_1684846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684888 : List Nat := [2, 1, 2, 5, 2, 1, 2, 2, 4]
def baseStart_1684888 : Nat := 118140960795 + 1684888 * 2 ^ 59
def prefixEnd_1684888 : Nat := 4983230072969 + 3 ^ 40 * 1684888 * 2
def baseEnd_1684888 : Nat := 384514396885648489622821

theorem tailTrace_1684888 : CollatzResearch.WordTrace tailWord_1684888 prefixEnd_1684888 384514396885648489622821 := by
  unfold tailWord_1684888
  simp only [CollatzResearch.WordTrace]
  refine ⟨30726456959973003403043659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40968609279964004537391545 30726456959973003403043659)
  ·
    refine ⟨46089685439959505104565489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30726456959973003403043659 46089685439959505104565489)
    ·
      refine ⟨34567264079969628828424117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46089685439959505104565489 34567264079969628828424117)
      ·
        refine ⟨3240681007497152702664761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34567264079969628828424117 3240681007497152702664761)
        ·
          refine ⟨2430510755622864526998571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3240681007497152702664761 2430510755622864526998571)
          ·
            refine ⟨3645766133434296790497857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2430510755622864526998571 3645766133434296790497857)
            ·
              refine ⟨2734324600075722592873393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3645766133434296790497857 2734324600075722592873393)
              ·
                refine ⟨2050743450056791944655045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2734324600075722592873393 2050743450056791944655045)
                ·
                  refine ⟨384514396885648489622821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050743450056791944655045 384514396885648489622821)
                  ·
                    rfl

theorem cell21_1684888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_1684888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684888 prefixEnd_1684888 := by exact prefixLift 1684888
  have htrace : WordTrace (prefixWord ++ tailWord_1684888) baseStart_1684888 baseEnd_1684888 := by
    simpa [prefixWord, tailWord_1684888, baseEnd_1684888] using wordTrace_append hprefix tailTrace_1684888
  have hstable : (prefixWord ++ tailWord_1684888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684888).length < 2 ^ (prefixWord ++ tailWord_1684888).sum := by decide
  have hdescent : baseEnd_1684888 < baseStart_1684888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684899 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 5]
def baseStart_1684899 : Nat := 118140960795 + 1684899 * 2 ^ 59
def prefixEnd_1684899 : Nat := 4983230072969 + 3 ^ 40 * 1684899 * 2
def baseEnd_1684899 : Nat := 384516907235514914939465

theorem tailTrace_1684899 : CollatzResearch.WordTrace tailWord_1684899 prefixEnd_1684899 384516907235514914939465 := by
  unfold tailWord_1684899
  simp only [CollatzResearch.WordTrace]
  refine ⟨61453315122906155684737751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40968876748604103789825167 61453315122906155684737751)
  ·
    refine ⟨92179972684359233527106627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61453315122906155684737751 92179972684359233527106627)
    ·
      refine ⟨138269959026538850290659941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92179972684359233527106627 138269959026538850290659941)
      ·
        refine ⟨25925617317476034429498739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138269959026538850290659941 25925617317476034429498739)
        ·
          refine ⟨38888425976214051644248109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25925617317476034429498739 38888425976214051644248109)
          ·
            refine ⟨14583159741080269366593041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38888425976214051644248109 14583159741080269366593041)
            ·
              refine ⟨10937369805810202024944781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14583159741080269366593041 10937369805810202024944781)
              ·
                refine ⟨4101513677178825759354293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10937369805810202024944781 4101513677178825759354293)
                ·
                  refine ⟨384516907235514914939465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4101513677178825759354293 384516907235514914939465)
                  ·
                    rfl

theorem cell21_1684899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 5].length) (baseStart_1684899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684899 prefixEnd_1684899 := by exact prefixLift 1684899
  have htrace : WordTrace (prefixWord ++ tailWord_1684899) baseStart_1684899 baseEnd_1684899 := by
    simpa [prefixWord, tailWord_1684899, baseEnd_1684899] using wordTrace_append hprefix tailTrace_1684899
  have hstable : (prefixWord ++ tailWord_1684899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684899).length < 2 ^ (prefixWord ++ tailWord_1684899).sum := by decide
  have hdescent : baseEnd_1684899 < baseStart_1684899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684950 : List Nat := [5, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1684950 : Nat := 118140960795 + 1684950 * 2 ^ 59
def prefixEnd_1684950 : Nat := 4983230072969 + 3 ^ 40 * 1684950 * 2
def baseEnd_1684950 : Nat := 384528546130350159589361

theorem tailTrace_1684950 : CollatzResearch.WordTrace tailWord_1684950 prefixEnd_1684950 384528546130350159589361 := by
  unfold tailWord_1684950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840948452857586962177769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40970116830480927596562869 3840948452857586962177769)
  ·
    refine ⟨2880711339643190221633327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3840948452857586962177769 2880711339643190221633327)
    ·
      refine ⟨4321067009464785332449991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2880711339643190221633327 4321067009464785332449991)
      ·
        refine ⟨6481600514197177998674987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4321067009464785332449991 6481600514197177998674987)
        ·
          refine ⟨9722400771295766998012481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6481600514197177998674987 9722400771295766998012481)
          ·
            refine ⟨7291800578471825248509361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9722400771295766998012481 7291800578471825248509361)
            ·
              refine ⟨5468850433853868936382021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7291800578471825248509361 5468850433853868936382021)
              ·
                refine ⟨1025409456347600425571629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5468850433853868936382021 1025409456347600425571629)
                ·
                  refine ⟨384528546130350159589361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025409456347600425571629 384528546130350159589361)
                  ·
                    rfl

theorem cell21_1684950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1684950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684950 prefixEnd_1684950 := by exact prefixLift 1684950
  have htrace : WordTrace (prefixWord ++ tailWord_1684950) baseStart_1684950 baseEnd_1684950 := by
    simpa [prefixWord, tailWord_1684950, baseEnd_1684950] using wordTrace_append hprefix tailTrace_1684950
  have hstable : (prefixWord ++ tailWord_1684950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684950).length < 2 ^ (prefixWord ++ tailWord_1684950).sum := by decide
  have hdescent : baseEnd_1684950 < baseStart_1684950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684975 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 5]
def baseStart_1684975 : Nat := 118140960795 + 1684975 * 2 ^ 59
def prefixEnd_1684975 : Nat := 4983230072969 + 3 ^ 40 * 1684975 * 2
def baseEnd_1684975 : Nat := 384534251470955671672643

theorem tailTrace_1684975 : CollatzResearch.WordTrace tailWord_1684975 prefixEnd_1684975 384534251470955671672643 := by
  unfold tailWord_1684975
  simp only [CollatzResearch.WordTrace]
  refine ⟨61456087070630820664504379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40970724713753880443002919 61456087070630820664504379)
  ·
    refine ⟨92184130605946230996756569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61456087070630820664504379 92184130605946230996756569)
    ·
      refine ⟨69138097954459673247567427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92184130605946230996756569 69138097954459673247567427)
      ·
        refine ⟨103707146931689509871351141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69138097954459673247567427 103707146931689509871351141)
        ·
          refine ⟨19445090049691783100878339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103707146931689509871351141 19445090049691783100878339)
          ·
            refine ⟨29167635074537674651317509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19445090049691783100878339 29167635074537674651317509)
            ·
              refine ⟨5468931576475813997122033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29167635074537674651317509 5468931576475813997122033)
              ·
                refine ⟨4101698682356860497841525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5468931576475813997122033 4101698682356860497841525)
                ·
                  refine ⟨384534251470955671672643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4101698682356860497841525 384534251470955671672643)
                  ·
                    rfl

theorem cell21_1684975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 5].length) (baseStart_1684975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684975 prefixEnd_1684975 := by exact prefixLift 1684975
  have htrace : WordTrace (prefixWord ++ tailWord_1684975) baseStart_1684975 baseEnd_1684975 := by
    simpa [prefixWord, tailWord_1684975, baseEnd_1684975] using wordTrace_append hprefix tailTrace_1684975
  have hstable : (prefixWord ++ tailWord_1684975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684975).length < 2 ^ (prefixWord ++ tailWord_1684975).sum := by decide
  have hdescent : baseEnd_1684975 < baseStart_1684975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684978 : List Nat := [3, 2, 1, 4, 1, 1, 4, 5]
def baseStart_1684978 : Nat := 118140960795 + 1684978 * 2 ^ 59
def prefixEnd_1684978 : Nat := 4983230072969 + 3 ^ 40 * 1684978 * 2
def baseEnd_1684978 : Nat := 128178312037276111040879

theorem tailTrace_1684978 : CollatzResearch.WordTrace tailWord_1684978 prefixEnd_1684978 128178312037276111040879 := by
  unfold tailWord_1684978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15364049122404988044215897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40970797659746634784575725 15364049122404988044215897)
  ·
    refine ⟨11523036841803741033161923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15364049122404988044215897 11523036841803741033161923)
    ·
      refine ⟨17284555262705611549742885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11523036841803741033161923 17284555262705611549742885)
      ·
        refine ⟨3240854111757302165576791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17284555262705611549742885 3240854111757302165576791)
        ·
          refine ⟨4861281167635953248365187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240854111757302165576791 4861281167635953248365187)
          ·
            refine ⟨7291921751453929872547781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4861281167635953248365187 7291921751453929872547781)
            ·
              refine ⟨1367235328397611851102709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7291921751453929872547781 1367235328397611851102709)
              ·
                refine ⟨128178312037276111040879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1367235328397611851102709 128178312037276111040879)
                ·
                  rfl

theorem cell21_1684978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_1684978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1684978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1684978 prefixEnd_1684978 := by exact prefixLift 1684978
  have htrace : WordTrace (prefixWord ++ tailWord_1684978) baseStart_1684978 baseEnd_1684978 := by
    simpa [prefixWord, tailWord_1684978, baseEnd_1684978] using wordTrace_append hprefix tailTrace_1684978
  have hstable : (prefixWord ++ tailWord_1684978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684978).length < 2 ^ (prefixWord ++ tailWord_1684978).sum := by decide
  have hdescent : baseEnd_1684978 < baseStart_1684978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685009 : List Nat := [1, 2, 2, 1, 1, 2, 7, 2, 3]
def baseStart_1685009 : Nat := 118140960795 + 1685009 * 2 ^ 59
def prefixEnd_1685009 : Nat := 4983230072969 + 3 ^ 40 * 1685009 * 2
def baseEnd_1685009 : Nat := 384542010734179168105907

theorem tailTrace_1685009 : CollatzResearch.WordTrace tailWord_1685009 prefixEnd_1685009 384542010734179168105907 := by
  unfold tailWord_1685009
  simp only [CollatzResearch.WordTrace]
  refine ⟨61457327152507644471242081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40971551435005096314161387 61457327152507644471242081)
  ·
    refine ⟨46092995364380733353431561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61457327152507644471242081 46092995364380733353431561)
    ·
      refine ⟨34569746523285550015073671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46092995364380733353431561 34569746523285550015073671)
      ·
        refine ⟨51854619784928325022610507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34569746523285550015073671 51854619784928325022610507)
        ·
          refine ⟨77781929677392487533915761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51854619784928325022610507 77781929677392487533915761)
          ·
            refine ⟨58336447258044365650436821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77781929677392487533915761 58336447258044365650436821)
            ·
              refine ⟨1367260482610414819932113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58336447258044365650436821 1367260482610414819932113)
              ·
                refine ⟨1025445361957811114949085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1367260482610414819932113 1025445361957811114949085)
                ·
                  refine ⟨384542010734179168105907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025445361957811114949085 384542010734179168105907)
                  ·
                    rfl

theorem cell21_1685009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 3].length) (baseStart_1685009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685009 prefixEnd_1685009 := by exact prefixLift 1685009
  have htrace : WordTrace (prefixWord ++ tailWord_1685009) baseStart_1685009 baseEnd_1685009 := by
    simpa [prefixWord, tailWord_1685009, baseEnd_1685009] using wordTrace_append hprefix tailTrace_1685009
  have hstable : (prefixWord ++ tailWord_1685009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685009).length < 2 ^ (prefixWord ++ tailWord_1685009).sum := by decide
  have hdescent : baseEnd_1685009 < baseStart_1685009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685023 : List Nat := [1, 1, 2, 4, 1, 1, 6, 1, 4]
def baseStart_1685023 : Nat := 118140960795 + 1685023 * 2 ^ 59
def prefixEnd_1685023 : Nat := 4983230072969 + 3 ^ 40 * 1685023 * 2
def baseEnd_1685023 : Nat := 384545205724918254872545

theorem tailTrace_1685023 : CollatzResearch.WordTrace tailWord_1685023 prefixEnd_1685023 384545205724918254872545 := by
  unfold tailWord_1685023
  simp only [CollatzResearch.WordTrace]
  refine ⟨61457837774456924862251723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40971891849637949908167815 61457837774456924862251723)
  ·
    refine ⟨92186756661685387293377585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61457837774456924862251723 92186756661685387293377585)
    ·
      refine ⟨69140067496264040470033189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92186756661685387293377585 69140067496264040470033189)
      ·
        refine ⟨12963762655549507588131223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69140067496264040470033189 12963762655549507588131223)
        ·
          refine ⟨19445643983324261382196835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12963762655549507588131223 19445643983324261382196835)
          ·
            refine ⟨29168465974986392073295253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19445643983324261382196835 29168465974986392073295253)
            ·
              refine ⟨1367271842577487128435715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29168465974986392073295253 1367271842577487128435715)
              ·
                refine ⟨2050907763866230692653573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367271842577487128435715 2050907763866230692653573)
                ·
                  refine ⟨384545205724918254872545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050907763866230692653573 384545205724918254872545)
                  ·
                    rfl

theorem cell21_1685023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 4].length) (baseStart_1685023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685023 prefixEnd_1685023 := by exact prefixLift 1685023
  have htrace : WordTrace (prefixWord ++ tailWord_1685023) baseStart_1685023 baseEnd_1685023 := by
    simpa [prefixWord, tailWord_1685023, baseEnd_1685023] using wordTrace_append hprefix tailTrace_1685023
  have hstable : (prefixWord ++ tailWord_1685023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685023).length < 2 ^ (prefixWord ++ tailWord_1685023).sum := by decide
  have hdescent : baseEnd_1685023 < baseStart_1685023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685065 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 6]
def baseStart_1685065 : Nat := 118140960795 + 1685065 * 2 ^ 59
def prefixEnd_1685065 : Nat := 4983230072969 + 3 ^ 40 * 1685065 * 2
def baseEnd_1685065 : Nat := 384554790697135515172459

theorem tailTrace_1685065 : CollatzResearch.WordTrace tailWord_1685065 prefixEnd_1685065 384554790697135515172459 := by
  unfold tailWord_1685065
  simp only [CollatzResearch.WordTrace]
  refine ⟨61459369640304766035280649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40972913093536510690187099 61459369640304766035280649)
  ·
    refine ⟨46094527230228574526460487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61459369640304766035280649 46094527230228574526460487)
    ·
      refine ⟨69141790845342861789690731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46094527230228574526460487 69141790845342861789690731)
      ·
        refine ⟨103712686268014292684536097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69141790845342861789690731 103712686268014292684536097)
        ·
          refine ⟨77784514701010719513402073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103712686268014292684536097 77784514701010719513402073)
          ·
            refine ⟨58338386025758039635051555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77784514701010719513402073 58338386025758039635051555)
            ·
              refine ⟨87507579038637059452577333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58338386025758039635051555 87507579038637059452577333)
              ·
                refine ⟨8203835534872224323679125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87507579038637059452577333 8203835534872224323679125)
                ·
                  refine ⟨384554790697135515172459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8203835534872224323679125 384554790697135515172459)
                  ·
                    rfl

theorem cell21_1685065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_1685065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685065 prefixEnd_1685065 := by exact prefixLift 1685065
  have htrace : WordTrace (prefixWord ++ tailWord_1685065) baseStart_1685065 baseEnd_1685065 := by
    simpa [prefixWord, tailWord_1685065, baseEnd_1685065] using wordTrace_append hprefix tailTrace_1685065
  have hstable : (prefixWord ++ tailWord_1685065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685065).length < 2 ^ (prefixWord ++ tailWord_1685065).sum := by decide
  have hdescent : baseEnd_1685065 < baseStart_1685065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685102 : List Nat := [4, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_1685102 : Nat := 118140960795 + 1685102 * 2 ^ 59
def prefixEnd_1685102 : Nat := 4983230072969 + 3 ^ 40 * 1685102 * 2
def baseEnd_1685102 : Nat := 384563234601231673055717

theorem tailTrace_1685102 : CollatzResearch.WordTrace tailWord_1685102 prefixEnd_1685102 384563234601231673055717 := by
  unfold tailWord_1685102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682589892646340169297195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40973812760780480902918373 7682589892646340169297195)
  ·
    refine ⟨11523884838969510253945793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7682589892646340169297195 11523884838969510253945793)
    ·
      refine ⟨8642913629227132690459345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11523884838969510253945793 8642913629227132690459345)
      ·
        refine ⟨6482185221920349517844509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8642913629227132690459345 6482185221920349517844509)
        ·
          refine ⟨2430819458220131069191691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6482185221920349517844509 2430819458220131069191691)
          ·
            refine ⟨3646229187330196603787537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2430819458220131069191691 3646229187330196603787537)
            ·
              refine ⟨2734671890497647452840653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3646229187330196603787537 2734671890497647452840653)
              ·
                refine ⟨1025501958936617794815245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2734671890497647452840653 1025501958936617794815245)
                ·
                  refine ⟨384563234601231673055717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025501958936617794815245 384563234601231673055717)
                  ·
                    rfl

theorem cell21_1685102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_1685102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685102 prefixEnd_1685102 := by exact prefixLift 1685102
  have htrace : WordTrace (prefixWord ++ tailWord_1685102) baseStart_1685102 baseEnd_1685102 := by
    simpa [prefixWord, tailWord_1685102, baseEnd_1685102] using wordTrace_append hprefix tailTrace_1685102
  have hstable : (prefixWord ++ tailWord_1685102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685102).length < 2 ^ (prefixWord ++ tailWord_1685102).sum := by decide
  have hdescent : baseEnd_1685102 < baseStart_1685102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685127 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 5]
def baseStart_1685127 : Nat := 118140960795 + 1685127 * 2 ^ 59
def prefixEnd_1685127 : Nat := 4983230072969 + 3 ^ 40 * 1685127 * 2
def baseEnd_1685127 : Nat := 384568939941837185138999

theorem tailTrace_1685127 : CollatzResearch.WordTrace tailWord_1685127 prefixEnd_1685127 384568939941837185138999 := by
  unfold tailWord_1685127
  simp only [CollatzResearch.WordTrace]
  refine ⟨61461630966080150624037635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40974420644053433749358423 61461630966080150624037635)
  ·
    refine ⟨92192446449120225936056453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61461630966080150624037635 92192446449120225936056453)
    ·
      refine ⟨17286083709210042363010585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92192446449120225936056453 17286083709210042363010585)
      ·
        refine ⟨12964562781907531772257939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17286083709210042363010585 12964562781907531772257939)
        ·
          refine ⟨19446844172861297658386909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12964562781907531772257939 19446844172861297658386909)
          ·
            refine ⟨7292566564822986621895091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19446844172861297658386909 7292566564822986621895091)
            ·
              refine ⟨10938849847234479932842637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7292566564822986621895091 10938849847234479932842637)
              ·
                refine ⟨4102068692712929974815989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10938849847234479932842637 4102068692712929974815989)
                ·
                  refine ⟨384568939941837185138999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4102068692712929974815989 384568939941837185138999)
                  ·
                    rfl

theorem cell21_1685127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 5].length) (baseStart_1685127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685127 prefixEnd_1685127 := by exact prefixLift 1685127
  have htrace : WordTrace (prefixWord ++ tailWord_1685127) baseStart_1685127 baseEnd_1685127 := by
    simpa [prefixWord, tailWord_1685127, baseEnd_1685127] using wordTrace_append hprefix tailTrace_1685127
  have hstable : (prefixWord ++ tailWord_1685127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685127).length < 2 ^ (prefixWord ++ tailWord_1685127).sum := by decide
  have hdescent : baseEnd_1685127 < baseStart_1685127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685220 : List Nat := [2, 3, 1, 1, 1, 3, 2, 5, 3]
def baseStart_1685220 : Nat := 118140960795 + 1685220 * 2 ^ 59
def prefixEnd_1685220 : Nat := 4983230072969 + 3 ^ 40 * 1685220 * 2
def baseEnd_1685220 : Nat := 384590163808889690088809

theorem tailTrace_1685220 : CollatzResearch.WordTrace tailWord_1685220 prefixEnd_1685220 384590163808889690088809 := by
  unfold tailWord_1685220
  simp only [CollatzResearch.WordTrace]
  refine ⟨30732511477371613753586557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40976681969828818338115409 30732511477371613753586557)
  ·
    refine ⟨11524691804014355157594959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30732511477371613753586557 11524691804014355157594959)
    ·
      refine ⟨17287037706021532736392439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11524691804014355157594959 17287037706021532736392439)
      ·
        refine ⟨25930556559032299104588659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17287037706021532736392439 25930556559032299104588659)
        ·
          refine ⟨38895834838548448656882989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25930556559032299104588659 38895834838548448656882989)
          ·
            refine ⟨14585938064455668246331121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38895834838548448656882989 14585938064455668246331121)
            ·
              refine ⟨10939453548341751184748341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14585938064455668246331121 10939453548341751184748341)
              ·
                refine ⟨1025573770157039173570157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10939453548341751184748341 1025573770157039173570157)
                ·
                  refine ⟨384590163808889690088809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025573770157039173570157 384590163808889690088809)
                  ·
                    rfl

theorem cell21_1685220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_1685220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685220 prefixEnd_1685220 := by exact prefixLift 1685220
  have htrace : WordTrace (prefixWord ++ tailWord_1685220) baseStart_1685220 baseEnd_1685220 := by
    simpa [prefixWord, tailWord_1685220, baseEnd_1685220] using wordTrace_append hprefix tailTrace_1685220
  have hstable : (prefixWord ++ tailWord_1685220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685220).length < 2 ^ (prefixWord ++ tailWord_1685220).sum := by decide
  have hdescent : baseEnd_1685220 < baseStart_1685220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685400 : List Nat := [2, 1, 2, 6, 10]
def baseStart_1685400 : Nat := 118140960795 + 1685400 * 2 ^ 59
def prefixEnd_1685400 : Nat := 4983230072969 + 3 ^ 40 * 1685400 * 2
def baseEnd_1685400 : Nat := 4748533855077152803561

theorem tailTrace_1685400 : CollatzResearch.WordTrace tailWord_1685400 prefixEnd_1685400 4748533855077152803561 := by
  unfold tailWord_1685400
  simp only [CollatzResearch.WordTrace]
  refine ⟨30735794047045559124362827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40981058729394078832483769 30735794047045559124362827)
  ·
    refine ⟨46103691070568338686544241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30735794047045559124362827 46103691070568338686544241)
    ·
      refine ⟨34577768302926254014908181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46103691070568338686544241 34577768302926254014908181)
      ·
        refine ⟨1620832889199668156948821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34577768302926254014908181 1620832889199668156948821)
        ·
          refine ⟨4748533855077152803561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1620832889199668156948821 4748533855077152803561)
          ·
            rfl

theorem cell21_1685400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 10].length) (baseStart_1685400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685400 prefixEnd_1685400 := by exact prefixLift 1685400
  have htrace : WordTrace (prefixWord ++ tailWord_1685400) baseStart_1685400 baseEnd_1685400 := by
    simpa [prefixWord, tailWord_1685400, baseEnd_1685400] using wordTrace_append hprefix tailTrace_1685400
  have hstable : (prefixWord ++ tailWord_1685400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685400).length < 2 ^ (prefixWord ++ tailWord_1685400).sum := by decide
  have hdescent : baseEnd_1685400 < baseStart_1685400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685448 : List Nat := [2, 1, 3, 1, 4, 1, 1, 5, 3]
def baseStart_1685448 : Nat := 118140960795 + 1685448 * 2 ^ 59
def prefixEnd_1685448 : Nat := 4983230072969 + 3 ^ 40 * 1685448 * 2
def baseEnd_1685448 : Nat := 384642196515211960288343

theorem tailTrace_1685448 : CollatzResearch.WordTrace tailWord_1685448 prefixEnd_1685448 384642196515211960288343 := by
  unfold tailWord_1685448
  simp only [CollatzResearch.WordTrace]
  refine ⟨30736669398958611223236499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40982225865278148297648665 30736669398958611223236499)
  ·
    refine ⟨46105004098437916834854749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30736669398958611223236499 46105004098437916834854749)
    ·
      refine ⟨17289376536914218813070531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46105004098437916834854749 17289376536914218813070531)
      ·
        refine ⟨25934064805371328219605797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17289376536914218813070531 25934064805371328219605797)
        ·
          refine ⟨4862637151007124041176087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25934064805371328219605797 4862637151007124041176087)
          ·
            refine ⟨7293955726510686061764131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4862637151007124041176087 7293955726510686061764131)
            ·
              refine ⟨10940933589766029092646197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7293955726510686061764131 10940933589766029092646197)
              ·
                refine ⟨1025712524040565227435581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10940933589766029092646197 1025712524040565227435581)
                ·
                  refine ⟨384642196515211960288343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025712524040565227435581 384642196515211960288343)
                  ·
                    rfl

theorem cell21_1685448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 3].length) (baseStart_1685448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685448 prefixEnd_1685448 := by exact prefixLift 1685448
  have htrace : WordTrace (prefixWord ++ tailWord_1685448) baseStart_1685448 baseEnd_1685448 := by
    simpa [prefixWord, tailWord_1685448, baseEnd_1685448] using wordTrace_append hprefix tailTrace_1685448
  have hstable : (prefixWord ++ tailWord_1685448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685448).length < 2 ^ (prefixWord ++ tailWord_1685448).sum := by decide
  have hdescent : baseEnd_1685448 < baseStart_1685448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685538 : List Nat := [3, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1685538 : Nat := 118140960795 + 1685538 * 2 ^ 59
def prefixEnd_1685538 : Nat := 4983230072969 + 3 ^ 40 * 1685538 * 2
def baseEnd_1685538 : Nat := 384662735741391803788159

theorem tailTrace_1685538 : CollatzResearch.WordTrace tailWord_1685538 prefixEnd_1685538 384662735741391803788159 := by
  unfold tailWord_1685538
  simp only [CollatzResearch.WordTrace]
  refine ⟨15369155341897791954312317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40984414245060778544832845 15369155341897791954312317)
  ·
    refine ⟨5763433253211671982867119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15369155341897791954312317 5763433253211671982867119)
    ·
      refine ⟨8645149879817507974300679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5763433253211671982867119 8645149879817507974300679)
      ·
        refine ⟨12967724819726261961451019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8645149879817507974300679 12967724819726261961451019)
        ·
          refine ⟨19451587229589392942176529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12967724819726261961451019 19451587229589392942176529)
          ·
            refine ⟨14588690422192044706632397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19451587229589392942176529 14588690422192044706632397)
            ·
              refine ⟨5470758908322016764987149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14588690422192044706632397 5470758908322016764987149)
              ·
                refine ⟨2051534590620756286870181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5470758908322016764987149 2051534590620756286870181)
                ·
                  refine ⟨384662735741391803788159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2051534590620756286870181 384662735741391803788159)
                  ·
                    rfl

theorem cell21_1685538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1685538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685538 prefixEnd_1685538 := by exact prefixLift 1685538
  have htrace : WordTrace (prefixWord ++ tailWord_1685538) baseStart_1685538 baseEnd_1685538 := by
    simpa [prefixWord, tailWord_1685538, baseEnd_1685538] using wordTrace_append hprefix tailTrace_1685538
  have hstable : (prefixWord ++ tailWord_1685538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685538).length < 2 ^ (prefixWord ++ tailWord_1685538).sum := by decide
  have hdescent : baseEnd_1685538 < baseStart_1685538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685583 : List Nat := [1, 1, 2, 1, 1, 2, 2, 8, 3]
def baseStart_1685583 : Nat := 118140960795 + 1685583 * 2 ^ 59
def prefixEnd_1685583 : Nat := 4983230072969 + 3 ^ 40 * 1685583 * 2
def baseEnd_1685583 : Nat := 384673005354481725538067

theorem tailTrace_1685583 : CollatzResearch.WordTrace tailWord_1685583 prefixEnd_1685583 384673005354481725538067 := by
  unfold tailWord_1685583
  simp only [CollatzResearch.WordTrace]
  refine ⟨61478262652428140502637403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40985508434952093668424935 61478262652428140502637403)
  ·
    refine ⟨92217393978642210753956105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61478262652428140502637403 92217393978642210753956105)
    ·
      refine ⟨69163045483981658065467079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92217393978642210753956105 69163045483981658065467079)
      ·
        refine ⟨103744568225972487098200619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69163045483981658065467079 103744568225972487098200619)
        ·
          refine ⟨155616852338958730647300929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103744568225972487098200619 155616852338958730647300929)
          ·
            refine ⟨116712639254219047985475697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155616852338958730647300929 116712639254219047985475697)
            ·
              refine ⟨87534479440664285989106773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116712639254219047985475697 87534479440664285989106773)
              ·
                refine ⟨1025794680945284601434845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 87534479440664285989106773 1025794680945284601434845)
                ·
                  refine ⟨384673005354481725538067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025794680945284601434845 384673005354481725538067)
                  ·
                    rfl

theorem cell21_1685583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 3].length) (baseStart_1685583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685583 prefixEnd_1685583 := by exact prefixLift 1685583
  have htrace : WordTrace (prefixWord ++ tailWord_1685583) baseStart_1685583 baseEnd_1685583 := by
    simpa [prefixWord, tailWord_1685583, baseEnd_1685583] using wordTrace_append hprefix tailTrace_1685583
  have hstable : (prefixWord ++ tailWord_1685583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685583).length < 2 ^ (prefixWord ++ tailWord_1685583).sum := by decide
  have hdescent : baseEnd_1685583 < baseStart_1685583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685586 : List Nat := [3, 2, 2, 1, 5, 1, 1, 6]
def baseStart_1685586 : Nat := 118140960795 + 1685586 * 2 ^ 59
def prefixEnd_1685586 : Nat := 4983230072969 + 3 ^ 40 * 1685586 * 2
def baseEnd_1685586 : Nat := 128224563331784795662687

theorem tailTrace_1685586 : CollatzResearch.WordTrace tailWord_1685586 prefixEnd_1685586 128224563331784795662687 := by
  unfold tailWord_1685586
  simp only [CollatzResearch.WordTrace]
  refine ⟨15369593017854318003749153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40985581380944848009997741 15369593017854318003749153)
  ·
    refine ⟨11527194763390738502811865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15369593017854318003749153 11527194763390738502811865)
    ·
      refine ⟨8645396072543053877108899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11527194763390738502811865 8645396072543053877108899)
      ·
        refine ⟨12968094108814580815663349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8645396072543053877108899 12968094108814580815663349)
        ·
          refine ⟨1215758822701366951468439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12968094108814580815663349 1215758822701366951468439)
          ·
            refine ⟨1823638234052050427202659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215758822701366951468439 1823638234052050427202659)
            ·
              refine ⟨2735457351078075640803989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1823638234052050427202659 2735457351078075640803989)
              ·
                refine ⟨128224563331784795662687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2735457351078075640803989 128224563331784795662687)
                ·
                  rfl

theorem cell21_1685586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_1685586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685586 prefixEnd_1685586 := by exact prefixLift 1685586
  have htrace : WordTrace (prefixWord ++ tailWord_1685586) baseStart_1685586 baseEnd_1685586 := by
    simpa [prefixWord, tailWord_1685586, baseEnd_1685586] using wordTrace_append hprefix tailTrace_1685586
  have hstable : (prefixWord ++ tailWord_1685586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685586).length < 2 ^ (prefixWord ++ tailWord_1685586).sum := by decide
  have hdescent : baseEnd_1685586 < baseStart_1685586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685654 : List Nat := [5, 3, 2, 1, 2, 1, 2, 5]
def baseStart_1685654 : Nat := 118140960795 + 1685654 * 2 ^ 59
def prefixEnd_1685654 : Nat := 4983230072969 + 3 ^ 40 * 1685654 * 2
def baseEnd_1685654 : Nat := 128229736173933793284863

theorem tailTrace_1685654 : CollatzResearch.WordTrace tailWord_1685654 prefixEnd_1685654 128229736173933793284863 := by
  unfold tailWord_1685654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3842553264698182476779501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40987234823447279752314677 3842553264698182476779501)
  ·
    refine ⟨1440957474261818428792313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3842553264698182476779501 1440957474261818428792313)
    ·
      refine ⟨1080718105696363821594235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1440957474261818428792313 1080718105696363821594235)
      ·
        refine ⟨1621077158544545732391353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080718105696363821594235 1621077158544545732391353)
        ·
          refine ⟨1215807868908409299293515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1621077158544545732391353 1215807868908409299293515)
          ·
            refine ⟨1823711803362613948940273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215807868908409299293515 1823711803362613948940273)
            ·
              refine ⟨1367783852521960461705205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1823711803362613948940273 1367783852521960461705205)
              ·
                refine ⟨128229736173933793284863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1367783852521960461705205 128229736173933793284863)
                ·
                  rfl

theorem cell21_1685654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_1685654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685654 prefixEnd_1685654 := by exact prefixLift 1685654
  have htrace : WordTrace (prefixWord ++ tailWord_1685654) baseStart_1685654 baseEnd_1685654 := by
    simpa [prefixWord, tailWord_1685654, baseEnd_1685654] using wordTrace_append hprefix tailTrace_1685654
  have hstable : (prefixWord ++ tailWord_1685654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685654).length < 2 ^ (prefixWord ++ tailWord_1685654).sum := by decide
  have hdescent : baseEnd_1685654 < baseStart_1685654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685687 : List Nat := [1, 1, 3, 1, 4, 2, 9]
def baseStart_1685687 : Nat := 118140960795 + 1685687 * 2 ^ 59
def prefixEnd_1685687 : Nat := 4983230072969 + 3 ^ 40 * 1685687 * 2
def baseEnd_1685687 : Nat := 42744082174600072867169

theorem tailTrace_1685687 : CollatzResearch.WordTrace tailWord_1685687 prefixEnd_1685687 42744082174600072867169 := by
  unfold tailWord_1685687
  simp only [CollatzResearch.WordTrace]
  refine ⟨61482055844051366264423315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40988037229367577509615543 61482055844051366264423315)
  ·
    refine ⟨92223083766077049396634973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61482055844051366264423315 92223083766077049396634973)
    ·
      refine ⟨34583656412278893523738115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92223083766077049396634973 34583656412278893523738115)
      ·
        refine ⟨51875484618418340285607173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34583656412278893523738115 51875484618418340285607173)
        ·
          refine ⟨9726653365953438803551345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51875484618418340285607173 9726653365953438803551345)
          ·
            refine ⟨7294990024465079102663509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9726653365953438803551345 7294990024465079102663509)
            ·
              refine ⟨42744082174600072867169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7294990024465079102663509 42744082174600072867169)
              ·
                rfl

theorem cell21_1685687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 9].length) (baseStart_1685687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685687 prefixEnd_1685687 := by exact prefixLift 1685687
  have htrace : WordTrace (prefixWord ++ tailWord_1685687) baseStart_1685687 baseEnd_1685687 := by
    simpa [prefixWord, tailWord_1685687, baseEnd_1685687] using wordTrace_append hprefix tailTrace_1685687
  have hstable : (prefixWord ++ tailWord_1685687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685687).length < 2 ^ (prefixWord ++ tailWord_1685687).sum := by decide
  have hdescent : baseEnd_1685687 < baseStart_1685687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685800 : List Nat := [2, 1, 5, 1, 4, 1, 1, 2, 4]
def baseStart_1685800 : Nat := 118140960795 + 1685800 * 2 ^ 59
def prefixEnd_1685800 : Nat := 4983230072969 + 3 ^ 40 * 1685800 * 2
def baseEnd_1685800 : Nat := 384722527710937570420957

theorem tailTrace_1685800 : CollatzResearch.WordTrace tailWord_1685800 prefixEnd_1685800 384722527710937570420957 := by
  unfold tailWord_1685800
  simp only [CollatzResearch.WordTrace]
  refine ⟨30743088646320993281643427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40990784861761324375524569 30743088646320993281643427)
  ·
    refine ⟨46114632969481489922465141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30743088646320993281643427 46114632969481489922465141)
    ·
      refine ⟨4323246840888889680231107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46114632969481489922465141 4323246840888889680231107)
      ·
        refine ⟨6484870261333334520346661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4323246840888889680231107 6484870261333334520346661)
        ·
          refine ⟨1215913174000000222564999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6484870261333334520346661 1215913174000000222564999)
          ·
            refine ⟨1823869761000000333847499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215913174000000222564999 1823869761000000333847499)
            ·
              refine ⟨2735804641500000500771249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1823869761000000333847499 2735804641500000500771249)
              ·
                refine ⟨2051853481125000375578437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2735804641500000500771249 2051853481125000375578437)
                ·
                  refine ⟨384722527710937570420957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2051853481125000375578437 384722527710937570420957)
                  ·
                    rfl

theorem cell21_1685800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 4].length) (baseStart_1685800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685800 prefixEnd_1685800 := by exact prefixLift 1685800
  have htrace : WordTrace (prefixWord ++ tailWord_1685800) baseStart_1685800 baseEnd_1685800 := by
    simpa [prefixWord, tailWord_1685800, baseEnd_1685800] using wordTrace_append hprefix tailTrace_1685800
  have hstable : (prefixWord ++ tailWord_1685800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685800).length < 2 ^ (prefixWord ++ tailWord_1685800).sum := by decide
  have hdescent : baseEnd_1685800 < baseStart_1685800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685811 : List Nat := [1, 1, 1, 2, 5, 1, 1, 6, 3]
def baseStart_1685811 : Nat := 118140960795 + 1685811 * 2 ^ 59
def prefixEnd_1685811 : Nat := 4983230072969 + 3 ^ 40 * 1685811 * 2
def baseEnd_1685811 : Nat := 384725038060803995737601

theorem tailTrace_1685811 : CollatzResearch.WordTrace tailWord_1685811 prefixEnd_1685811 384725038060803995737601 := by
  unfold tailWord_1685811
  simp only [CollatzResearch.WordTrace]
  refine ⟨61486578495602135441937287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40991052330401423627958191 61486578495602135441937287)
  ·
    refine ⟨92229867743403203162905931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61486578495602135441937287 92229867743403203162905931)
    ·
      refine ⟨138344801615104804744358897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92229867743403203162905931 138344801615104804744358897)
      ·
        refine ⟨103758601211328603558269173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138344801615104804744358897 103758601211328603558269173)
        ·
          refine ⟨9727368863562056583587735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103758601211328603558269173 9727368863562056583587735)
          ·
            refine ⟨14591053295343084875381603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9727368863562056583587735 14591053295343084875381603)
            ·
              refine ⟨21886579943014627313072405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14591053295343084875381603 21886579943014627313072405)
              ·
                refine ⟨1025933434828810655300269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21886579943014627313072405 1025933434828810655300269)
                ·
                  refine ⟨384725038060803995737601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025933434828810655300269 384725038060803995737601)
                  ·
                    rfl

theorem cell21_1685811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 3].length) (baseStart_1685811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685811 prefixEnd_1685811 := by exact prefixLift 1685811
  have htrace : WordTrace (prefixWord ++ tailWord_1685811) baseStart_1685811 baseEnd_1685811 := by
    simpa [prefixWord, tailWord_1685811, baseEnd_1685811] using wordTrace_append hprefix tailTrace_1685811
  have hstable : (prefixWord ++ tailWord_1685811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685811).length < 2 ^ (prefixWord ++ tailWord_1685811).sum := by decide
  have hdescent : baseEnd_1685811 < baseStart_1685811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685845 : List Nat := [1, 3, 2, 2, 4, 2, 1, 3, 3]
def baseStart_1685845 : Nat := 118140960795 + 1685845 * 2 ^ 59
def prefixEnd_1685845 : Nat := 4983230072969 + 3 ^ 40 * 1685845 * 2
def baseEnd_1685845 : Nat := 384732797324027492170865

theorem tailTrace_1685845 : CollatzResearch.WordTrace tailWord_1685845 prefixEnd_1685845 384732797324027492170865 := by
  unfold tailWord_1685845
  simp only [CollatzResearch.WordTrace]
  refine ⟨61487818577478959248674989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40991879051652639499116659 61487818577478959248674989)
  ·
    refine ⟨23057931966554609718253121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61487818577478959248674989 23057931966554609718253121)
    ·
      refine ⟨17293448974915957288689841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23057931966554609718253121 17293448974915957288689841)
      ·
        refine ⟨12970086731186967966517381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17293448974915957288689841 12970086731186967966517381)
        ·
          refine ⟨2431891262097556493722009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12970086731186967966517381 2431891262097556493722009)
          ·
            refine ⟨1823918446573167370291507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2431891262097556493722009 1823918446573167370291507)
            ·
              refine ⟨2735877669859751055437261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1823918446573167370291507 2735877669859751055437261)
              ·
                refine ⟨1025954126197406645788973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2735877669859751055437261 1025954126197406645788973)
                ·
                  refine ⟨384732797324027492170865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025954126197406645788973 384732797324027492170865)
                  ·
                    rfl

theorem cell21_1685845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_1685845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685845 prefixEnd_1685845 := by exact prefixLift 1685845
  have htrace : WordTrace (prefixWord ++ tailWord_1685845) baseStart_1685845 baseEnd_1685845 := by
    simpa [prefixWord, tailWord_1685845, baseEnd_1685845] using wordTrace_append hprefix tailTrace_1685845
  have hstable : (prefixWord ++ tailWord_1685845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685845).length < 2 ^ (prefixWord ++ tailWord_1685845).sum := by decide
  have hdescent : baseEnd_1685845 < baseStart_1685845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685856 : List Nat := [2, 1, 1, 3, 5, 2, 7]
def baseStart_1685856 : Nat := 118140960795 + 1685856 * 2 ^ 59
def prefixEnd_1685856 : Nat := 4983230072969 + 3 ^ 40 * 1685856 * 2
def baseEnd_1685856 : Nat := 42748367519321546387501

theorem tailTrace_1685856 : CollatzResearch.WordTrace tailWord_1685856 prefixEnd_1685856 42748367519321546387501 := by
  unfold tailWord_1685856
  simp only [CollatzResearch.WordTrace]
  refine ⟨30744109890219554063662711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40992146520292738751550281 30744109890219554063662711)
  ·
    refine ⟨46116164835329331095494067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30744109890219554063662711 46116164835329331095494067)
    ·
      refine ⟨69174247252993996643241101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46116164835329331095494067 69174247252993996643241101)
      ·
        refine ⟨25940342719872748741215413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69174247252993996643241101 25940342719872748741215413)
        ·
          refine ⟨2431907129988070194488945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25940342719872748741215413 2431907129988070194488945)
          ·
            refine ⟨1823930347491052645866709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2431907129988070194488945 1823930347491052645866709)
            ·
              refine ⟨42748367519321546387501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1823930347491052645866709 42748367519321546387501)
              ·
                rfl

theorem cell21_1685856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 7].length) (baseStart_1685856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685856 prefixEnd_1685856 := by exact prefixLift 1685856
  have htrace : WordTrace (prefixWord ++ tailWord_1685856) baseStart_1685856 baseEnd_1685856 := by
    simpa [prefixWord, tailWord_1685856, baseEnd_1685856] using wordTrace_append hprefix tailTrace_1685856
  have hstable : (prefixWord ++ tailWord_1685856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685856).length < 2 ^ (prefixWord ++ tailWord_1685856).sum := by decide
  have hdescent : baseEnd_1685856 < baseStart_1685856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685884 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 8]
def baseStart_1685884 : Nat := 118140960795 + 1685884 * 2 ^ 59
def prefixEnd_1685884 : Nat := 4983230072969 + 3 ^ 40 * 1685884 * 2
def baseEnd_1685884 : Nat := 384741697655372091020785

theorem tailTrace_1685884 : CollatzResearch.WordTrace tailWord_1685884 prefixEnd_1685884 384741697655372091020785 := by
  unfold tailWord_1685884
  simp only [CollatzResearch.WordTrace]
  refine ⟨30744620512168834454672353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40992827349558445939563137 30744620512168834454672353)
  ·
    refine ⟨23058465384126625841004265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30744620512168834454672353 23058465384126625841004265)
    ·
      refine ⟨17293849038094969380753199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23058465384126625841004265 17293849038094969380753199)
      ·
        refine ⟨25940773557142454071129799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17293849038094969380753199 25940773557142454071129799)
        ·
          refine ⟨38911160335713681106694699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25940773557142454071129799 38911160335713681106694699)
          ·
            refine ⟨58366740503570521660042049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38911160335713681106694699 58366740503570521660042049)
            ·
              refine ⟨43775055377677891245031537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58366740503570521660042049 43775055377677891245031537)
              ·
                refine ⟨32831291533258418433773653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43775055377677891245031537 32831291533258418433773653)
                ·
                  refine ⟨384741697655372091020785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32831291533258418433773653 384741697655372091020785)
                  ·
                    rfl

theorem cell21_1685884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_1685884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685884 prefixEnd_1685884 := by exact prefixLift 1685884
  have htrace : WordTrace (prefixWord ++ tailWord_1685884) baseStart_1685884 baseEnd_1685884 := by
    simpa [prefixWord, tailWord_1685884, baseEnd_1685884] using wordTrace_append hprefix tailTrace_1685884
  have hstable : (prefixWord ++ tailWord_1685884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685884).length < 2 ^ (prefixWord ++ tailWord_1685884).sum := by decide
  have hdescent : baseEnd_1685884 < baseStart_1685884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685921 : List Nat := [1, 2, 3, 5, 1, 1, 1, 4, 3]
def baseStart_1685921 : Nat := 118140960795 + 1685921 * 2 ^ 59
def prefixEnd_1685921 : Nat := 4983230072969 + 3 ^ 40 * 1685921 * 2
def baseEnd_1685921 : Nat := 384750141559468248904043

theorem tailTrace_1685921 : CollatzResearch.WordTrace tailWord_1685921 prefixEnd_1685921 384750141559468248904043 := by
  unfold tailWord_1685921
  simp only [CollatzResearch.WordTrace]
  refine ⟨61490590525203624228441617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40993727016802416152294411 61490590525203624228441617)
  ·
    refine ⟨46117942893902718171331213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61490590525203624228441617 46117942893902718171331213)
    ·
      refine ⟨17294228585213519314249205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46117942893902718171331213 17294228585213519314249205)
      ·
        refine ⟨1621333929863767435710863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17294228585213519314249205 1621333929863767435710863)
        ·
          refine ⟨2432000894795651153566295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1621333929863767435710863 2432000894795651153566295)
          ·
            refine ⟨3648001342193476730349443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432000894795651153566295 3648001342193476730349443)
            ·
              refine ⟨5472002013290215095524165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648001342193476730349443 5472002013290215095524165)
              ·
                refine ⟨1026000377491915330410781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5472002013290215095524165 1026000377491915330410781)
                ·
                  refine ⟨384750141559468248904043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026000377491915330410781 384750141559468248904043)
                  ·
                    rfl

theorem cell21_1685921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 3].length) (baseStart_1685921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685921 prefixEnd_1685921 := by exact prefixLift 1685921
  have htrace : WordTrace (prefixWord ++ tailWord_1685921) baseStart_1685921 baseEnd_1685921 := by
    simpa [prefixWord, tailWord_1685921, baseEnd_1685921] using wordTrace_append hprefix tailTrace_1685921
  have hstable : (prefixWord ++ tailWord_1685921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685921).length < 2 ^ (prefixWord ++ tailWord_1685921).sum := by decide
  have hdescent : baseEnd_1685921 < baseStart_1685921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685929 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 9]
def baseStart_1685929 : Nat := 118140960795 + 1685929 * 2 ^ 59
def prefixEnd_1685929 : Nat := 4983230072969 + 3 ^ 40 * 1685929 * 2
def baseEnd_1685929 : Nat := 384751967268462012770693

theorem tailTrace_1685929 : CollatzResearch.WordTrace tailWord_1685929 prefixEnd_1685929 384751967268462012770693 := by
  unfold tailWord_1685929
  simp only [CollatzResearch.WordTrace]
  refine ⟨61490882309174641594732841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40993921539449761063155227 61490882309174641594732841)
  ·
    refine ⟨46118161731880981196049631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61490882309174641594732841 46118161731880981196049631)
    ·
      refine ⟨69177242597821471794074447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46118161731880981196049631 69177242597821471794074447)
      ·
        refine ⟨103765863896732207691111671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69177242597821471794074447 103765863896732207691111671)
        ·
          refine ⟨155648795845098311536667507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103765863896732207691111671 155648795845098311536667507)
          ·
            refine ⟨233473193767647467305001261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155648795845098311536667507 233473193767647467305001261)
            ·
              refine ⟨87552447662867800239375473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233473193767647467305001261 87552447662867800239375473)
              ·
                refine ⟨65664335747150850179531605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87552447662867800239375473 65664335747150850179531605)
                ·
                  refine ⟨384751967268462012770693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65664335747150850179531605 384751967268462012770693)
                  ·
                    rfl

theorem cell21_1685929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_1685929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685929 prefixEnd_1685929 := by exact prefixLift 1685929
  have htrace : WordTrace (prefixWord ++ tailWord_1685929) baseStart_1685929 baseEnd_1685929 := by
    simpa [prefixWord, tailWord_1685929, baseEnd_1685929] using wordTrace_append hprefix tailTrace_1685929
  have hstable : (prefixWord ++ tailWord_1685929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685929).length < 2 ^ (prefixWord ++ tailWord_1685929).sum := by decide
  have hdescent : baseEnd_1685929 < baseStart_1685929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685991 : List Nat := [1, 1, 5, 2, 1, 1, 2, 8]
def baseStart_1685991 : Nat := 118140960795 + 1685991 * 2 ^ 59
def prefixEnd_1685991 : Nat := 4983230072969 + 3 ^ 40 * 1685991 * 2
def baseEnd_1685991 : Nat := 128255372171054560912411

theorem tailTrace_1685991 : CollatzResearch.WordTrace tailWord_1685991 prefixEnd_1685991 128255372171054560912411 := by
  unfold tailWord_1685991
  simp only [CollatzResearch.WordTrace]
  refine ⟨61493143634950026183489827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40995429089966684122326551 61493143634950026183489827)
  ·
    refine ⟨92239715452425039275234741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61493143634950026183489827 92239715452425039275234741)
    ·
      refine ⟨8647473323664847432053257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92239715452425039275234741 8647473323664847432053257)
      ·
        refine ⟨6485604992748635574039943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8647473323664847432053257 6485604992748635574039943)
        ·
          refine ⟨9728407489122953361059915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6485604992748635574039943 9728407489122953361059915)
          ·
            refine ⟨14592611233684430041589873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9728407489122953361059915 14592611233684430041589873)
            ·
              refine ⟨10944458425263322531192405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14592611233684430041589873 10944458425263322531192405)
              ·
                refine ⟨128255372171054560912411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10944458425263322531192405 128255372171054560912411)
                ·
                  rfl

theorem cell21_1685991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 8].length) (baseStart_1685991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1685991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1685991 prefixEnd_1685991 := by exact prefixLift 1685991
  have htrace : WordTrace (prefixWord ++ tailWord_1685991) baseStart_1685991 baseEnd_1685991 := by
    simpa [prefixWord, tailWord_1685991, baseEnd_1685991] using wordTrace_append hprefix tailTrace_1685991
  have hstable : (prefixWord ++ tailWord_1685991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685991).length < 2 ^ (prefixWord ++ tailWord_1685991).sum := by decide
  have hdescent : baseEnd_1685991 < baseStart_1685991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686098 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_1686098 : Nat := 118140960795 + 1686098 * 2 ^ 59
def prefixEnd_1686098 : Nat := 4983230072969 + 3 ^ 40 * 1686098 * 2
def baseEnd_1686098 : Nat := 384790535370955274453681

theorem tailTrace_1686098 : CollatzResearch.WordTrace tailWord_1686098 prefixEnd_1686098 384790535370955274453681 := by
  unfold tailWord_1686098
  simp only [CollatzResearch.WordTrace]
  refine ⟨15374261561390595864408737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40998030830374922305089965 15374261561390595864408737)
  ·
    refine ⟨11530696171042946898306553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15374261561390595864408737 11530696171042946898306553)
    ·
      refine ⟨8648022128282210173729915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11530696171042946898306553 8648022128282210173729915)
      ·
        refine ⟨12972033192423315260594873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8648022128282210173729915 12972033192423315260594873)
        ·
          refine ⟨9729024894317486445446155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12972033192423315260594873 9729024894317486445446155)
          ·
            refine ⟨14593537341476229668169233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9729024894317486445446155 14593537341476229668169233)
            ·
              refine ⟨10945153006107172251126925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14593537341476229668169233 10945153006107172251126925)
              ·
                refine ⟨4104432377290189594172597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10945153006107172251126925 4104432377290189594172597)
                ·
                  refine ⟨384790535370955274453681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4104432377290189594172597 384790535370955274453681)
                  ·
                    rfl

theorem cell21_1686098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_1686098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686098 prefixEnd_1686098 := by exact prefixLift 1686098
  have htrace : WordTrace (prefixWord ++ tailWord_1686098) baseStart_1686098 baseEnd_1686098 := by
    simpa [prefixWord, tailWord_1686098, baseEnd_1686098] using wordTrace_append hprefix tailTrace_1686098
  have hstable : (prefixWord ++ tailWord_1686098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686098).length < 2 ^ (prefixWord ++ tailWord_1686098).sum := by decide
  have hdescent : baseEnd_1686098 < baseStart_1686098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686177 : List Nat := [1, 2, 3, 3, 3, 2, 2, 5]
def baseStart_1686177 : Nat := 118140960795 + 1686177 * 2 ^ 59
def prefixEnd_1686177 : Nat := 4983230072969 + 3 ^ 40 * 1686177 * 2
def baseEnd_1686177 : Nat := 128269521415756230878951

theorem tailTrace_1686177 : CollatzResearch.WordTrace tailWord_1686177 prefixEnd_1686177 128269521415756230878951 := by
  unfold tailWord_1686177
  simp only [CollatzResearch.WordTrace]
  refine ⟨61499927612276179949760785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40999951741517453299840523 61499927612276179949760785)
  ·
    refine ⟨46124945709207134962320589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61499927612276179949760785 46124945709207134962320589)
    ·
      refine ⟨17296854640952675610870221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46124945709207134962320589 17296854640952675610870221)
      ·
        refine ⟨6486320490357253354076333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17296854640952675610870221 6486320490357253354076333)
        ·
          refine ⟨2432370183883970007778625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6486320490357253354076333 2432370183883970007778625)
          ·
            refine ⟨1824277637912977505833969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2432370183883970007778625 1824277637912977505833969)
            ·
              refine ⟨1368208228434733129375477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1824277637912977505833969 1368208228434733129375477)
              ·
                refine ⟨128269521415756230878951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1368208228434733129375477 128269521415756230878951)
                ·
                  rfl

theorem cell21_1686177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 5].length) (baseStart_1686177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686177 prefixEnd_1686177 := by exact prefixLift 1686177
  have htrace : WordTrace (prefixWord ++ tailWord_1686177) baseStart_1686177 baseEnd_1686177 := by
    simpa [prefixWord, tailWord_1686177, baseEnd_1686177] using wordTrace_append hprefix tailTrace_1686177
  have hstable : (prefixWord ++ tailWord_1686177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686177).length < 2 ^ (prefixWord ++ tailWord_1686177).sum := by decide
  have hdescent : baseEnd_1686177 < baseStart_1686177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686191 : List Nat := [1, 1, 2, 1, 2, 5, 3, 3, 3]
def baseStart_1686191 : Nat := 118140960795 + 1686191 * 2 ^ 59
def prefixEnd_1686191 : Nat := 4983230072969 + 3 ^ 40 * 1686191 * 2
def baseEnd_1686191 : Nat := 384811759238007779403491

theorem tailTrace_1686191 : CollatzResearch.WordTrace tailWord_1686191 prefixEnd_1686191 384811759238007779403491 := by
  unfold tailWord_1686191
  simp only [CollatzResearch.WordTrace]
  refine ⟨61500438234225460340770427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41000292156150306893846951 61500438234225460340770427)
  ·
    refine ⟨92250657351338190511155641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61500438234225460340770427 92250657351338190511155641)
    ·
      refine ⟨69187993013503642883366731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92250657351338190511155641 69187993013503642883366731)
      ·
        refine ⟨103781989520255464325050097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69187993013503642883366731 103781989520255464325050097)
        ·
          refine ⟨77836492140191598243787573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103781989520255464325050097 77836492140191598243787573)
          ·
            refine ⟨7297171138142962335355085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77836492140191598243787573 7297171138142962335355085)
            ·
              refine ⟨2736439176803610875758157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7297171138142962335355085 2736439176803610875758157)
              ·
                refine ⟨1026164691301354078409309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2736439176803610875758157 1026164691301354078409309)
                ·
                  refine ⟨384811759238007779403491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026164691301354078409309 384811759238007779403491)
                  ·
                    rfl

theorem cell21_1686191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 3].length) (baseStart_1686191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686191 prefixEnd_1686191 := by exact prefixLift 1686191
  have htrace : WordTrace (prefixWord ++ tailWord_1686191) baseStart_1686191 baseEnd_1686191 := by
    simpa [prefixWord, tailWord_1686191, baseEnd_1686191] using wordTrace_append hprefix tailTrace_1686191
  have hstable : (prefixWord ++ tailWord_1686191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686191).length < 2 ^ (prefixWord ++ tailWord_1686191).sum := by decide
  have hdescent : baseEnd_1686191 < baseStart_1686191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686208 : List Nat := [2, 1, 1, 2, 4, 3, 3, 2, 3]
def baseStart_1686208 : Nat := 118140960795 + 1686208 * 2 ^ 59
def prefixEnd_1686208 : Nat := 4983230072969 + 3 ^ 40 * 1686208 * 2
def baseEnd_1686208 : Nat := 384815638869619527620123

theorem tailTrace_1686208 : CollatzResearch.WordTrace tailWord_1686208 prefixEnd_1686208 384815638869619527620123 := by
  unfold tailWord_1686208
  simp only [CollatzResearch.WordTrace]
  refine ⟨30750529137581936122069639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41000705516775914829426185 30750529137581936122069639)
  ·
    refine ⟨46125793706372904183104459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30750529137581936122069639 46125793706372904183104459)
    ·
      refine ⟨69188690559559356274656689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46125793706372904183104459 69188690559559356274656689)
      ·
        refine ⟨51891517919669517205992517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69188690559559356274656689 51891517919669517205992517)
        ·
          refine ⟨9729659609938034476123597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51891517919669517205992517 9729659609938034476123597)
          ·
            refine ⟨3648622353726762928546349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9729659609938034476123597 3648622353726762928546349)
            ·
              refine ⟨1368233382647536098204881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3648622353726762928546349 1368233382647536098204881)
              ·
                refine ⟨1026175036985652073653661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1368233382647536098204881 1026175036985652073653661)
                ·
                  refine ⟨384815638869619527620123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026175036985652073653661 384815638869619527620123)
                  ·
                    rfl

theorem cell21_1686208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 3].length) (baseStart_1686208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686208 prefixEnd_1686208 := by exact prefixLift 1686208
  have htrace : WordTrace (prefixWord ++ tailWord_1686208) baseStart_1686208 baseEnd_1686208 := by
    simpa [prefixWord, tailWord_1686208, baseEnd_1686208] using wordTrace_append hprefix tailTrace_1686208
  have hstable : (prefixWord ++ tailWord_1686208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686208).length < 2 ^ (prefixWord ++ tailWord_1686208).sum := by decide
  have hdescent : baseEnd_1686208 < baseStart_1686208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686214 : List Nat := [6, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1686214 : Nat := 118140960795 + 1686214 * 2 ^ 59
def prefixEnd_1686214 : Nat := 4983230072969 + 3 ^ 40 * 1686214 * 2
def baseEnd_1686214 : Nat := 384817008151364850520111

theorem tailTrace_1686214 : CollatzResearch.WordTrace tailWord_1686214 prefixEnd_1686214 384817008151364850520111 := by
  unfold tailWord_1686214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1921914909785691727151803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41000851408761423512571797 1921914909785691727151803)
  ·
    refine ⟨2882872364678537590727705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1921914909785691727151803 2882872364678537590727705)
    ·
      refine ⟨2162154273508903193045779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2882872364678537590727705 2162154273508903193045779)
      ·
        refine ⟨3243231410263354789568669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2162154273508903193045779 3243231410263354789568669)
        ·
          refine ⟨1216211778848758046088251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3243231410263354789568669 1216211778848758046088251)
          ·
            refine ⟨1824317668273137069132377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216211778848758046088251 1824317668273137069132377)
            ·
              refine ⟨1368238251204852801849283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1824317668273137069132377 1368238251204852801849283)
              ·
                refine ⟨2052357376807279202773925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368238251204852801849283 2052357376807279202773925)
                ·
                  refine ⟨384817008151364850520111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2052357376807279202773925 384817008151364850520111)
                  ·
                    rfl

theorem cell21_1686214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1686214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686214 prefixEnd_1686214 := by exact prefixLift 1686214
  have htrace : WordTrace (prefixWord ++ tailWord_1686214) baseStart_1686214 baseEnd_1686214 := by
    simpa [prefixWord, tailWord_1686214, baseEnd_1686214] using wordTrace_append hprefix tailTrace_1686214
  have hstable : (prefixWord ++ tailWord_1686214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686214).length < 2 ^ (prefixWord ++ tailWord_1686214).sum := by decide
  have hdescent : baseEnd_1686214 < baseStart_1686214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686222 : List Nat := [4, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_1686222 : Nat := 118140960795 + 1686222 * 2 ^ 59
def prefixEnd_1686222 : Nat := 4983230072969 + 3 ^ 40 * 1686222 * 2
def baseEnd_1686222 : Nat := 384818833860358614386761

theorem tailTrace_1686222 : CollatzResearch.WordTrace tailWord_1686222 prefixEnd_1686222 384818833860358614386761 := by
  unfold tailWord_1686222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7687696112139144079393615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41001045931408768423432613 7687696112139144079393615)
  ·
    refine ⟨11531544168208716119090423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7687696112139144079393615 11531544168208716119090423)
    ·
      refine ⟨17297316252313074178635635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11531544168208716119090423 17297316252313074178635635)
      ·
        refine ⟨25945974378469611267953453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17297316252313074178635635 25945974378469611267953453)
        ·
          refine ⟨9729740391926104225482545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25945974378469611267953453 9729740391926104225482545)
          ·
            refine ⟨7297305293944578169111909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9729740391926104225482545 7297305293944578169111909)
            ·
              refine ⟨1368244742614608406708483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7297305293944578169111909 1368244742614608406708483)
              ·
                refine ⟨2052367113921912610062725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368244742614608406708483 2052367113921912610062725)
                ·
                  refine ⟨384818833860358614386761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2052367113921912610062725 384818833860358614386761)
                  ·
                    rfl

theorem cell21_1686222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_1686222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686222 prefixEnd_1686222 := by exact prefixLift 1686222
  have htrace : WordTrace (prefixWord ++ tailWord_1686222) baseStart_1686222 baseEnd_1686222 := by
    simpa [prefixWord, tailWord_1686222, baseEnd_1686222] using wordTrace_append hprefix tailTrace_1686222
  have hstable : (prefixWord ++ tailWord_1686222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686222).length < 2 ^ (prefixWord ++ tailWord_1686222).sum := by decide
  have hdescent : baseEnd_1686222 < baseStart_1686222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686233 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 7]
def baseStart_1686233 : Nat := 118140960795 + 1686233 * 2 ^ 59
def prefixEnd_1686233 : Nat := 4983230072969 + 3 ^ 40 * 1686233 * 2
def baseEnd_1686233 : Nat := 384821344210225039703405

theorem tailTrace_1686233 : CollatzResearch.WordTrace tailWord_1686233 prefixEnd_1686233 384821344210225039703405 := by
  unfold tailWord_1686233
  simp only [CollatzResearch.WordTrace]
  refine ⟨61501970100073301513799353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41001313400048867675866235 61501970100073301513799353)
  ·
    refine ⟨46126477575054976135349515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61501970100073301513799353 46126477575054976135349515)
    ·
      refine ⟨69189716362582464203024273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46126477575054976135349515 69189716362582464203024273)
      ·
        refine ⟨51892287271936848152268205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69189716362582464203024273 51892287271936848152268205)
        ·
          refine ⟨19459607726976318057100577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51892287271936848152268205 19459607726976318057100577)
          ·
            refine ⟨14594705795232238542825433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19459607726976318057100577 14594705795232238542825433)
            ·
              refine ⟨10946029346424178907119075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14594705795232238542825433 10946029346424178907119075)
              ·
                refine ⟨16419044019636268360678613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10946029346424178907119075 16419044019636268360678613)
                ·
                  refine ⟨384821344210225039703405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16419044019636268360678613 384821344210225039703405)
                  ·
                    rfl

theorem cell21_1686233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_1686233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686233 prefixEnd_1686233 := by exact prefixLift 1686233
  have htrace : WordTrace (prefixWord ++ tailWord_1686233) baseStart_1686233 baseEnd_1686233 := by
    simpa [prefixWord, tailWord_1686233, baseEnd_1686233] using wordTrace_append hprefix tailTrace_1686233
  have hstable : (prefixWord ++ tailWord_1686233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686233).length < 2 ^ (prefixWord ++ tailWord_1686233).sum := by decide
  have hdescent : baseEnd_1686233 < baseStart_1686233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686236 : List Nat := [2, 2, 5, 1, 1, 1, 2, 7]
def baseStart_1686236 : Nat := 118140960795 + 1686236 * 2 ^ 59
def prefixEnd_1686236 : Nat := 4983230072969 + 3 ^ 40 * 1686236 * 2
def baseEnd_1686236 : Nat := 128274009617032567051133

theorem tailTrace_1686236 : CollatzResearch.WordTrace tailWord_1686236 prefixEnd_1686236 128274009617032567051133 := by
  unfold tailWord_1686236
  simp only [CollatzResearch.WordTrace]
  refine ⟨30751039759531216513079281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41001386346041622017439041 30751039759531216513079281)
  ·
    refine ⟨23063279819648412384809461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30751039759531216513079281 23063279819648412384809461)
    ·
      refine ⟨2162182483092038661075887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23063279819648412384809461 2162182483092038661075887)
      ·
        refine ⟨3243273724638057991613831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2162182483092038661075887 3243273724638057991613831)
        ·
          refine ⟨4864910586957086987420747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243273724638057991613831 4864910586957086987420747)
          ·
            refine ⟨7297365880435630481131121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4864910586957086987420747 7297365880435630481131121)
            ·
              refine ⟨5473024410326722860848341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7297365880435630481131121 5473024410326722860848341)
              ·
                refine ⟨128274009617032567051133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5473024410326722860848341 128274009617032567051133)
                ·
                  rfl

theorem cell21_1686236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_1686236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686236 prefixEnd_1686236 := by exact prefixLift 1686236
  have htrace : WordTrace (prefixWord ++ tailWord_1686236) baseStart_1686236 baseEnd_1686236 := by
    simpa [prefixWord, tailWord_1686236, baseEnd_1686236] using wordTrace_append hprefix tailTrace_1686236
  have hstable : (prefixWord ++ tailWord_1686236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686236).length < 2 ^ (prefixWord ++ tailWord_1686236).sum := by decide
  have hdescent : baseEnd_1686236 < baseStart_1686236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686301 : List Nat := [1, 4, 2, 4, 1, 1, 2, 3, 3]
def baseStart_1686301 : Nat := 118140960795 + 1686301 * 2 ^ 59
def prefixEnd_1686301 : Nat := 4983230072969 + 3 ^ 40 * 1686301 * 2
def baseEnd_1686301 : Nat := 384836862736672032569933

theorem tailTrace_1686301 : CollatzResearch.WordTrace tailWord_1686301 prefixEnd_1686301 384836862736672032569933 := by
  unfold tailWord_1686301
  simp only [CollatzResearch.WordTrace]
  refine ⟨61504450263826949127274757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41002966842551299418183171 61504450263826949127274757)
  ·
    refine ⟨11532084424467552961364017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61504450263826949127274757 11532084424467552961364017)
    ·
      refine ⟨8649063318350664721023013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11532084424467552961364017 8649063318350664721023013)
      ·
        refine ⟨1621699372190749635191815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8649063318350664721023013 1621699372190749635191815)
        ·
          refine ⟨2432549058286124452787723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1621699372190749635191815 2432549058286124452787723)
          ·
            refine ⟨3648823587429186679181585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432549058286124452787723 3648823587429186679181585)
            ·
              refine ⟨2736617690571890009386189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3648823587429186679181585 2736617690571890009386189)
              ·
                refine ⟨1026231633964458753519821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2736617690571890009386189 1026231633964458753519821)
                ·
                  refine ⟨384836862736672032569933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026231633964458753519821 384836862736672032569933)
                  ·
                    rfl

theorem cell21_1686301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_1686301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686301 prefixEnd_1686301 := by exact prefixLift 1686301
  have htrace : WordTrace (prefixWord ++ tailWord_1686301) baseStart_1686301 baseEnd_1686301 := by
    simpa [prefixWord, tailWord_1686301, baseEnd_1686301] using wordTrace_append hprefix tailTrace_1686301
  have hstable : (prefixWord ++ tailWord_1686301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686301).length < 2 ^ (prefixWord ++ tailWord_1686301).sum := by decide
  have hdescent : baseEnd_1686301 < baseStart_1686301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686309 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 7]
def baseStart_1686309 : Nat := 118140960795 + 1686309 * 2 ^ 59
def prefixEnd_1686309 : Nat := 4983230072969 + 3 ^ 40 * 1686309 * 2
def baseEnd_1686309 : Nat := 384838688445665796436583

theorem tailTrace_1686309 : CollatzResearch.WordTrace tailWord_1686309 prefixEnd_1686309 384838688445665796436583 := by
  unfold tailWord_1686309
  simp only [CollatzResearch.WordTrace]
  refine ⟨61504742047797966493565981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41003161365198644329043987 61504742047797966493565981)
  ·
    refine ⟨23064278267924237435087243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61504742047797966493565981 23064278267924237435087243)
    ·
      refine ⟨34596417401886356152630865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23064278267924237435087243 34596417401886356152630865)
      ·
        refine ⟨25947313051414767114473149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34596417401886356152630865 25947313051414767114473149)
        ·
          refine ⟨9730242394280537667927431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25947313051414767114473149 9730242394280537667927431)
          ·
            refine ⟨14595363591420806501891147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9730242394280537667927431 14595363591420806501891147)
            ·
              refine ⟨21893045387131209752836721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14595363591420806501891147 21893045387131209752836721)
              ·
                refine ⟨16419784040348407314627541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21893045387131209752836721 16419784040348407314627541)
                ·
                  refine ⟨384838688445665796436583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16419784040348407314627541 384838688445665796436583)
                  ·
                    rfl

theorem cell21_1686309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_1686309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686309 prefixEnd_1686309 := by exact prefixLift 1686309
  have htrace : WordTrace (prefixWord ++ tailWord_1686309) baseStart_1686309 baseEnd_1686309 := by
    simpa [prefixWord, tailWord_1686309, baseEnd_1686309] using wordTrace_append hprefix tailTrace_1686309
  have hstable : (prefixWord ++ tailWord_1686309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686309).length < 2 ^ (prefixWord ++ tailWord_1686309).sum := by decide
  have hdescent : baseEnd_1686309 < baseStart_1686309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686371 : List Nat := [1, 1, 1, 5, 3, 3, 7]
def baseStart_1686371 : Nat := 118140960795 + 1686371 * 2 ^ 59
def prefixEnd_1686371 : Nat := 4983230072969 + 3 ^ 40 * 1686371 * 2
def baseEnd_1686371 : Nat := 42761426410040829600347

theorem tailTrace_1686371 : CollatzResearch.WordTrace tailWord_1686371 prefixEnd_1686371 42761426410040829600347 := by
  unfold tailWord_1686371
  simp only [CollatzResearch.WordTrace]
  refine ⟨61507003373573351082322967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41004668915715567388215311 61507003373573351082322967)
  ·
    refine ⟨92260505060360026623484451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61507003373573351082322967 92260505060360026623484451)
    ·
      refine ⟨138390757590540039935226677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92260505060360026623484451 138390757590540039935226677)
      ·
        refine ⟨12974133524113128743927501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138390757590540039935226677 12974133524113128743927501)
        ·
          refine ⟨4865300071542423278972813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12974133524113128743927501 4865300071542423278972813)
          ·
            refine ⟨1824487526828408729614805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4865300071542423278972813 1824487526828408729614805)
            ·
              refine ⟨42761426410040829600347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1824487526828408729614805 42761426410040829600347)
              ·
                rfl

theorem cell21_1686371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 7].length) (baseStart_1686371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686371 prefixEnd_1686371 := by exact prefixLift 1686371
  have htrace : WordTrace (prefixWord ++ tailWord_1686371) baseStart_1686371 baseEnd_1686371 := by
    simpa [prefixWord, tailWord_1686371, baseEnd_1686371] using wordTrace_append hprefix tailTrace_1686371
  have hstable : (prefixWord ++ tailWord_1686371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686371).length < 2 ^ (prefixWord ++ tailWord_1686371).sum := by decide
  have hdescent : baseEnd_1686371 < baseStart_1686371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686433 : List Nat := [1, 2, 3, 4, 1, 1, 1, 4, 4]
def baseStart_1686433 : Nat := 118140960795 + 1686433 * 2 ^ 59
def prefixEnd_1686433 : Nat := 4983230072969 + 3 ^ 40 * 1686433 * 2
def baseEnd_1686433 : Nat := 384866986935069136369663

theorem tailTrace_1686433 : CollatzResearch.WordTrace tailWord_1686433 prefixEnd_1686433 384866986935069136369663 := by
  unfold tailWord_1686433
  simp only [CollatzResearch.WordTrace]
  refine ⟨61509264699348735671079953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41006176466232490447386635 61509264699348735671079953)
  ·
    refine ⟨46131948524511551753309965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61509264699348735671079953 46131948524511551753309965)
    ·
      refine ⟨17299480696691831907491237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46131948524511551753309965 17299480696691831907491237)
      ·
        refine ⟨3243652630629718482654607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17299480696691831907491237 3243652630629718482654607)
        ·
          refine ⟨4865478945944577723981911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243652630629718482654607 4865478945944577723981911)
          ·
            refine ⟨7298218418916866585972867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4865478945944577723981911 7298218418916866585972867)
            ·
              refine ⟨10947327628375299878959301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7298218418916866585972867 10947327628375299878959301)
              ·
                refine ⟨2052623930320368727304869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10947327628375299878959301 2052623930320368727304869)
                ·
                  refine ⟨384866986935069136369663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2052623930320368727304869 384866986935069136369663)
                  ·
                    rfl

theorem cell21_1686433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_1686433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686433 prefixEnd_1686433 := by exact prefixLift 1686433
  have htrace : WordTrace (prefixWord ++ tailWord_1686433) baseStart_1686433 baseEnd_1686433 := by
    simpa [prefixWord, tailWord_1686433, baseEnd_1686433] using wordTrace_append hprefix tailTrace_1686433
  have hstable : (prefixWord ++ tailWord_1686433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686433).length < 2 ^ (prefixWord ++ tailWord_1686433).sum := by decide
  have hdescent : baseEnd_1686433 < baseStart_1686433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686546 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 5]
def baseStart_1686546 : Nat := 118140960795 + 1686546 * 2 ^ 59
def prefixEnd_1686546 : Nat := 4983230072969 + 3 ^ 40 * 1686546 * 2
def baseEnd_1686546 : Nat := 384892775074606050986099

theorem tailTrace_1686546 : CollatzResearch.WordTrace tailWord_1686546 prefixEnd_1686546 384892775074606050986099 := by
  unfold tailWord_1686546
  simp only [CollatzResearch.WordTrace]
  refine ⟨15378346536984838992485873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41008924098626237313295661 15378346536984838992485873)
  ·
    refine ⟨11533759902738629244364405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15378346536984838992485873 11533759902738629244364405)
    ·
      refine ⟨1081289990881746491659163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11533759902738629244364405 1081289990881746491659163)
      ·
        refine ⟨1621934986322619737488745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081289990881746491659163 1621934986322619737488745)
        ·
          refine ⟨1216451239741964803116559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1621934986322619737488745 1216451239741964803116559)
          ·
            refine ⟨1824676859612947204674839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216451239741964803116559 1824676859612947204674839)
            ·
              refine ⟨2737015289419420807012259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824676859612947204674839 2737015289419420807012259)
              ·
                refine ⟨4105522934129131210518389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737015289419420807012259 4105522934129131210518389)
                ·
                  refine ⟨384892775074606050986099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4105522934129131210518389 384892775074606050986099)
                  ·
                    rfl

theorem cell21_1686546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_1686546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686546 prefixEnd_1686546 := by exact prefixLift 1686546
  have htrace : WordTrace (prefixWord ++ tailWord_1686546) baseStart_1686546 baseEnd_1686546 := by
    simpa [prefixWord, tailWord_1686546, baseEnd_1686546] using wordTrace_append hprefix tailTrace_1686546
  have hstable : (prefixWord ++ tailWord_1686546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686546).length < 2 ^ (prefixWord ++ tailWord_1686546).sum := by decide
  have hdescent : baseEnd_1686546 < baseStart_1686546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686560 : List Nat := [2, 1, 1, 7, 2, 1, 2, 1, 4]
def baseStart_1686560 : Nat := 118140960795 + 1686560 * 2 ^ 59
def prefixEnd_1686560 : Nat := 4983230072969 + 3 ^ 40 * 1686560 * 2
def baseEnd_1686560 : Nat := 384895970065345137752737

theorem tailTrace_1686560 : CollatzResearch.WordTrace tailWord_1686560 prefixEnd_1686560 384895970065345137752737 := by
  unfold tailWord_1686560
  simp only [CollatzResearch.WordTrace]
  refine ⟨30756948384944318180476567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41009264513259090907302089 30756948384944318180476567)
  ·
    refine ⟨46135422577416477270714851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30756948384944318180476567 46135422577416477270714851)
    ·
      refine ⟨69203133866124715906072277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46135422577416477270714851 69203133866124715906072277)
      ·
        refine ⟨1621948449987298029048569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 69203133866124715906072277 1621948449987298029048569)
        ·
          refine ⟨1216461337490473521786427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1621948449987298029048569 1216461337490473521786427)
          ·
            refine ⟨1824692006235710282679641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216461337490473521786427 1824692006235710282679641)
            ·
              refine ⟨1368519004676782712009731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1824692006235710282679641 1368519004676782712009731)
              ·
                refine ⟨2052778507015174068014597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368519004676782712009731 2052778507015174068014597)
                ·
                  refine ⟨384895970065345137752737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2052778507015174068014597 384895970065345137752737)
                  ·
                    rfl

theorem cell21_1686560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 4].length) (baseStart_1686560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686560 prefixEnd_1686560 := by exact prefixLift 1686560
  have htrace : WordTrace (prefixWord ++ tailWord_1686560) baseStart_1686560 baseEnd_1686560 := by
    simpa [prefixWord, tailWord_1686560, baseEnd_1686560] using wordTrace_append hprefix tailTrace_1686560
  have hstable : (prefixWord ++ tailWord_1686560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686560).length < 2 ^ (prefixWord ++ tailWord_1686560).sum := by decide
  have hdescent : baseEnd_1686560 < baseStart_1686560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686605 : List Nat := [1, 6, 1, 1, 1, 4, 2, 2, 3]
def baseStart_1686605 : Nat := 118140960795 + 1686605 * 2 ^ 59
def prefixEnd_1686605 : Nat := 4983230072969 + 3 ^ 40 * 1686605 * 2
def baseEnd_1686605 : Nat := 384906239678435059502645

theorem tailTrace_1686605 : CollatzResearch.WordTrace tailWord_1686605 prefixEnd_1686605 384906239678435059502645 := by
  unfold tailWord_1686605
  simp only [CollatzResearch.WordTrace]
  refine ⟨61515538054725609046341269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41010358703150406030894179 61515538054725609046341269)
  ·
    refine ⟨2883540846315262924047247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61515538054725609046341269 2883540846315262924047247)
    ·
      refine ⟨4325311269472894386070871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2883540846315262924047247 4325311269472894386070871)
      ·
        refine ⟨6487966904209341579106307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4325311269472894386070871 6487966904209341579106307)
        ·
          refine ⟨9731950356314012368659461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6487966904209341579106307 9731950356314012368659461)
          ·
            refine ⟨1824740691808877319123649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9731950356314012368659461 1824740691808877319123649)
            ·
              refine ⟨1368555518856657989342737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1824740691808877319123649 1368555518856657989342737)
              ·
                refine ⟨1026416639142493492007053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1368555518856657989342737 1026416639142493492007053)
                ·
                  refine ⟨384906239678435059502645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026416639142493492007053 384906239678435059502645)
                  ·
                    rfl

theorem cell21_1686605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_1686605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686605 prefixEnd_1686605 := by exact prefixLift 1686605
  have htrace : WordTrace (prefixWord ++ tailWord_1686605) baseStart_1686605 baseEnd_1686605 := by
    simpa [prefixWord, tailWord_1686605, baseEnd_1686605] using wordTrace_append hprefix tailTrace_1686605
  have hstable : (prefixWord ++ tailWord_1686605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686605).length < 2 ^ (prefixWord ++ tailWord_1686605).sum := by decide
  have hdescent : baseEnd_1686605 < baseStart_1686605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686613 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 5]
def baseStart_1686613 : Nat := 118140960795 + 1686613 * 2 ^ 59
def prefixEnd_1686613 : Nat := 4983230072969 + 3 ^ 40 * 1686613 * 2
def baseEnd_1686613 : Nat := 384908065387428823369295

theorem tailTrace_1686613 : CollatzResearch.WordTrace tailWord_1686613 prefixEnd_1686613 384908065387428823369295 := by
  unfold tailWord_1686613
  simp only [CollatzResearch.WordTrace]
  refine ⟨61515829838696626412632493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41010553225797750941754995 61515829838696626412632493)
  ·
    refine ⟨23068436189511234904737185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61515829838696626412632493 23068436189511234904737185)
    ·
      refine ⟨17301327142133426178552889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23068436189511234904737185 17301327142133426178552889)
      ·
        refine ⟨12975995356600069633914667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17301327142133426178552889 12975995356600069633914667)
        ·
          refine ⟨19463993034900104450872001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12975995356600069633914667 19463993034900104450872001)
          ·
            refine ⟨14597994776175078338154001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19463993034900104450872001 14597994776175078338154001)
            ·
              refine ⟨10948496082131308753615501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14597994776175078338154001 10948496082131308753615501)
              ·
                refine ⟨4105686030799240782605813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10948496082131308753615501 4105686030799240782605813)
                ·
                  refine ⟨384908065387428823369295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4105686030799240782605813 384908065387428823369295)
                  ·
                    rfl

theorem cell21_1686613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_1686613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686613 prefixEnd_1686613 := by exact prefixLift 1686613
  have htrace : WordTrace (prefixWord ++ tailWord_1686613) baseStart_1686613 baseEnd_1686613 := by
    simpa [prefixWord, tailWord_1686613, baseEnd_1686613] using wordTrace_append hprefix tailTrace_1686613
  have hstable : (prefixWord ++ tailWord_1686613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686613).length < 2 ^ (prefixWord ++ tailWord_1686613).sum := by decide
  have hdescent : baseEnd_1686613 < baseStart_1686613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686627 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 8]
def baseStart_1686627 : Nat := 118140960795 + 1686627 * 2 ^ 59
def prefixEnd_1686627 : Nat := 4983230072969 + 3 ^ 40 * 1686627 * 2
def baseEnd_1686627 : Nat := 384911260378167910135933

theorem tailTrace_1686627 : CollatzResearch.WordTrace tailWord_1686627 prefixEnd_1686627 384911260378167910135933 := by
  unfold tailWord_1686627
  simp only [CollatzResearch.WordTrace]
  refine ⟨61516340460645906803642135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41010893640430604535761423 61516340460645906803642135)
  ·
    refine ⟨92274510690968860205463203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61516340460645906803642135 92274510690968860205463203)
    ·
      refine ⟨138411766036453290308194805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92274510690968860205463203 138411766036453290308194805)
      ·
        refine ⟨12976103065917495966393263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138411766036453290308194805 12976103065917495966393263)
        ·
          refine ⟨19464154598876243949589895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12976103065917495966393263 19464154598876243949589895)
          ·
            refine ⟨29196231898314365924384843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19464154598876243949589895 29196231898314365924384843)
            ·
              refine ⟨43794347847471548886577265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29196231898314365924384843 43794347847471548886577265)
              ·
                refine ⟨32845760885603661664932949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43794347847471548886577265 32845760885603661664932949)
                ·
                  refine ⟨384911260378167910135933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32845760885603661664932949 384911260378167910135933)
                  ·
                    rfl

theorem cell21_1686627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_1686627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686627 prefixEnd_1686627 := by exact prefixLift 1686627
  have htrace : WordTrace (prefixWord ++ tailWord_1686627) baseStart_1686627 baseEnd_1686627 := by
    simpa [prefixWord, tailWord_1686627, baseEnd_1686627] using wordTrace_append hprefix tailTrace_1686627
  have hstable : (prefixWord ++ tailWord_1686627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686627).length < 2 ^ (prefixWord ++ tailWord_1686627).sum := by decide
  have hdescent : baseEnd_1686627 < baseStart_1686627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686689 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 5]
def baseStart_1686689 : Nat := 118140960795 + 1686689 * 2 ^ 59
def prefixEnd_1686689 : Nat := 4983230072969 + 3 ^ 40 * 1686689 * 2
def baseEnd_1686689 : Nat := 384925409622869580102473

theorem tailTrace_1686689 : CollatzResearch.WordTrace tailWord_1686689 prefixEnd_1686689 384925409622869580102473 := by
  unfold tailWord_1686689
  simp only [CollatzResearch.WordTrace]
  refine ⟨61518601786421291392399121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41012401190947527594932747 61518601786421291392399121)
  ·
    refine ⟨46138951339815968544299341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61518601786421291392399121 46138951339815968544299341)
    ·
      refine ⟨17302106752430988204112253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46138951339815968544299341 17302106752430988204112253)
      ·
        refine ⟨6488290032161620576542095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17302106752430988204112253 6488290032161620576542095)
        ·
          refine ⟨9732435048242430864813143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6488290032161620576542095 9732435048242430864813143)
          ·
            refine ⟨14598652572363646297219715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9732435048242430864813143 14598652572363646297219715)
            ·
              refine ⟨21897978858545469445829573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14598652572363646297219715 21897978858545469445829573)
              ·
                refine ⟨4105871035977275521093045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21897978858545469445829573 4105871035977275521093045)
                ·
                  refine ⟨384925409622869580102473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4105871035977275521093045 384925409622869580102473)
                  ·
                    rfl

theorem cell21_1686689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_1686689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686689 prefixEnd_1686689 := by exact prefixLift 1686689
  have htrace : WordTrace (prefixWord ++ tailWord_1686689) baseStart_1686689 baseEnd_1686689 := by
    simpa [prefixWord, tailWord_1686689, baseEnd_1686689] using wordTrace_append hprefix tailTrace_1686689
  have hstable : (prefixWord ++ tailWord_1686689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686689).length < 2 ^ (prefixWord ++ tailWord_1686689).sum := by decide
  have hdescent : baseEnd_1686689 < baseStart_1686689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686692 : List Nat := [2, 3, 1, 2, 3, 3, 2, 5]
def baseStart_1686692 : Nat := 118140960795 + 1686692 * 2 ^ 59
def prefixEnd_1686692 : Nat := 4983230072969 + 3 ^ 40 * 1686692 * 2
def baseEnd_1686692 : Nat := 128308698087914080517489

theorem tailTrace_1686692 : CollatzResearch.WordTrace tailWord_1686692 prefixEnd_1686692 128308698087914080517489 := by
  unfold tailWord_1686692
  simp only [CollatzResearch.WordTrace]
  refine ⟨30759355602705211452379165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41012474136940281936505553 30759355602705211452379165)
  ·
    refine ⟨11534758351014454294642187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30759355602705211452379165 11534758351014454294642187)
    ·
      refine ⟨17302137526521681441963281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11534758351014454294642187 17302137526521681441963281)
      ·
        refine ⟨12976603144891261081472461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17302137526521681441963281 12976603144891261081472461)
        ·
          refine ⟨4866226179334222905552173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12976603144891261081472461 4866226179334222905552173)
          ·
            refine ⟨1824834817250333589582065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4866226179334222905552173 1824834817250333589582065)
            ·
              refine ⟨1368626112937750192186549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1824834817250333589582065 1368626112937750192186549)
              ·
                refine ⟨128308698087914080517489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1368626112937750192186549 128308698087914080517489)
                ·
                  rfl

theorem cell21_1686692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 5].length) (baseStart_1686692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686692 prefixEnd_1686692 := by exact prefixLift 1686692
  have htrace : WordTrace (prefixWord ++ tailWord_1686692) baseStart_1686692 baseEnd_1686692 := by
    simpa [prefixWord, tailWord_1686692, baseEnd_1686692] using wordTrace_append hprefix tailTrace_1686692
  have hstable : (prefixWord ++ tailWord_1686692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686692).length < 2 ^ (prefixWord ++ tailWord_1686692).sum := by decide
  have hdescent : baseEnd_1686692 < baseStart_1686692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686703 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 6]
def baseStart_1686703 : Nat := 118140960795 + 1686703 * 2 ^ 59
def prefixEnd_1686703 : Nat := 4983230072969 + 3 ^ 40 * 1686703 * 2
def baseEnd_1686703 : Nat := 384928604613608666869111

theorem tailTrace_1686703 : CollatzResearch.WordTrace tailWord_1686703 prefixEnd_1686703 384928604613608666869111 := by
  unfold tailWord_1686703
  simp only [CollatzResearch.WordTrace]
  refine ⟨61519112408370571783408763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41012741605580381188939175 61519112408370571783408763)
  ·
    refine ⟨92278668612555857675113145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61519112408370571783408763 92278668612555857675113145)
    ·
      refine ⟨69209001459416893256334859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92278668612555857675113145 69209001459416893256334859)
      ·
        refine ⟨103813502189125339884502289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69209001459416893256334859 103813502189125339884502289)
        ·
          refine ⟨77860126641844004913376717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103813502189125339884502289 77860126641844004913376717)
          ·
            refine ⟨29197547490691501842516269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77860126641844004913376717 29197547490691501842516269)
            ·
              refine ⟨10949080309009313190943601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29197547490691501842516269 10949080309009313190943601)
              ·
                refine ⟨8211810231756984893207701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10949080309009313190943601 8211810231756984893207701)
                ·
                  refine ⟨384928604613608666869111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8211810231756984893207701 384928604613608666869111)
                  ·
                    rfl

theorem cell21_1686703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_1686703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686703 prefixEnd_1686703 := by exact prefixLift 1686703
  have htrace : WordTrace (prefixWord ++ tailWord_1686703) baseStart_1686703 baseEnd_1686703 := by
    simpa [prefixWord, tailWord_1686703, baseEnd_1686703] using wordTrace_append hprefix tailTrace_1686703
  have hstable : (prefixWord ++ tailWord_1686703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686703).length < 2 ^ (prefixWord ++ tailWord_1686703).sum := by decide
  have hdescent : baseEnd_1686703 < baseStart_1686703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686726 : List Nat := [6, 1, 2, 2, 1, 1, 2, 6]
def baseStart_1686726 : Nat := 118140960795 + 1686726 * 2 ^ 59
def prefixEnd_1686726 : Nat := 4983230072969 + 3 ^ 40 * 1686726 * 2
def baseEnd_1686726 : Nat := 128311284508988579328577

theorem tailTrace_1686726 : CollatzResearch.WordTrace tailWord_1686726 prefixEnd_1686726 128311284508988579328577 := by
  unfold tailWord_1686726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922498477727726459734251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41013300858191497807664021 1922498477727726459734251)
  ·
    refine ⟨2883747716591589689601377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1922498477727726459734251 2883747716591589689601377)
    ·
      refine ⟨2162810787443692267201033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2883747716591589689601377 2162810787443692267201033)
      ·
        refine ⟨1622108090582769200400775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2162810787443692267201033 1622108090582769200400775)
        ·
          refine ⟨2433162135874153800601163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622108090582769200400775 2433162135874153800601163)
          ·
            refine ⟨3649743203811230700901745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433162135874153800601163 3649743203811230700901745)
            ·
              refine ⟨2737307402858423025676309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3649743203811230700901745 2737307402858423025676309)
              ·
                refine ⟨128311284508988579328577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2737307402858423025676309 128311284508988579328577)
                ·
                  rfl

theorem cell21_1686726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_1686726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686726 prefixEnd_1686726 := by exact prefixLift 1686726
  have htrace : WordTrace (prefixWord ++ tailWord_1686726) baseStart_1686726 baseEnd_1686726 := by
    simpa [prefixWord, tailWord_1686726, baseEnd_1686726] using wordTrace_append hprefix tailTrace_1686726
  have hstable : (prefixWord ++ tailWord_1686726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686726).length < 2 ^ (prefixWord ++ tailWord_1686726).sum := by decide
  have hdescent : baseEnd_1686726 < baseStart_1686726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686796 : List Nat := [2, 2, 1, 2, 2, 3, 2, 3, 4]
def baseStart_1686796 : Nat := 118140960795 + 1686796 * 2 ^ 59
def prefixEnd_1686796 : Nat := 4983230072969 + 3 ^ 40 * 1686796 * 2
def baseEnd_1686796 : Nat := 384949828480661171818921

theorem tailTrace_1686796 : CollatzResearch.WordTrace tailWord_1686796 prefixEnd_1686796 384949828480661171818921 := by
  unfold tailWord_1686796
  simp only [CollatzResearch.WordTrace]
  refine ⟨30761252198516824333272121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41015002931355765777696161 30761252198516824333272121)
  ·
    refine ⟨23070939148887618249954091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30761252198516824333272121 23070939148887618249954091)
    ·
      refine ⟨34606408723331427374931137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23070939148887618249954091 34606408723331427374931137)
      ·
        refine ⟨25954806542498570531198353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34606408723331427374931137 25954806542498570531198353)
        ·
          refine ⟨19466104906873927898398765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25954806542498570531198353 19466104906873927898398765)
          ·
            refine ⟨7299789340077722961899537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19466104906873927898398765 7299789340077722961899537)
            ·
              refine ⟨5474842005058292221424653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7299789340077722961899537 5474842005058292221424653)
              ·
                refine ⟨2053065751896859583034245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5474842005058292221424653 2053065751896859583034245)
                ·
                  refine ⟨384949828480661171818921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2053065751896859583034245 384949828480661171818921)
                  ·
                    rfl

theorem cell21_1686796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_1686796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686796 prefixEnd_1686796 := by exact prefixLift 1686796
  have htrace : WordTrace (prefixWord ++ tailWord_1686796) baseStart_1686796 baseEnd_1686796 := by
    simpa [prefixWord, tailWord_1686796, baseEnd_1686796] using wordTrace_append hprefix tailTrace_1686796
  have hstable : (prefixWord ++ tailWord_1686796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686796).length < 2 ^ (prefixWord ++ tailWord_1686796).sum := by decide
  have hdescent : baseEnd_1686796 < baseStart_1686796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686945 : List Nat := [1, 2, 3, 15]
def baseStart_1686945 : Nat := 118140960795 + 1686945 * 2 ^ 59
def prefixEnd_1686945 : Nat := 4983230072969 + 3 ^ 40 * 1686945 * 2
def baseEnd_1686945 : Nat := 1584295606216749069281

theorem tailTrace_1686945 : CollatzResearch.WordTrace tailWord_1686945 prefixEnd_1686945 1584295606216749069281 := by
  unfold tailWord_1686945
  simp only [CollatzResearch.WordTrace]
  refine ⟨61527938873493847113718289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41018625915662564742478859 61527938873493847113718289)
  ·
    refine ⟨46145954155120385335288717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61527938873493847113718289 46145954155120385335288717)
    ·
      refine ⟨17304732808170144500733269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46145954155120385335288717 17304732808170144500733269)
      ·
        refine ⟨1584295606216749069281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 17304732808170144500733269 1584295606216749069281)
        ·
          rfl

theorem cell21_1686945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 15].length) (baseStart_1686945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686945 prefixEnd_1686945 := by exact prefixLift 1686945
  have htrace : WordTrace (prefixWord ++ tailWord_1686945) baseStart_1686945 baseEnd_1686945 := by
    simpa [prefixWord, tailWord_1686945, baseEnd_1686945] using wordTrace_append hprefix tailTrace_1686945
  have hstable : (prefixWord ++ tailWord_1686945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686945).length < 2 ^ (prefixWord ++ tailWord_1686945).sum := by decide
  have hdescent : baseEnd_1686945 < baseStart_1686945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686976 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 7]
def baseStart_1686976 : Nat := 118140960795 + 1686976 * 2 ^ 59
def prefixEnd_1686976 : Nat := 4983230072969 + 3 ^ 40 * 1686976 * 2
def baseEnd_1686976 : Nat := 384990906933020858818553

theorem tailTrace_1686976 : CollatzResearch.WordTrace tailWord_1686976 prefixEnd_1686976 384990906933020858818553 := by
  unfold tailWord_1686976
  simp only [CollatzResearch.WordTrace]
  refine ⟨30764534768190769704048391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41019379690921026272064521 30764534768190769704048391)
  ·
    refine ⟨46146802152286154556072587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30764534768190769704048391 46146802152286154556072587)
    ·
      refine ⟨69220203228429231834108881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46146802152286154556072587 69220203228429231834108881)
      ·
        refine ⟨51915152421321923875581661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69220203228429231834108881 51915152421321923875581661)
        ·
          refine ⟨19468182157995721453343123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51915152421321923875581661 19468182157995721453343123)
          ·
            refine ⟨29202273236993582180014685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19468182157995721453343123 29202273236993582180014685)
            ·
              refine ⟨10950852463872593317505507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29202273236993582180014685 10950852463872593317505507)
              ·
                refine ⟨16426278695808889976258261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10950852463872593317505507 16426278695808889976258261)
                ·
                  refine ⟨384990906933020858818553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16426278695808889976258261 384990906933020858818553)
                  ·
                    rfl

theorem cell21_1686976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_1686976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1686976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1686976 prefixEnd_1686976 := by exact prefixLift 1686976
  have htrace : WordTrace (prefixWord ++ tailWord_1686976) baseStart_1686976 baseEnd_1686976 := by
    simpa [prefixWord, tailWord_1686976, baseEnd_1686976] using wordTrace_append hprefix tailTrace_1686976
  have hstable : (prefixWord ++ tailWord_1686976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686976).length < 2 ^ (prefixWord ++ tailWord_1686976).sum := by decide
  have hdescent : baseEnd_1686976 < baseStart_1686976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687007 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 6]
def baseStart_1687007 : Nat := 118140960795 + 1687007 * 2 ^ 59
def prefixEnd_1687007 : Nat := 4983230072969 + 3 ^ 40 * 1687007 * 2
def baseEnd_1687007 : Nat := 384997981555371693801823

theorem tailTrace_1687007 : CollatzResearch.WordTrace tailWord_1687007 prefixEnd_1687007 384997981555371693801823 := by
  unfold tailWord_1687007
  simp only [CollatzResearch.WordTrace]
  refine ⟨61530200199269231702475275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41020133466179487801650183 61530200199269231702475275)
  ·
    refine ⟨92295300298903847553712913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61530200199269231702475275 92295300298903847553712913)
    ·
      refine ⟨69221475224177885665284685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92295300298903847553712913 69221475224177885665284685)
      ·
        refine ⟨25958053209066707124481757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69221475224177885665284685 25958053209066707124481757)
        ·
          refine ⟨9734269953400015171680659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25958053209066707124481757 9734269953400015171680659)
          ·
            refine ⟨14601404930100022757520989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9734269953400015171680659 14601404930100022757520989)
            ·
              refine ⟨5475526848787508534070371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14601404930100022757520989 5475526848787508534070371)
              ·
                refine ⟨8213290273181262801105557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5475526848787508534070371 8213290273181262801105557)
                ·
                  refine ⟨384997981555371693801823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8213290273181262801105557 384997981555371693801823)
                  ·
                    rfl

theorem cell21_1687007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 6].length) (baseStart_1687007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687007 prefixEnd_1687007 := by exact prefixLift 1687007
  have htrace : WordTrace (prefixWord ++ tailWord_1687007) baseStart_1687007 baseEnd_1687007 := by
    simpa [prefixWord, tailWord_1687007, baseEnd_1687007] using wordTrace_append hprefix tailTrace_1687007
  have hstable : (prefixWord ++ tailWord_1687007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687007).length < 2 ^ (prefixWord ++ tailWord_1687007).sum := by decide
  have hdescent : baseEnd_1687007 < baseStart_1687007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687044 : List Nat := [2, 3, 2, 3, 2, 2, 1, 3, 3]
def baseStart_1687044 : Nat := 118140960795 + 1687044 * 2 ^ 59
def prefixEnd_1687044 : Nat := 4983230072969 + 3 ^ 40 * 1687044 * 2
def baseEnd_1687044 : Nat := 385006425459467851685081

theorem tailTrace_1687044 : CollatzResearch.WordTrace tailWord_1687044 prefixEnd_1687044 385006425459467851685081 := by
  unfold tailWord_1687044
  simp only [CollatzResearch.WordTrace]
  refine ⟨30765774850067593510786093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41021033133423458014381457 30765774850067593510786093)
  ·
    refine ⟨11537165568775347566544785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30765774850067593510786093 11537165568775347566544785)
    ·
      refine ⟨8652874176581510674908589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11537165568775347566544785 8652874176581510674908589)
      ·
        refine ⟨3244827816218066503090721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8652874176581510674908589 3244827816218066503090721)
        ·
          refine ⟨2433620862163549877318041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3244827816218066503090721 2433620862163549877318041)
          ·
            refine ⟨1825215646622662407988531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2433620862163549877318041 1825215646622662407988531)
            ·
              refine ⟨2737823469933993611982797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825215646622662407988531 2737823469933993611982797)
              ·
                refine ⟨1026683801225247604493549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2737823469933993611982797 1026683801225247604493549)
                ·
                  refine ⟨385006425459467851685081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026683801225247604493549 385006425459467851685081)
                  ·
                    rfl

theorem cell21_1687044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_1687044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687044 prefixEnd_1687044 := by exact prefixLift 1687044
  have htrace : WordTrace (prefixWord ++ tailWord_1687044) baseStart_1687044 baseEnd_1687044 := by
    simpa [prefixWord, tailWord_1687044, baseEnd_1687044] using wordTrace_append hprefix tailTrace_1687044
  have hstable : (prefixWord ++ tailWord_1687044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687044).length < 2 ^ (prefixWord ++ tailWord_1687044).sum := by decide
  have hdescent : baseEnd_1687044 < baseStart_1687044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687128 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 5]
def baseStart_1687128 : Nat := 118140960795 + 1687128 * 2 ^ 59
def prefixEnd_1687128 : Nat := 4983230072969 + 3 ^ 40 * 1687128 * 2
def baseEnd_1687128 : Nat := 385025595403902372284909

theorem tailTrace_1687128 : CollatzResearch.WordTrace tailWord_1687128 prefixEnd_1687128 385025595403902372284909 := by
  unfold tailWord_1687128
  simp only [CollatzResearch.WordTrace]
  refine ⟨30767306715915434683815019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41023075621220579578420025 30767306715915434683815019)
  ·
    refine ⟨46150960073873152025722529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30767306715915434683815019 46150960073873152025722529)
    ·
      refine ⟨34613220055404864019291897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46150960073873152025722529 34613220055404864019291897)
      ·
        refine ⟨25959915041553648014468923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34613220055404864019291897 25959915041553648014468923)
        ·
          refine ⟨38939872562330472021703385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25959915041553648014468923 38939872562330472021703385)
          ·
            refine ⟨29204904421747854016277539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38939872562330472021703385 29204904421747854016277539)
            ·
              refine ⟨43807356632621781024416309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29204904421747854016277539 43807356632621781024416309)
              ·
                refine ⟨4106939684308291971039029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43807356632621781024416309 4106939684308291971039029)
                ·
                  refine ⟨385025595403902372284909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4106939684308291971039029 385025595403902372284909)
                  ·
                    rfl

theorem cell21_1687128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_1687128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687128 prefixEnd_1687128 := by exact prefixLift 1687128
  have htrace : WordTrace (prefixWord ++ tailWord_1687128) baseStart_1687128 baseEnd_1687128 := by
    simpa [prefixWord, tailWord_1687128, baseEnd_1687128] using wordTrace_append hprefix tailTrace_1687128
  have hstable : (prefixWord ++ tailWord_1687128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687128).length < 2 ^ (prefixWord ++ tailWord_1687128).sum := by decide
  have hdescent : baseEnd_1687128 < baseStart_1687128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687173 : List Nat := [1, 3, 1, 1, 4, 1, 10]
def baseStart_1687173 : Nat := 118140960795 + 1687173 * 2 ^ 59
def prefixEnd_1687173 : Nat := 4983230072969 + 3 ^ 40 * 1687173 * 2
def baseEnd_1687173 : Nat := 42781762779665810448313

theorem tailTrace_1687173 : CollatzResearch.WordTrace tailWord_1687173 prefixEnd_1687173 42781762779665810448313 := by
  unfold tailWord_1687173
  simp only [CollatzResearch.WordTrace]
  refine ⟨61536254716667842053018173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41024169811111894702012115 61536254716667842053018173)
  ·
    refine ⟨23076095518750440769881815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61536254716667842053018173 23076095518750440769881815)
    ·
      refine ⟨34614143278125661154822723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23076095518750440769881815 34614143278125661154822723)
      ·
        refine ⟨51921214917188491732234085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34614143278125661154822723 51921214917188491732234085)
        ·
          refine ⟨9735227796972842199793891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51921214917188491732234085 9735227796972842199793891)
          ·
            refine ⟨14602841695459263299690837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9735227796972842199793891 14602841695459263299690837)
            ·
              refine ⟨42781762779665810448313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14602841695459263299690837 42781762779665810448313)
              ·
                rfl

theorem cell21_1687173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 10].length) (baseStart_1687173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687173 prefixEnd_1687173 := by exact prefixLift 1687173
  have htrace : WordTrace (prefixWord ++ tailWord_1687173) baseStart_1687173 baseEnd_1687173 := by
    simpa [prefixWord, tailWord_1687173, baseEnd_1687173] using wordTrace_append hprefix tailTrace_1687173
  have hstable : (prefixWord ++ tailWord_1687173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687173).length < 2 ^ (prefixWord ++ tailWord_1687173).sum := by decide
  have hdescent : baseEnd_1687173 < baseStart_1687173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687249 : List Nat := [1, 2, 2, 1, 2, 4, 1, 8]
def baseStart_1687249 : Nat := 118140960795 + 1687249 * 2 ^ 59
def prefixEnd_1687249 : Nat := 4983230072969 + 3 ^ 40 * 1687249 * 2
def baseEnd_1687249 : Nat := 128351069750811016922665

theorem tailTrace_1687249 : CollatzResearch.WordTrace tailWord_1687249 prefixEnd_1687249 128351069750811016922665 := by
  unfold tailWord_1687249
  simp only [CollatzResearch.WordTrace]
  refine ⟨61539026664392507032784801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41026017776261671355189867 61539026664392507032784801)
  ·
    refine ⟨46154269998294380274588601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61539026664392507032784801 46154269998294380274588601)
    ·
      refine ⟨34615702498720785205941451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46154269998294380274588601 34615702498720785205941451)
      ·
        refine ⟨51923553748081177808912177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34615702498720785205941451 51923553748081177808912177)
        ·
          refine ⟨38942665311060883356684133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51923553748081177808912177 38942665311060883356684133)
          ·
            refine ⟨7301749745823915629378275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38942665311060883356684133 7301749745823915629378275)
            ·
              refine ⟨10952624618735873444067413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7301749745823915629378275 10952624618735873444067413)
              ·
                refine ⟨128351069750811016922665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10952624618735873444067413 128351069750811016922665)
                ·
                  rfl

theorem cell21_1687249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 8].length) (baseStart_1687249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687249 prefixEnd_1687249 := by exact prefixLift 1687249
  have htrace : WordTrace (prefixWord ++ tailWord_1687249) baseStart_1687249 baseEnd_1687249 := by
    simpa [prefixWord, tailWord_1687249, baseEnd_1687249] using wordTrace_append hprefix tailTrace_1687249
  have hstable : (prefixWord ++ tailWord_1687249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687249).length < 2 ^ (prefixWord ++ tailWord_1687249).sum := by decide
  have hdescent : baseEnd_1687249 < baseStart_1687249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687314 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_1687314 : Nat := 118140960795 + 1687314 * 2 ^ 59
def prefixEnd_1687314 : Nat := 4983230072969 + 3 ^ 40 * 1687314 * 2
def baseEnd_1687314 : Nat := 385068043138007382184529

theorem tailTrace_1687314 : CollatzResearch.WordTrace tailWord_1687314 prefixEnd_1687314 385068043138007382184529 := by
  unfold tailWord_1687314
  simp only [CollatzResearch.WordTrace]
  refine ⟨15385349352289255783475249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41027598272771348755933997 15385349352289255783475249)
  ·
    refine ⟨11539012014216941837606437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15385349352289255783475249 11539012014216941837606437)
    ·
      refine ⟨2163564752665676594551207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11539012014216941837606437 2163564752665676594551207)
      ·
        refine ⟨3245347128998514891826811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2163564752665676594551207 3245347128998514891826811)
        ·
          refine ⟨4868020693497772337740217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3245347128998514891826811 4868020693497772337740217)
          ·
            refine ⟨3651015520123329253305163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4868020693497772337740217 3651015520123329253305163)
            ·
              refine ⟨5476523280184993879957745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3651015520123329253305163 5476523280184993879957745)
              ·
                refine ⟨4107392460138745409968309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5476523280184993879957745 4107392460138745409968309)
                ·
                  refine ⟨385068043138007382184529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4107392460138745409968309 385068043138007382184529)
                  ·
                    rfl

theorem cell21_1687314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_1687314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687314 prefixEnd_1687314 := by exact prefixLift 1687314
  have htrace : WordTrace (prefixWord ++ tailWord_1687314) baseStart_1687314 baseEnd_1687314 := by
    simpa [prefixWord, tailWord_1687314, baseEnd_1687314] using wordTrace_append hprefix tailTrace_1687314
  have hstable : (prefixWord ++ tailWord_1687314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687314).length < 2 ^ (prefixWord ++ tailWord_1687314).sum := by decide
  have hdescent : baseEnd_1687314 < baseStart_1687314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687356 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 5]
def baseStart_1687356 : Nat := 118140960795 + 1687356 * 2 ^ 59
def prefixEnd_1687356 : Nat := 4983230072969 + 3 ^ 40 * 1687356 * 2
def baseEnd_1687356 : Nat := 385077628110224642484443

theorem tailTrace_1687356 : CollatzResearch.WordTrace tailWord_1687356 prefixEnd_1687356 385077628110224642484443 := by
  unfold tailWord_1687356
  simp only [CollatzResearch.WordTrace]
  refine ⟨30771464637502432153464961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41028619516669909537953281 30771464637502432153464961)
  ·
    refine ⟨23078598478126824115098721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30771464637502432153464961 23078598478126824115098721)
    ·
      refine ⟨17308948858595118086324041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23078598478126824115098721 17308948858595118086324041)
      ·
        refine ⟨12981711643946338564743031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17308948858595118086324041 12981711643946338564743031)
        ·
          refine ⟨19472567465919507847114547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12981711643946338564743031 19472567465919507847114547)
          ·
            refine ⟨29208851198879261770671821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19472567465919507847114547 29208851198879261770671821)
            ·
              refine ⟨10953319199579723164001933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29208851198879261770671821 10953319199579723164001933)
              ·
                refine ⟨4107494699842396186500725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10953319199579723164001933 4107494699842396186500725)
                ·
                  refine ⟨385077628110224642484443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4107494699842396186500725 385077628110224642484443)
                  ·
                    rfl

theorem cell21_1687356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_1687356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687356 prefixEnd_1687356 := by exact prefixLift 1687356
  have htrace : WordTrace (prefixWord ++ tailWord_1687356) baseStart_1687356 baseEnd_1687356 := by
    simpa [prefixWord, tailWord_1687356, baseEnd_1687356] using wordTrace_append hprefix tailTrace_1687356
  have hstable : (prefixWord ++ tailWord_1687356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687356).length < 2 ^ (prefixWord ++ tailWord_1687356).sum := by decide
  have hdescent : baseEnd_1687356 < baseStart_1687356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687508 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1687508 : Nat := 118140960795 + 1687508 * 2 ^ 59
def prefixEnd_1687508 : Nat := 4983230072969 + 3 ^ 40 * 1687508 * 2
def baseEnd_1687508 : Nat := 385112316581106155950799

theorem tailTrace_1687508 : CollatzResearch.WordTrace tailWord_1687508 prefixEnd_1687508 385112316581106155950799 := by
  unfold tailWord_1687508
  simp only [CollatzResearch.WordTrace]
  refine ⟨30774236585227097133231589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41032315446969462844308785 30774236585227097133231589)
  ·
    refine ⟨5770169359730080712480923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30774236585227097133231589 5770169359730080712480923)
    ·
      refine ⟨8655254039595121068721385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5770169359730080712480923 8655254039595121068721385)
      ·
        refine ⟨6491440529696340801541039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8655254039595121068721385 6491440529696340801541039)
        ·
          refine ⟨9737160794544511202311559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6491440529696340801541039 9737160794544511202311559)
          ·
            refine ⟨14605741191816766803467339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9737160794544511202311559 14605741191816766803467339)
            ·
              refine ⟨21908611787725150205201009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14605741191816766803467339 21908611787725150205201009)
              ·
                refine ⟨16431458840793862653900757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21908611787725150205201009 16431458840793862653900757)
                ·
                  refine ⟨385112316581106155950799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16431458840793862653900757 385112316581106155950799)
                  ·
                    rfl

theorem cell21_1687508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1687508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687508 prefixEnd_1687508 := by exact prefixLift 1687508
  have htrace : WordTrace (prefixWord ++ tailWord_1687508) baseStart_1687508 baseEnd_1687508 := by
    simpa [prefixWord, tailWord_1687508, baseEnd_1687508] using wordTrace_append hprefix tailTrace_1687508
  have hstable : (prefixWord ++ tailWord_1687508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687508).length < 2 ^ (prefixWord ++ tailWord_1687508).sum := by decide
  have hdescent : baseEnd_1687508 < baseStart_1687508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687553 : List Nat := [1, 2, 4, 1, 2, 1, 3, 7]
def baseStart_1687553 : Nat := 118140960795 + 1687553 * 2 ^ 59
def prefixEnd_1687553 : Nat := 4983230072969 + 3 ^ 40 * 1687553 * 2
def baseEnd_1687553 : Nat := 128374195398065359233569

theorem tailTrace_1687553 : CollatzResearch.WordTrace tailWord_1687553 prefixEnd_1687553 128374195398065359233569 := by
  unfold tailWord_1687553
  simp only [CollatzResearch.WordTrace]
  refine ⟨61550114455291166951851313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41033409636860777967900875 61550114455291166951851313)
  ·
    refine ⟨46162585841468375213888485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61550114455291166951851313 46162585841468375213888485)
    ·
      refine ⟨8655484845275320352604091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46162585841468375213888485 8655484845275320352604091)
      ·
        refine ⟨12983227267912980528906137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8655484845275320352604091 12983227267912980528906137)
        ·
          refine ⟨9737420450934735396679603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12983227267912980528906137 9737420450934735396679603)
          ·
            refine ⟨14606130676402103095019405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9737420450934735396679603 14606130676402103095019405)
            ·
              refine ⟨5477299003650788660632277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14606130676402103095019405 5477299003650788660632277)
              ·
                refine ⟨128374195398065359233569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5477299003650788660632277 128374195398065359233569)
                ·
                  rfl

theorem cell21_1687553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 7].length) (baseStart_1687553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687553 prefixEnd_1687553 := by exact prefixLift 1687553
  have htrace : WordTrace (prefixWord ++ tailWord_1687553) baseStart_1687553 baseEnd_1687553 := by
    simpa [prefixWord, tailWord_1687553, baseEnd_1687553] using wordTrace_append hprefix tailTrace_1687553
  have hstable : (prefixWord ++ tailWord_1687553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687553).length < 2 ^ (prefixWord ++ tailWord_1687553).sum := by decide
  have hdescent : baseEnd_1687553 < baseStart_1687553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687660 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 5]
def baseStart_1687660 : Nat := 118140960795 + 1687660 * 2 ^ 59
def prefixEnd_1687660 : Nat := 4983230072969 + 3 ^ 40 * 1687660 * 2
def baseEnd_1687660 : Nat := 385147005051987669417155

theorem tailTrace_1687660 : CollatzResearch.WordTrace tailWord_1687660 prefixEnd_1687660 385147005051987669417155 := by
  unfold tailWord_1687660
  simp only [CollatzResearch.WordTrace]
  refine ⟨30777008532951762112998217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41036011377269016150664289 30777008532951762112998217)
  ·
    refine ⟨23082756399713821584748663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30777008532951762112998217 23082756399713821584748663)
    ·
      refine ⟨34624134599570732377122995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23082756399713821584748663 34624134599570732377122995)
      ·
        refine ⟨51936201899356098565684493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34624134599570732377122995 51936201899356098565684493)
        ·
          refine ⟨19476075712258536962131685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51936201899356098565684493 19476075712258536962131685)
          ·
            refine ⟨3651764196048475680399691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19476075712258536962131685 3651764196048475680399691)
            ·
              refine ⟨5477646294072713520599537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3651764196048475680399691 5477646294072713520599537)
              ·
                refine ⟨4108234720554535140449653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5477646294072713520599537 4108234720554535140449653)
                ·
                  refine ⟨385147005051987669417155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4108234720554535140449653 385147005051987669417155)
                  ·
                    rfl

theorem cell21_1687660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_1687660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687660 prefixEnd_1687660 := by exact prefixLift 1687660
  have htrace : WordTrace (prefixWord ++ tailWord_1687660) baseStart_1687660 baseEnd_1687660 := by
    simpa [prefixWord, tailWord_1687660, baseEnd_1687660] using wordTrace_append hprefix tailTrace_1687660
  have hstable : (prefixWord ++ tailWord_1687660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687660).length < 2 ^ (prefixWord ++ tailWord_1687660).sum := by decide
  have hdescent : baseEnd_1687660 < baseStart_1687660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687677 : List Nat := [1, 4, 1, 1, 3, 2, 1, 5, 3]
def baseStart_1687677 : Nat := 118140960795 + 1687677 * 2 ^ 59
def prefixEnd_1687677 : Nat := 4983230072969 + 3 ^ 40 * 1687677 * 2
def baseEnd_1687677 : Nat := 385150884683599417633787

theorem tailTrace_1687677 : CollatzResearch.WordTrace tailWord_1687677 prefixEnd_1687677 385150884683599417633787 := by
  unfold tailWord_1687677
  simp only [CollatzResearch.WordTrace]
  refine ⟨61554637106841936129365285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41036424737894624086243523 61554637106841936129365285)
  ·
    refine ⟨11541494457532863024255991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61554637106841936129365285 11541494457532863024255991)
    ·
      refine ⟨17312241686299294536383987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11541494457532863024255991 17312241686299294536383987)
      ·
        refine ⟨25968362529448941804575981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17312241686299294536383987 25968362529448941804575981)
        ·
          refine ⟨9738135948543353176715993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25968362529448941804575981 9738135948543353176715993)
          ·
            refine ⟨7303601961407514882536995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9738135948543353176715993 7303601961407514882536995)
            ·
              refine ⟨10955402942111272323805493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7303601961407514882536995 10955402942111272323805493)
              ·
                refine ⟨1027069025822931780356765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10955402942111272323805493 1027069025822931780356765)
                ·
                  refine ⟨385150884683599417633787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1027069025822931780356765 385150884683599417633787)
                  ·
                    rfl

theorem cell21_1687677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_1687677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687677 prefixEnd_1687677 := by exact prefixLift 1687677
  have htrace : WordTrace (prefixWord ++ tailWord_1687677) baseStart_1687677 baseEnd_1687677 := by
    simpa [prefixWord, tailWord_1687677, baseEnd_1687677] using wordTrace_append hprefix tailTrace_1687677
  have hstable : (prefixWord ++ tailWord_1687677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687677).length < 2 ^ (prefixWord ++ tailWord_1687677).sum := by decide
  have hdescent : baseEnd_1687677 < baseStart_1687677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687708 : List Nat := [2, 2, 3, 2, 1, 1, 5, 1, 4]
def baseStart_1687708 : Nat := 118140960795 + 1687708 * 2 ^ 59
def prefixEnd_1687708 : Nat := 4983230072969 + 3 ^ 40 * 1687708 * 2
def baseEnd_1687708 : Nat := 385157959305950252617057

theorem tailTrace_1687708 : CollatzResearch.WordTrace tailWord_1687708 prefixEnd_1687708 385157959305950252617057 := by
  unfold tailWord_1687708
  simp only [CollatzResearch.WordTrace]
  refine ⟨30777883884864814211871889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41037178513153085615829185 30777883884864814211871889)
  ·
    refine ⟨23083412913648610658903917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30777883884864814211871889 23083412913648610658903917)
    ·
      refine ⟨8656279842618228997088969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23083412913648610658903917 8656279842618228997088969)
      ·
        refine ⟨6492209881963671747816727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8656279842618228997088969 6492209881963671747816727)
        ·
          refine ⟨9738314822945507621725091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6492209881963671747816727 9738314822945507621725091)
          ·
            refine ⟨14607472234418261432587637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9738314822945507621725091 14607472234418261432587637)
            ·
              refine ⟨1369450521976712009305091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14607472234418261432587637 1369450521976712009305091)
              ·
                refine ⟨2054175782965068013957637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369450521976712009305091 2054175782965068013957637)
                ·
                  refine ⟨385157959305950252617057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2054175782965068013957637 385157959305950252617057)
                  ·
                    rfl

theorem cell21_1687708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_1687708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687708 prefixEnd_1687708 := by exact prefixLift 1687708
  have htrace : WordTrace (prefixWord ++ tailWord_1687708) baseStart_1687708 baseEnd_1687708 := by
    simpa [prefixWord, tailWord_1687708, baseEnd_1687708] using wordTrace_append hprefix tailTrace_1687708
  have hstable : (prefixWord ++ tailWord_1687708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687708).length < 2 ^ (prefixWord ++ tailWord_1687708).sum := by decide
  have hdescent : baseEnd_1687708 < baseStart_1687708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687781 : List Nat := [1, 3, 1, 4, 2, 1, 2, 7]
def baseStart_1687781 : Nat := 118140960795 + 1687781 * 2 ^ 59
def prefixEnd_1687781 : Nat := 4983230072969 + 3 ^ 40 * 1687781 * 2
def baseEnd_1687781 : Nat := 128391539633506115966747

theorem tailTrace_1687781 : CollatzResearch.WordTrace tailWord_1687781 prefixEnd_1687781 128391539633506115966747 := by
  unfold tailWord_1687781
  simp only [CollatzResearch.WordTrace]
  refine ⟨61558430298465161891151197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41038953532310107927434131 61558430298465161891151197)
  ·
    refine ⟨23084411361924435709181699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61558430298465161891151197 23084411361924435709181699)
    ·
      refine ⟨34626617042886653563772549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23084411361924435709181699 34626617042886653563772549)
      ·
        refine ⟨6492490695541247543207353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34626617042886653563772549 6492490695541247543207353)
        ·
          refine ⟨4869368021655935657405515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6492490695541247543207353 4869368021655935657405515)
          ·
            refine ⟨7304052032483903486108273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4869368021655935657405515 7304052032483903486108273)
            ·
              refine ⟨5478039024362927614581205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7304052032483903486108273 5478039024362927614581205)
              ·
                refine ⟨128391539633506115966747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5478039024362927614581205 128391539633506115966747)
                ·
                  rfl

theorem cell21_1687781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 7].length) (baseStart_1687781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687781 prefixEnd_1687781 := by exact prefixLift 1687781
  have htrace : WordTrace (prefixWord ++ tailWord_1687781) baseStart_1687781 baseEnd_1687781 := by
    simpa [prefixWord, tailWord_1687781, baseEnd_1687781] using wordTrace_append hprefix tailTrace_1687781
  have hstable : (prefixWord ++ tailWord_1687781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687781).length < 2 ^ (prefixWord ++ tailWord_1687781).sum := by decide
  have hdescent : baseEnd_1687781 < baseStart_1687781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687815 : List Nat := [1, 1, 4, 5, 1, 2, 1, 6]
def baseStart_1687815 : Nat := 118140960795 + 1687815 * 2 ^ 59
def prefixEnd_1687815 : Nat := 4983230072969 + 3 ^ 40 * 1687815 * 2
def baseEnd_1687815 : Nat := 128394126054580614777835

theorem tailTrace_1687815 : CollatzResearch.WordTrace tailWord_1687815 prefixEnd_1687815 128394126054580614777835 := by
  unfold tailWord_1687815
  simp only [CollatzResearch.WordTrace]
  refine ⟨61559670380341985697888899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41039780253561323798592599 61559670380341985697888899)
  ·
    refine ⟨92339505570512978546833349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61559670380341985697888899 92339505570512978546833349)
    ·
      refine ⟨17313657294471183477531253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92339505570512978546833349 17313657294471183477531253)
      ·
        refine ⟨1623155371356673451018555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17313657294471183477531253 1623155371356673451018555)
        ·
          refine ⟨2434733057035010176527833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623155371356673451018555 2434733057035010176527833)
          ·
            refine ⟨1826049792776257632395875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2434733057035010176527833 1826049792776257632395875)
            ·
              refine ⟨2739074689164386448593813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826049792776257632395875 2739074689164386448593813)
              ·
                refine ⟨128394126054580614777835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2739074689164386448593813 128394126054580614777835)
                ·
                  rfl

theorem cell21_1687815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 6].length) (baseStart_1687815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687815 prefixEnd_1687815 := by exact prefixLift 1687815
  have htrace : WordTrace (prefixWord ++ tailWord_1687815) baseStart_1687815 baseEnd_1687815 := by
    simpa [prefixWord, tailWord_1687815, baseEnd_1687815] using wordTrace_append hprefix tailTrace_1687815
  have hstable : (prefixWord ++ tailWord_1687815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687815).length < 2 ^ (prefixWord ++ tailWord_1687815).sum := by decide
  have hdescent : baseEnd_1687815 < baseStart_1687815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687857 : List Nat := [1, 2, 2, 3, 4, 1, 8]
def baseStart_1687857 : Nat := 118140960795 + 1687857 * 2 ^ 59
def prefixEnd_1687857 : Nat := 4983230072969 + 3 ^ 40 * 1687857 * 2
def baseEnd_1687857 : Nat := 42799107015106567181491

theorem tailTrace_1687857 : CollatzResearch.WordTrace tailWord_1687857 prefixEnd_1687857 42799107015106567181491 := by
  unfold tailWord_1687857
  simp only [CollatzResearch.WordTrace]
  refine ⟨61561202246189826870917825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41040801497459884580611883 61561202246189826870917825)
  ·
    refine ⟨46170901684642370153188369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61561202246189826870917825 46170901684642370153188369)
    ·
      refine ⟨34628176263481777614891277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46170901684642370153188369 34628176263481777614891277)
      ·
        refine ⟨12985566098805666605584229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34628176263481777614891277 12985566098805666605584229)
        ·
          refine ⟨2434793643526062488547043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12985566098805666605584229 2434793643526062488547043)
          ·
            refine ⟨3652190465289093732820565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2434793643526062488547043 3652190465289093732820565)
            ·
              refine ⟨42799107015106567181491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3652190465289093732820565 42799107015106567181491)
              ·
                rfl

theorem cell21_1687857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 8].length) (baseStart_1687857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687857 prefixEnd_1687857 := by exact prefixLift 1687857
  have htrace : WordTrace (prefixWord ++ tailWord_1687857) baseStart_1687857 baseEnd_1687857 := by
    simpa [prefixWord, tailWord_1687857, baseEnd_1687857] using wordTrace_append hprefix tailTrace_1687857
  have hstable : (prefixWord ++ tailWord_1687857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687857).length < 2 ^ (prefixWord ++ tailWord_1687857).sum := by decide
  have hdescent : baseEnd_1687857 < baseStart_1687857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687860 : List Nat := [2, 5, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1687860 : Nat := 118140960795 + 1687860 * 2 ^ 59
def prefixEnd_1687860 : Nat := 4983230072969 + 3 ^ 40 * 1687860 * 2
def baseEnd_1687860 : Nat := 385192647776831766083413

theorem tailTrace_1687860 : CollatzResearch.WordTrace tailWord_1687860 prefixEnd_1687860 385192647776831766083413 := by
  unfold tailWord_1687860
  simp only [CollatzResearch.WordTrace]
  refine ⟨30780655832589479191638517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41040874443452638922184689 30780655832589479191638517)
  ·
    refine ⟨2885686484305263674216111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30780655832589479191638517 2885686484305263674216111)
    ·
      refine ⟨4328529726457895511324167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2885686484305263674216111 4328529726457895511324167)
      ·
        refine ⟨6492794589686843266986251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4328529726457895511324167 6492794589686843266986251)
        ·
          refine ⟨9739191884530264900479377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6492794589686843266986251 9739191884530264900479377)
          ·
            refine ⟨7304393913397698675359533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9739191884530264900479377 7304393913397698675359533)
            ·
              refine ⟨2739147717524137003259825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7304393913397698675359533 2739147717524137003259825)
              ·
                refine ⟨2054360788143102752444869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2739147717524137003259825 2054360788143102752444869)
                ·
                  refine ⟨385192647776831766083413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2054360788143102752444869 385192647776831766083413)
                  ·
                    rfl

theorem cell21_1687860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1687860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687860 prefixEnd_1687860 := by exact prefixLift 1687860
  have htrace : WordTrace (prefixWord ++ tailWord_1687860) baseStart_1687860 baseEnd_1687860 := by
    simpa [prefixWord, tailWord_1687860, baseEnd_1687860] using wordTrace_append hprefix tailTrace_1687860
  have hstable : (prefixWord ++ tailWord_1687860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687860).length < 2 ^ (prefixWord ++ tailWord_1687860).sum := by decide
  have hdescent : baseEnd_1687860 < baseStart_1687860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687922 : List Nat := [3, 2, 1, 2, 1, 4, 3, 2, 3]
def baseStart_1687922 : Nat := 118140960795 + 1687922 * 2 ^ 59
def prefixEnd_1687922 : Nat := 4983230072969 + 3 ^ 40 * 1687922 * 2
def baseEnd_1687922 : Nat := 385206797021533436049953

theorem tailTrace_1687922 : CollatzResearch.WordTrace tailWord_1687922 prefixEnd_1687922 385206797021533436049953 := by
  unfold tailWord_1687922
  simp only [CollatzResearch.WordTrace]
  refine ⟨15390893247738585743008505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41042381993969561981356013 15390893247738585743008505)
  ·
    refine ⟨11543169935803939307256379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15390893247738585743008505 11543169935803939307256379)
    ·
      refine ⟨17314754903705908960884569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11543169935803939307256379 17314754903705908960884569)
      ·
        refine ⟨12986066177779431720663427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17314754903705908960884569 12986066177779431720663427)
        ·
          refine ⟨19479099266669147580995141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12986066177779431720663427 19479099266669147580995141)
          ·
            refine ⟨3652331112500465171436589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19479099266669147580995141 3652331112500465171436589)
            ·
              refine ⟨1369624167187674439288721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3652331112500465171436589 1369624167187674439288721)
              ·
                refine ⟨1027218125390755829466541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1369624167187674439288721 1027218125390755829466541)
                ·
                  refine ⟨385206797021533436049953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1027218125390755829466541 385206797021533436049953)
                  ·
                    rfl

theorem cell21_1687922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_1687922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687922 prefixEnd_1687922 := by exact prefixLift 1687922
  have htrace : WordTrace (prefixWord ++ tailWord_1687922) baseStart_1687922 baseEnd_1687922 := by
    simpa [prefixWord, tailWord_1687922, baseEnd_1687922] using wordTrace_append hprefix tailTrace_1687922
  have hstable : (prefixWord ++ tailWord_1687922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687922).length < 2 ^ (prefixWord ++ tailWord_1687922).sum := by decide
  have hdescent : baseEnd_1687922 < baseStart_1687922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687933 : List Nat := [1, 4, 1, 1, 2, 4, 2, 6]
def baseStart_1687933 : Nat := 118140960795 + 1687933 * 2 ^ 59
def prefixEnd_1687933 : Nat := 4983230072969 + 3 ^ 40 * 1687933 * 2
def baseEnd_1687933 : Nat := 128403102457133287122199

theorem tailTrace_1687933 : CollatzResearch.WordTrace tailWord_1687933 prefixEnd_1687933 128403102457133287122199 := by
  unfold tailWord_1687933
  simp only [CollatzResearch.WordTrace]
  refine ⟨61563974193914491850684453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41042649462609661233789635 61563974193914491850684453)
  ·
    refine ⟨11543245161358967222003335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61563974193914491850684453 11543245161358967222003335)
    ·
      refine ⟨17314867742038450833005003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11543245161358967222003335 17314867742038450833005003)
      ·
        refine ⟨25972301613057676249507505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17314867742038450833005003 25972301613057676249507505)
        ·
          refine ⟨19479226209793257187130629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25972301613057676249507505 19479226209793257187130629)
          ·
            refine ⟨3652354914336235722586993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19479226209793257187130629 3652354914336235722586993)
            ·
              refine ⟨2739266185752176791940245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3652354914336235722586993 2739266185752176791940245)
              ·
                refine ⟨128403102457133287122199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2739266185752176791940245 128403102457133287122199)
                ·
                  rfl

theorem cell21_1687933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 6].length) (baseStart_1687933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1687933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1687933 prefixEnd_1687933 := by exact prefixLift 1687933
  have htrace : WordTrace (prefixWord ++ tailWord_1687933) baseStart_1687933 baseEnd_1687933 := by
    simpa [prefixWord, tailWord_1687933, baseEnd_1687933] using wordTrace_append hprefix tailTrace_1687933
  have hstable : (prefixWord ++ tailWord_1687933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687933).length < 2 ^ (prefixWord ++ tailWord_1687933).sum := by decide
  have hdescent : baseEnd_1687933 < baseStart_1687933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688040 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 5]
def baseStart_1688040 : Nat := 118140960795 + 1688040 * 2 ^ 59
def prefixEnd_1688040 : Nat := 4983230072969 + 3 ^ 40 * 1688040 * 2
def baseEnd_1688040 : Nat := 385233726229191453083045

theorem tailTrace_1688040 : CollatzResearch.WordTrace tailWord_1688040 prefixEnd_1688040 385233726229191453083045 := by
  unfold tailWord_1688040
  simp only [CollatzResearch.WordTrace]
  refine ⟨30783938402263424562414787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41045251203017899416553049 30783938402263424562414787)
  ·
    refine ⟨46175907603395136843622181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30783938402263424562414787 46175907603395136843622181)
    ·
      refine ⟨8657982675636588158179159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46175907603395136843622181 8657982675636588158179159)
      ·
        refine ⟨12986974013454882237268739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8657982675636588158179159 12986974013454882237268739)
        ·
          refine ⟨19480461020182323355903109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12986974013454882237268739 19480461020182323355903109)
          ·
            refine ⟨3652586441284185629231833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19480461020182323355903109 3652586441284185629231833)
            ·
              refine ⟨2739439830963139221923875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3652586441284185629231833 2739439830963139221923875)
              ·
                refine ⟨4109159746444708832885813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2739439830963139221923875 4109159746444708832885813)
                ·
                  refine ⟨385233726229191453083045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4109159746444708832885813 385233726229191453083045)
                  ·
                    rfl

theorem cell21_1688040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_1688040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688040 prefixEnd_1688040 := by exact prefixLift 1688040
  have htrace : WordTrace (prefixWord ++ tailWord_1688040) baseStart_1688040 baseEnd_1688040 := by
    simpa [prefixWord, tailWord_1688040, baseEnd_1688040] using wordTrace_append hprefix tailTrace_1688040
  have hstable : (prefixWord ++ tailWord_1688040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688040).length < 2 ^ (prefixWord ++ tailWord_1688040).sum := by decide
  have hdescent : baseEnd_1688040 < baseStart_1688040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688161 : List Nat := [1, 2, 3, 1, 1, 6, 1, 6]
def baseStart_1688161 : Nat := 118140960795 + 1688161 * 2 ^ 59
def prefixEnd_1688161 : Nat := 4983230072969 + 3 ^ 40 * 1688161 * 2
def baseEnd_1688161 : Nat := 128420446692574043855377

theorem tailTrace_1688161 : CollatzResearch.WordTrace tailWord_1688161 prefixEnd_1688161 128420446692574043855377 := by
  unfold tailWord_1688161
  simp only [CollatzResearch.WordTrace]
  refine ⟨61572290037088486789984337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41048193358058991193322891 61572290037088486789984337)
  ·
    refine ⟨46179217527816365092488253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61572290037088486789984337 46179217527816365092488253)
    ·
      refine ⟨17317206572931136909683095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46179217527816365092488253 17317206572931136909683095)
      ·
        refine ⟨25975809859396705364524643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17317206572931136909683095 25975809859396705364524643)
        ·
          refine ⟨38963714789095058046786965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25975809859396705364524643 38963714789095058046786965)
          ·
            refine ⟨1826424130738830845943139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38963714789095058046786965 1826424130738830845943139)
            ·
              refine ⟨2739636196108246268914709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826424130738830845943139 2739636196108246268914709)
              ·
                refine ⟨128420446692574043855377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2739636196108246268914709 128420446692574043855377)
                ·
                  rfl

theorem cell21_1688161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 6].length) (baseStart_1688161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688161 prefixEnd_1688161 := by exact prefixLift 1688161
  have htrace : WordTrace (prefixWord ++ tailWord_1688161) baseStart_1688161 baseEnd_1688161 := by
    simpa [prefixWord, tailWord_1688161, baseEnd_1688161] using wordTrace_append hprefix tailTrace_1688161
  have hstable : (prefixWord ++ tailWord_1688161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688161).length < 2 ^ (prefixWord ++ tailWord_1688161).sum := by decide
  have hdescent : baseEnd_1688161 < baseStart_1688161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688178 : List Nat := [3, 2, 1, 2, 4, 1, 3, 5]
def baseStart_1688178 : Nat := 118140960795 + 1688178 * 2 ^ 59
def prefixEnd_1688178 : Nat := 4983230072969 + 3 ^ 40 * 1688178 * 2
def baseEnd_1688178 : Nat := 128421739903111293260921

theorem tailTrace_1688178 : CollatzResearch.WordTrace tailWord_1688178 prefixEnd_1688178 128421739903111293260921 := by
  unfold tailWord_1688178
  simp only [CollatzResearch.WordTrace]
  refine ⟨15393227519506724673338297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41048606718684599128902125 15393227519506724673338297)
  ·
    refine ⟨11544920639630043505003723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15393227519506724673338297 11544920639630043505003723)
    ·
      refine ⟨17317380959445065257505585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11544920639630043505003723 17317380959445065257505585)
      ·
        refine ⟨12988035719583798943129189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17317380959445065257505585 12988035719583798943129189)
        ·
          refine ⟨2435256697421962301836723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12988035719583798943129189 2435256697421962301836723)
          ·
            refine ⟨3652885046132943452755085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2435256697421962301836723 3652885046132943452755085)
            ·
              refine ⟨1369831892299853794783157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3652885046132943452755085 1369831892299853794783157)
              ·
                refine ⟨128421739903111293260921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1369831892299853794783157 128421739903111293260921)
                ·
                  rfl

theorem cell21_1688178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_1688178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688178 prefixEnd_1688178 := by exact prefixLift 1688178
  have htrace : WordTrace (prefixWord ++ tailWord_1688178) baseStart_1688178 baseEnd_1688178 := by
    simpa [prefixWord, tailWord_1688178, baseEnd_1688178] using wordTrace_append hprefix tailTrace_1688178
  have hstable : (prefixWord ++ tailWord_1688178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688178).length < 2 ^ (prefixWord ++ tailWord_1688178).sum := by decide
  have hdescent : baseEnd_1688178 < baseStart_1688178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688192 : List Nat := [2, 1, 1, 2, 1, 5, 1, 5, 3]
def baseStart_1688192 : Nat := 118140960795 + 1688192 * 2 ^ 59
def prefixEnd_1688192 : Nat := 4983230072969 + 3 ^ 40 * 1688192 * 2
def baseEnd_1688192 : Nat := 385268414700072966549401

theorem tailTrace_1688192 : CollatzResearch.WordTrace tailWord_1688192 prefixEnd_1688192 385268414700072966549401 := by
  unfold tailWord_1688192
  simp only [CollatzResearch.WordTrace]
  refine ⟨30786710349988089542181415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41048947133317452722908553 30786710349988089542181415)
  ·
    refine ⟨46180065524982134313272123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30786710349988089542181415 46180065524982134313272123)
    ·
      refine ⟨69270098287473201469908185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46180065524982134313272123 69270098287473201469908185)
      ·
        refine ⟨51952573715604901102431139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69270098287473201469908185 51952573715604901102431139)
        ·
          refine ⟨77928860573407351653646709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51952573715604901102431139 77928860573407351653646709)
          ·
            refine ⟨7305830678756939217529379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77928860573407351653646709 7305830678756939217529379)
            ·
              refine ⟨10958746018135408826294069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7305830678756939217529379 10958746018135408826294069)
              ·
                refine ⟨1027382439200194577465069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10958746018135408826294069 1027382439200194577465069)
                ·
                  refine ⟨385268414700072966549401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1027382439200194577465069 385268414700072966549401)
                  ·
                    rfl

theorem cell21_1688192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 3].length) (baseStart_1688192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688192 prefixEnd_1688192 := by exact prefixLift 1688192
  have htrace : WordTrace (prefixWord ++ tailWord_1688192) baseStart_1688192 baseEnd_1688192 := by
    simpa [prefixWord, tailWord_1688192, baseEnd_1688192] using wordTrace_append hprefix tailTrace_1688192
  have hstable : (prefixWord ++ tailWord_1688192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688192).length < 2 ^ (prefixWord ++ tailWord_1688192).sum := by decide
  have hdescent : baseEnd_1688192 < baseStart_1688192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688206 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1688206 : Nat := 118140960795 + 1688206 * 2 ^ 59
def prefixEnd_1688206 : Nat := 4983230072969 + 3 ^ 40 * 1688206 * 2
def baseEnd_1688206 : Nat := 385271609690812053316039

theorem tailTrace_1688206 : CollatzResearch.WordTrace tailWord_1688206 prefixEnd_1688206 385271609690812053316039 := by
  unfold tailWord_1688206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7696741415240682434421559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41049287547950306316914981 7696741415240682434421559)
  ·
    refine ⟨11545112122861023651632339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7696741415240682434421559 11545112122861023651632339)
    ·
      refine ⟨17317668184291535477448509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11545112122861023651632339 17317668184291535477448509)
      ·
        refine ⟨6494125569109325804043191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17317668184291535477448509 6494125569109325804043191)
        ·
          refine ⟨9741188353663988706064787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6494125569109325804043191 9741188353663988706064787)
          ·
            refine ⟨14611782530495983059097181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9741188353663988706064787 14611782530495983059097181)
            ·
              refine ⟨5479418448935993647161443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14611782530495983059097181 5479418448935993647161443)
              ·
                refine ⟨8219127673403990470742165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479418448935993647161443 8219127673403990470742165)
                ·
                  refine ⟨385271609690812053316039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8219127673403990470742165 385271609690812053316039)
                  ·
                    rfl

theorem cell21_1688206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1688206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688206 prefixEnd_1688206 := by exact prefixLift 1688206
  have htrace : WordTrace (prefixWord ++ tailWord_1688206) baseStart_1688206 baseEnd_1688206 := by
    simpa [prefixWord, tailWord_1688206, baseEnd_1688206] using wordTrace_append hprefix tailTrace_1688206
  have hstable : (prefixWord ++ tailWord_1688206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688206).length < 2 ^ (prefixWord ++ tailWord_1688206).sum := by decide
  have hdescent : baseEnd_1688206 < baseStart_1688206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688237 : List Nat := [1, 5, 2, 1, 1, 3, 1, 7]
def baseStart_1688237 : Nat := 118140960795 + 1688237 * 2 ^ 59
def prefixEnd_1688237 : Nat := 4983230072969 + 3 ^ 40 * 1688237 * 2
def baseEnd_1688237 : Nat := 128426228104387629433103

theorem tailTrace_1688237 : CollatzResearch.WordTrace tailWord_1688237 prefixEnd_1688237 128426228104387629433103 := by
  unfold tailWord_1688237
  simp only [CollatzResearch.WordTrace]
  refine ⟨61575061984813151769750965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41050041323208767846500643 61575061984813151769750965)
  ·
    refine ⟨5772662061076232978414153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61575061984813151769750965 5772662061076232978414153)
    ·
      refine ⟨4329496545807174733810615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5772662061076232978414153 4329496545807174733810615)
      ·
        refine ⟨6494244818710762100715923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4329496545807174733810615 6494244818710762100715923)
        ·
          refine ⟨9741367228066143151073885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6494244818710762100715923 9741367228066143151073885)
          ·
            refine ⟨3653012710524803681652707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9741367228066143151073885 3653012710524803681652707)
            ·
              refine ⟨5479519065787205522479061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653012710524803681652707 5479519065787205522479061)
              ·
                refine ⟨128426228104387629433103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5479519065787205522479061 128426228104387629433103)
                ·
                  rfl

theorem cell21_1688237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 7].length) (baseStart_1688237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688237 prefixEnd_1688237 := by exact prefixLift 1688237
  have htrace : WordTrace (prefixWord ++ tailWord_1688237) baseStart_1688237 baseEnd_1688237 := by
    simpa [prefixWord, tailWord_1688237, baseEnd_1688237] using wordTrace_append hprefix tailTrace_1688237
  have hstable : (prefixWord ++ tailWord_1688237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688237).length < 2 ^ (prefixWord ++ tailWord_1688237).sum := by decide
  have hdescent : baseEnd_1688237 < baseStart_1688237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688268 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 5]
def baseStart_1688268 : Nat := 118140960795 + 1688268 * 2 ^ 59
def prefixEnd_1688268 : Nat := 4983230072969 + 3 ^ 40 * 1688268 * 2
def baseEnd_1688268 : Nat := 385285758935513723282579

theorem tailTrace_1688268 : CollatzResearch.WordTrace tailWord_1688268 prefixEnd_1688268 385285758935513723282579 := by
  unfold tailWord_1688268
  simp only [CollatzResearch.WordTrace]
  refine ⟨30788096323850422032064729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41050795098467229376086305 30788096323850422032064729)
  ·
    refine ⟨23091072242887816524048547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30788096323850422032064729 23091072242887816524048547)
    ·
      refine ⟨34636608364331724786072821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23091072242887816524048547 34636608364331724786072821)
      ·
        refine ⟨3247182034156099198694327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34636608364331724786072821 3247182034156099198694327)
        ·
          refine ⟨4870773051234148798041491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3247182034156099198694327 4870773051234148798041491)
          ·
            refine ⟨7306159576851223197062237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4870773051234148798041491 7306159576851223197062237)
            ·
              refine ⟨2739809841319208698898339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7306159576851223197062237 2739809841319208698898339)
              ·
                refine ⟨4109714761978813048347509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2739809841319208698898339 4109714761978813048347509)
                ·
                  refine ⟨385285758935513723282579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4109714761978813048347509 385285758935513723282579)
                  ·
                    rfl

theorem cell21_1688268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_1688268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688268 prefixEnd_1688268 := by exact prefixLift 1688268
  have htrace : WordTrace (prefixWord ++ tailWord_1688268) baseStart_1688268 baseEnd_1688268 := by
    simpa [prefixWord, tailWord_1688268, baseEnd_1688268] using wordTrace_append hprefix tailTrace_1688268
  have hstable : (prefixWord ++ tailWord_1688268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688268).length < 2 ^ (prefixWord ++ tailWord_1688268).sum := by decide
  have hdescent : baseEnd_1688268 < baseStart_1688268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688282 : List Nat := [3, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_1688282 : Nat := 118140960795 + 1688282 * 2 ^ 59
def prefixEnd_1688282 : Nat := 4983230072969 + 3 ^ 40 * 1688282 * 2
def baseEnd_1688282 : Nat := 385288953926252810049217

theorem tailTrace_1688282 : CollatzResearch.WordTrace tailWord_1688282 prefixEnd_1688282 385288953926252810049217 := by
  unfold tailWord_1688282
  simp only [CollatzResearch.WordTrace]
  refine ⟨15394175817412531113784775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41051135513100082970092733 15394175817412531113784775)
  ·
    refine ⟨23091263726118796670677163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15394175817412531113784775 23091263726118796670677163)
    ·
      refine ⟨34636895589178195006015745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23091263726118796670677163 34636895589178195006015745)
      ·
        refine ⟨25977671691883646254511809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34636895589178195006015745 25977671691883646254511809)
        ·
          refine ⟨19483253768912734690883857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25977671691883646254511809 19483253768912734690883857)
          ·
            refine ⟨14612440326684551018162893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19483253768912734690883857 14612440326684551018162893)
            ·
              refine ⟨5479665122506706631811085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14612440326684551018162893 5479665122506706631811085)
              ·
                refine ⟨2054874420940014986929157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5479665122506706631811085 2054874420940014986929157)
                ·
                  refine ⟨385288953926252810049217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2054874420940014986929157 385288953926252810049217)
                  ·
                    rfl

theorem cell21_1688282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_1688282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688282 prefixEnd_1688282 := by exact prefixLift 1688282
  have htrace : WordTrace (prefixWord ++ tailWord_1688282) baseStart_1688282 baseEnd_1688282 := by
    simpa [prefixWord, tailWord_1688282, baseEnd_1688282] using wordTrace_append hprefix tailTrace_1688282
  have hstable : (prefixWord ++ tailWord_1688282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688282).length < 2 ^ (prefixWord ++ tailWord_1688282).sum := by decide
  have hdescent : baseEnd_1688282 < baseStart_1688282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688510 : List Nat := [4, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_1688510 : Nat := 118140960795 + 1688510 * 2 ^ 59
def prefixEnd_1688510 : Nat := 4983230072969 + 3 ^ 40 * 1688510 * 2
def baseEnd_1688510 : Nat := 385340986632575080248751

theorem tailTrace_1688510 : CollatzResearch.WordTrace tailWord_1688510 prefixEnd_1688510 385340986632575080248751 := by
  unfold tailWord_1688510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7698127389103014924304873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41056679408549412929625989 7698127389103014924304873)
  ·
    refine ⟨5773595541827261193228655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7698127389103014924304873 5773595541827261193228655)
    ·
      refine ⟨8660393312740891789842983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5773595541827261193228655 8660393312740891789842983)
      ·
        refine ⟨12990589969111337684764475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8660393312740891789842983 12990589969111337684764475)
        ·
          refine ⟨19485884953667006527146713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12990589969111337684764475 19485884953667006527146713)
          ·
            refine ⟨14614413715250254895360035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19485884953667006527146713 14614413715250254895360035)
            ·
              refine ⟨21921620572875382343040053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14614413715250254895360035 21921620572875382343040053)
              ·
                refine ⟨2055151928707067094660005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21921620572875382343040053 2055151928707067094660005)
                ·
                  refine ⟨385340986632575080248751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2055151928707067094660005 385340986632575080248751)
                  ·
                    rfl

theorem cell21_1688510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_1688510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688510 prefixEnd_1688510 := by exact prefixLift 1688510
  have htrace : WordTrace (prefixWord ++ tailWord_1688510) baseStart_1688510 baseEnd_1688510 := by
    simpa [prefixWord, tailWord_1688510, baseEnd_1688510] using wordTrace_append hprefix tailTrace_1688510
  have hstable : (prefixWord ++ tailWord_1688510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688510).length < 2 ^ (prefixWord ++ tailWord_1688510).sum := by decide
  have hdescent : baseEnd_1688510 < baseStart_1688510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688600 : List Nat := [2, 1, 2, 3, 2, 4, 7]
def baseStart_1688600 : Nat := 118140960795 + 1688600 * 2 ^ 59
def prefixEnd_1688600 : Nat := 4983230072969 + 3 ^ 40 * 1688600 * 2
def baseEnd_1688600 : Nat := 42817947317639435972063

theorem tailTrace_1688600 : CollatzResearch.WordTrace tailWord_1688600 prefixEnd_1688600 42817947317639435972063 := by
  unfold tailWord_1688600
  simp only [CollatzResearch.WordTrace]
  refine ⟨30794150841249032382607627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41058867788332043176810169 30794150841249032382607627)
  ·
    refine ⟨46191226261873548573911441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30794150841249032382607627 46191226261873548573911441)
    ·
      refine ⟨34643419696405161430433581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46191226261873548573911441 34643419696405161430433581)
      ·
        refine ⟨12991282386151935536412593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34643419696405161430433581 12991282386151935536412593)
        ·
          refine ⟨9743461789613951652309445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12991282386151935536412593 9743461789613951652309445)
          ·
            refine ⟨1826899085552615934808021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9743461789613951652309445 1826899085552615934808021)
            ·
              refine ⟨42817947317639435972063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1826899085552615934808021 42817947317639435972063)
              ·
                rfl

theorem cell21_1688600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 7].length) (baseStart_1688600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688600 prefixEnd_1688600 := by exact prefixLift 1688600
  have htrace : WordTrace (prefixWord ++ tailWord_1688600) baseStart_1688600 baseEnd_1688600 := by
    simpa [prefixWord, tailWord_1688600, baseEnd_1688600] using wordTrace_append hprefix tailTrace_1688600
  have hstable : (prefixWord ++ tailWord_1688600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688600).length < 2 ^ (prefixWord ++ tailWord_1688600).sum := by decide
  have hdescent : baseEnd_1688600 < baseStart_1688600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688769 : List Nat := [1, 2, 6, 1, 1, 3, 7]
def baseStart_1688769 : Nat := 118140960795 + 1688769 * 2 ^ 59
def prefixEnd_1688769 : Nat := 4983230072969 + 3 ^ 40 * 1688769 * 2
def baseEnd_1688769 : Nat := 42822232662360909492395

theorem tailTrace_1688769 : CollatzResearch.WordTrace tailWord_1688769 prefixEnd_1688769 42822232662360909492395 := by
  unfold tailWord_1688769
  simp only [CollatzResearch.WordTrace]
  refine ⟨61594465618885806628117361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41062977079257204418744907 61594465618885806628117361)
  ·
    refine ⟨46195849214164354971088021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61594465618885806628117361 46195849214164354971088021)
    ·
      refine ⟨2165430431913954139269751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46195849214164354971088021 2165430431913954139269751)
      ·
        refine ⟨3248145647870931208904627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165430431913954139269751 3248145647870931208904627)
        ·
          refine ⟨4872218471806396813356941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3248145647870931208904627 4872218471806396813356941)
          ·
            refine ⟨1827081926927398805008853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4872218471806396813356941 1827081926927398805008853)
            ·
              refine ⟨42822232662360909492395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1827081926927398805008853 42822232662360909492395)
              ·
                rfl

theorem cell21_1688769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 7].length) (baseStart_1688769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688769 prefixEnd_1688769 := by exact prefixLift 1688769
  have htrace : WordTrace (prefixWord ++ tailWord_1688769) baseStart_1688769 baseEnd_1688769 := by
    simpa [prefixWord, tailWord_1688769, baseEnd_1688769] using wordTrace_append hprefix tailTrace_1688769
  have hstable : (prefixWord ++ tailWord_1688769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688769).length < 2 ^ (prefixWord ++ tailWord_1688769).sum := by decide
  have hdescent : baseEnd_1688769 < baseStart_1688769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688811 : List Nat := [1, 1, 1, 1, 2, 6, 2, 7]
def baseStart_1688811 : Nat := 118140960795 + 1688811 * 2 ^ 59
def prefixEnd_1688811 : Nat := 4983230072969 + 3 ^ 40 * 1688811 * 2
def baseEnd_1688811 : Nat := 128469892977821815243823

theorem tailTrace_1688811 : CollatzResearch.WordTrace tailWord_1688811 prefixEnd_1688811 128469892977821815243823 := by
  unfold tailWord_1688811
  simp only [CollatzResearch.WordTrace]
  refine ⟨61595997484733647801146287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41063998323155765200764191 61595997484733647801146287)
  ·
    refine ⟨92393996227100471701719431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61595997484733647801146287 92393996227100471701719431)
    ·
      refine ⟨138590994340650707552579147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92393996227100471701719431 138590994340650707552579147)
      ·
        refine ⟨207886491510976061328868721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138590994340650707552579147 207886491510976061328868721)
        ·
          refine ⟨155914868633232045996651541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207886491510976061328868721 155914868633232045996651541)
          ·
            refine ⟨7308509467182752156093041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155914868633232045996651541 7308509467182752156093041)
            ·
              refine ⟨5481382100387064117069781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7308509467182752156093041 5481382100387064117069781)
              ·
                refine ⟨128469892977821815243823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5481382100387064117069781 128469892977821815243823)
                ·
                  rfl

theorem cell21_1688811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 7].length) (baseStart_1688811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688811 prefixEnd_1688811 := by exact prefixLift 1688811
  have htrace : WordTrace (prefixWord ++ tailWord_1688811) baseStart_1688811 baseEnd_1688811 := by
    simpa [prefixWord, tailWord_1688811, baseEnd_1688811] using wordTrace_append hprefix tailTrace_1688811
  have hstable : (prefixWord ++ tailWord_1688811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688811).length < 2 ^ (prefixWord ++ tailWord_1688811).sum := by decide
  have hdescent : baseEnd_1688811 < baseStart_1688811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688828 : List Nat := [2, 2, 2, 1, 6, 8]
def baseStart_1688828 : Nat := 118140960795 + 1688828 * 2 ^ 59
def prefixEnd_1688828 : Nat := 4983230072969 + 3 ^ 40 * 1688828 * 2
def baseEnd_1688828 : Nat := 14274576243151007183263

theorem tailTrace_1688828 : CollatzResearch.WordTrace tailWord_1688828 prefixEnd_1688828 14274576243151007183263 := by
  unfold tailWord_1688828
  simp only [CollatzResearch.WordTrace]
  refine ⟨30798308762836029852257569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41064411683781373136343425 30798308762836029852257569)
  ·
    refine ⟨23098731572127022389193177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30798308762836029852257569 23098731572127022389193177)
    ·
      refine ⟨17324048679095266791894883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23098731572127022389193177 17324048679095266791894883)
      ·
        refine ⟨25986073018642900187842325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17324048679095266791894883 25986073018642900187842325)
        ·
          refine ⟨1218097172748885946305109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25986073018642900187842325 1218097172748885946305109)
          ·
            refine ⟨14274576243151007183263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1218097172748885946305109 14274576243151007183263)
            ·
              rfl

theorem cell21_1688828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 8].length) (baseStart_1688828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688828 prefixEnd_1688828 := by exact prefixLift 1688828
  have htrace : WordTrace (prefixWord ++ tailWord_1688828) baseStart_1688828 baseEnd_1688828 := by
    simpa [prefixWord, tailWord_1688828, baseEnd_1688828] using wordTrace_append hprefix tailTrace_1688828
  have hstable : (prefixWord ++ tailWord_1688828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688828).length < 2 ^ (prefixWord ++ tailWord_1688828).sum := by decide
  have hdescent : baseEnd_1688828 < baseStart_1688828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688842 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_1688842 : Nat := 118140960795 + 1688842 * 2 ^ 59
def prefixEnd_1688842 : Nat := 4983230072969 + 3 ^ 40 * 1688842 * 2
def baseEnd_1688842 : Nat := 385416753555816280714739

theorem tailTrace_1688842 : CollatzResearch.WordTrace tailWord_1688842 prefixEnd_1688842 385416753555816280714739 := by
  unfold tailWord_1688842
  simp only [CollatzResearch.WordTrace]
  refine ⟨15399282036905335023881195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41064752098414226730349853 15399282036905335023881195)
  ·
    refine ⟨23098923055358002535821793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15399282036905335023881195 23098923055358002535821793)
    ·
      refine ⟨17324192291518501901866345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23098923055358002535821793 17324192291518501901866345)
      ·
        refine ⟨12993144218638876426399759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17324192291518501901866345 12993144218638876426399759)
        ·
          refine ⟨19489716327958314639599639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12993144218638876426399759 19489716327958314639599639)
          ·
            refine ⟨29234574491937471959399459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19489716327958314639599639 29234574491937471959399459)
            ·
              refine ⟨43851861737906207939099189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29234574491937471959399459 43851861737906207939099189)
              ·
                refine ⟨4111112037928706994290549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43851861737906207939099189 4111112037928706994290549)
                ·
                  refine ⟨385416753555816280714739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4111112037928706994290549 385416753555816280714739)
                  ·
                    rfl

theorem cell21_1688842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_1688842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688842 prefixEnd_1688842 := by exact prefixLift 1688842
  have htrace : WordTrace (prefixWord ++ tailWord_1688842) baseStart_1688842 baseEnd_1688842 := by
    simpa [prefixWord, tailWord_1688842, baseEnd_1688842] using wordTrace_append hprefix tailTrace_1688842
  have hstable : (prefixWord ++ tailWord_1688842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688842).length < 2 ^ (prefixWord ++ tailWord_1688842).sum := by decide
  have hdescent : baseEnd_1688842 < baseStart_1688842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688958 : List Nat := [4, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_1688958 : Nat := 118140960795 + 1688958 * 2 ^ 59
def prefixEnd_1688958 : Nat := 4983230072969 + 3 ^ 40 * 1688958 * 2
def baseEnd_1688958 : Nat := 385443226336225856781169

theorem tailTrace_1688958 : CollatzResearch.WordTrace tailWord_1688958 prefixEnd_1688958 385443226336225856781169 := by
  unfold tailWord_1688958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7700169876900136488343441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41067572676800727937831685 7700169876900136488343441)
  ·
    refine ⟨5775127407675102366257581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7700169876900136488343441 5775127407675102366257581)
    ·
      refine ⟨2165672777878163387346593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5775127407675102366257581 2165672777878163387346593)
      ·
        refine ⟨1624254583408622540509945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2165672777878163387346593 1624254583408622540509945)
        ·
          refine ⟨1218190937556466905382459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1624254583408622540509945 1218190937556466905382459)
          ·
            refine ⟨1827286406334700358073689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218190937556466905382459 1827286406334700358073689)
            ·
              refine ⟨1370464804751025268555267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1827286406334700358073689 1370464804751025268555267)
              ·
                refine ⟨2055697207126537902832901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370464804751025268555267 2055697207126537902832901)
                ·
                  refine ⟨385443226336225856781169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2055697207126537902832901 385443226336225856781169)
                  ·
                    rfl

theorem cell21_1688958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_1688958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688958 prefixEnd_1688958 := by exact prefixLift 1688958
  have htrace : WordTrace (prefixWord ++ tailWord_1688958) baseStart_1688958 baseEnd_1688958 := by
    simpa [prefixWord, tailWord_1688958, baseEnd_1688958] using wordTrace_append hprefix tailTrace_1688958
  have hstable : (prefixWord ++ tailWord_1688958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688958).length < 2 ^ (prefixWord ++ tailWord_1688958).sum := by decide
  have hdescent : baseEnd_1688958 < baseStart_1688958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688963 : List Nat := [1, 1, 1, 3, 5, 1, 1, 8]
def baseStart_1688963 : Nat := 118140960795 + 1688963 * 2 ^ 59
def prefixEnd_1688963 : Nat := 4983230072969 + 3 ^ 40 * 1688963 * 2
def baseEnd_1688963 : Nat := 128481455801448986399275

theorem tailTrace_1688963 : CollatzResearch.WordTrace tailWord_1688963 prefixEnd_1688963 128481455801448986399275 := by
  unfold tailWord_1688963
  simp only [CollatzResearch.WordTrace]
  refine ⟨61601541380182977760679543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41067694253455318507119695 61601541380182977760679543)
  ·
    refine ⟨92402312070274466641019315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61601541380182977760679543 92402312070274466641019315)
    ·
      refine ⟨138603468105411699961528973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92402312070274466641019315 138603468105411699961528973)
      ·
        refine ⟨51976300539529387485573365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138603468105411699961528973 51976300539529387485573365)
        ·
          refine ⟨4872778175580880076772503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51976300539529387485573365 4872778175580880076772503)
          ·
            refine ⟨7309167263371320115158755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4872778175580880076772503 7309167263371320115158755)
            ·
              refine ⟨10963750895056980172738133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7309167263371320115158755 10963750895056980172738133)
              ·
                refine ⟨128481455801448986399275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10963750895056980172738133 128481455801448986399275)
                ·
                  rfl

theorem cell21_1688963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 8].length) (baseStart_1688963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688963 prefixEnd_1688963 := by exact prefixLift 1688963
  have htrace : WordTrace (prefixWord ++ tailWord_1688963) baseStart_1688963 baseEnd_1688963 := by
    simpa [prefixWord, tailWord_1688963, baseEnd_1688963] using wordTrace_append hprefix tailTrace_1688963
  have hstable : (prefixWord ++ tailWord_1688963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688963).length < 2 ^ (prefixWord ++ tailWord_1688963).sum := by decide
  have hdescent : baseEnd_1688963 < baseStart_1688963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688980 : List Nat := [2, 4, 2, 1, 2, 1, 2, 7]
def baseStart_1688980 : Nat := 118140960795 + 1688980 * 2 ^ 59
def prefixEnd_1688980 : Nat := 4983230072969 + 3 ^ 40 * 1688980 * 2
def baseEnd_1688980 : Nat := 128482749011986235804819

theorem tailTrace_1688980 : CollatzResearch.WordTrace tailWord_1688980 prefixEnd_1688980 128482749011986235804819 := by
  unfold tailWord_1688980
  simp only [CollatzResearch.WordTrace]
  refine ⟨30801080710560694832024197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41068107614080926442698929 30801080710560694832024197)
  ·
    refine ⟨5775202633230130281004537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30801080710560694832024197 5775202633230130281004537)
    ·
      refine ⟨4331401974922597710753403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5775202633230130281004537 4331401974922597710753403)
      ·
        refine ⟨6497102962383896566130105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4331401974922597710753403 6497102962383896566130105)
        ·
          refine ⟨4872827221787922424597579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6497102962383896566130105 4872827221787922424597579)
          ·
            refine ⟨7309240832681883636896369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4872827221787922424597579 7309240832681883636896369)
            ·
              refine ⟨5481930624511412727672277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7309240832681883636896369 5481930624511412727672277)
              ·
                refine ⟨128482749011986235804819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5481930624511412727672277 128482749011986235804819)
                ·
                  rfl

theorem cell21_1688980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_1688980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1688980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1688980 prefixEnd_1688980 := by exact prefixLift 1688980
  have htrace : WordTrace (prefixWord ++ tailWord_1688980) baseStart_1688980 baseEnd_1688980 := by
    simpa [prefixWord, tailWord_1688980, baseEnd_1688980] using wordTrace_append hprefix tailTrace_1688980
  have hstable : (prefixWord ++ tailWord_1688980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688980).length < 2 ^ (prefixWord ++ tailWord_1688980).sum := by decide
  have hdescent : baseEnd_1688980 < baseStart_1688980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689090 : List Nat := [3, 4, 1, 2, 1, 3, 2, 5]
def baseStart_1689090 : Nat := 118140960795 + 1689090 * 2 ^ 59
def prefixEnd_1689090 : Nat := 4983230072969 + 3 ^ 40 * 1689090 * 2
def baseEnd_1689090 : Nat := 128491116844874320193633

theorem tailTrace_1689090 : CollatzResearch.WordTrace tailWord_1689090 prefixEnd_1689090 128491116844874320193633 := by
  unfold tailWord_1689090
  simp only [CollatzResearch.WordTrace]
  refine ⟨15401543362680719612638181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41070782300481918967035149 15401543362680719612638181)
  ·
    refine ⟨2887789380502634927369659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15401543362680719612638181 2887789380502634927369659)
    ·
      refine ⟨4331684070753952391054489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2887789380502634927369659 4331684070753952391054489)
      ·
        refine ⟨3248763053065464293290867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4331684070753952391054489 3248763053065464293290867)
        ·
          refine ⟨4873144579598196439936301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3248763053065464293290867 4873144579598196439936301)
          ·
            refine ⟨1827429217349323664976113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4873144579598196439936301 1827429217349323664976113)
            ·
              refine ⟨1370571913011992748732085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1827429217349323664976113 1370571913011992748732085)
              ·
                refine ⟨128491116844874320193633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1370571913011992748732085 128491116844874320193633)
                ·
                  rfl

theorem cell21_1689090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_1689090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689090 prefixEnd_1689090 := by exact prefixLift 1689090
  have htrace : WordTrace (prefixWord ++ tailWord_1689090) baseStart_1689090 baseEnd_1689090 := by
    simpa [prefixWord, tailWord_1689090, baseEnd_1689090] using wordTrace_append hprefix tailTrace_1689090
  have hstable : (prefixWord ++ tailWord_1689090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689090).length < 2 ^ (prefixWord ++ tailWord_1689090).sum := by decide
  have hdescent : baseEnd_1689090 < baseStart_1689090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689180 : List Nat := [2, 2, 4, 1, 2, 2, 1, 4, 3]
def baseStart_1689180 : Nat := 118140960795 + 1689180 * 2 ^ 59
def prefixEnd_1689180 : Nat := 4983230072969 + 3 ^ 40 * 1689180 * 2
def baseEnd_1689180 : Nat := 385493889760802804080715

theorem tailTrace_1689180 : CollatzResearch.WordTrace tailWord_1689180 prefixEnd_1689180 385493889760802804080715 := by
  unfold tailWord_1689180
  simp only [CollatzResearch.WordTrace]
  refine ⟨30804728010198411910664497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41072970680264549214219329 30804728010198411910664497)
  ·
    refine ⟨23103546007648808932998373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30804728010198411910664497 23103546007648808932998373)
    ·
      refine ⟨4331914876434151674937195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23103546007648808932998373 4331914876434151674937195)
      ·
        refine ⟨6497872314651227512405793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4331914876434151674937195 6497872314651227512405793)
        ·
          refine ⟨4873404235988420634304345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6497872314651227512405793 4873404235988420634304345)
          ·
            refine ⟨3655053176991315475728259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4873404235988420634304345 3655053176991315475728259)
            ·
              refine ⟨5482579765486973213592389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655053176991315475728259 5482579765486973213592389)
              ·
                refine ⟨1027983706028807477548573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5482579765486973213592389 1027983706028807477548573)
                ·
                  refine ⟨385493889760802804080715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1027983706028807477548573 385493889760802804080715)
                  ·
                    rfl

theorem cell21_1689180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_1689180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689180 prefixEnd_1689180 := by exact prefixLift 1689180
  have htrace : WordTrace (prefixWord ++ tailWord_1689180) baseStart_1689180 baseEnd_1689180 := by
    simpa [prefixWord, tailWord_1689180, baseEnd_1689180] using wordTrace_append hprefix tailTrace_1689180
  have hstable : (prefixWord ++ tailWord_1689180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689180).length < 2 ^ (prefixWord ++ tailWord_1689180).sum := by decide
  have hdescent : baseEnd_1689180 < baseStart_1689180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689191 : List Nat := [1, 1, 5, 1, 1, 1, 5, 6]
def baseStart_1689191 : Nat := 118140960795 + 1689191 * 2 ^ 59
def prefixEnd_1689191 : Nat := 4983230072969 + 3 ^ 40 * 1689191 * 2
def baseEnd_1689191 : Nat := 128498800036889743132453

theorem tailTrace_1689191 : CollatzResearch.WordTrace tailWord_1689191 prefixEnd_1689191 128498800036889743132453 := by
  unfold tailWord_1689191
  simp only [CollatzResearch.WordTrace]
  refine ⟨61609857223356972699979427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41073238148904648466652951 61609857223356972699979427)
  ·
    refine ⟨92414785835035459049969141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61609857223356972699979427 92414785835035459049969141)
    ·
      refine ⟨8663886172034574285934607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92414785835035459049969141 8663886172034574285934607)
      ·
        refine ⟨12995829258051861428901911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8663886172034574285934607 12995829258051861428901911)
        ·
          refine ⟨19493743887077792143352867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12995829258051861428901911 19493743887077792143352867)
          ·
            refine ⟨29240615830616688215029301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19493743887077792143352867 29240615830616688215029301)
            ·
              refine ⟨2741307734120314520158997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29240615830616688215029301 2741307734120314520158997)
              ·
                refine ⟨128498800036889743132453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2741307734120314520158997 128498800036889743132453)
                ·
                  rfl

theorem cell21_1689191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 6].length) (baseStart_1689191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689191 prefixEnd_1689191 := by exact prefixLift 1689191
  have htrace : WordTrace (prefixWord ++ tailWord_1689191) baseStart_1689191 baseEnd_1689191 := by
    simpa [prefixWord, tailWord_1689191, baseEnd_1689191] using wordTrace_append hprefix tailTrace_1689191
  have hstable : (prefixWord ++ tailWord_1689191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689191).length < 2 ^ (prefixWord ++ tailWord_1689191).sum := by decide
  have hdescent : baseEnd_1689191 < baseStart_1689191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689239 : List Nat := [1, 1, 3, 3, 2, 2, 2, 4, 3]
def baseStart_1689239 : Nat := 118140960795 + 1689239 * 2 ^ 59
def prefixEnd_1689239 : Nat := 4983230072969 + 3 ^ 40 * 1689239 * 2
def baseEnd_1689239 : Nat := 385507354364631812597261

theorem tailTrace_1689239 : CollatzResearch.WordTrace tailWord_1689239 prefixEnd_1689239 385507354364631812597261 := by
  unfold tailWord_1689239
  simp only [CollatzResearch.WordTrace]
  refine ⟨61611607927183076897726771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41074405284788717931817847 61611607927183076897726771)
  ·
    refine ⟨92417411890774615346590157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61611607927183076897726771 92417411890774615346590157)
    ·
      refine ⟨34656529459040480754971309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92417411890774615346590157 34656529459040480754971309)
      ·
        refine ⟨12996198547140180283114241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34656529459040480754971309 12996198547140180283114241)
        ·
          refine ⟨9747148910355135212335681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12996198547140180283114241 9747148910355135212335681)
          ·
            refine ⟨7310361682766351409251761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9747148910355135212335681 7310361682766351409251761)
            ·
              refine ⟨5482771262074763556938821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7310361682766351409251761 5482771262074763556938821)
              ·
                refine ⟨1028019611639018166926029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5482771262074763556938821 1028019611639018166926029)
                ·
                  refine ⟨385507354364631812597261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1028019611639018166926029 385507354364631812597261)
                  ·
                    rfl

theorem cell21_1689239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 3].length) (baseStart_1689239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689239 prefixEnd_1689239 := by exact prefixLift 1689239
  have htrace : WordTrace (prefixWord ++ tailWord_1689239) baseStart_1689239 baseEnd_1689239 := by
    simpa [prefixWord, tailWord_1689239, baseEnd_1689239] using wordTrace_append hprefix tailTrace_1689239
  have hstable : (prefixWord ++ tailWord_1689239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689239).length < 2 ^ (prefixWord ++ tailWord_1689239).sum := by decide
  have hdescent : baseEnd_1689239 < baseStart_1689239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689270 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1689270 : Nat := 118140960795 + 1689270 * 2 ^ 59
def prefixEnd_1689270 : Nat := 4983230072969 + 3 ^ 40 * 1689270 * 2
def baseEnd_1689270 : Nat := 385514428986982647580531

theorem tailTrace_1689270 : CollatzResearch.WordTrace tailWord_1689270 prefixEnd_1689270 385514428986982647580531 := by
  unfold tailWord_1689270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3850796161879423074506579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41075159060047179461403509 3850796161879423074506579)
  ·
    refine ⟨5776194242819134611759869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3850796161879423074506579 5776194242819134611759869)
    ·
      refine ⟨2166072841057175479409951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5776194242819134611759869 2166072841057175479409951)
      ·
        refine ⟨3249109261585763219114927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2166072841057175479409951 3249109261585763219114927)
        ·
          refine ⟨4873663892378644828672391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3249109261585763219114927 4873663892378644828672391)
          ·
            refine ⟨7310495838567967243008587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4873663892378644828672391 7310495838567967243008587)
            ·
              refine ⟨10965743757851950864512881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7310495838567967243008587 10965743757851950864512881)
              ·
                refine ⟨8224307818388963148384661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10965743757851950864512881 8224307818388963148384661)
                ·
                  refine ⟨385514428986982647580531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8224307818388963148384661 385514428986982647580531)
                  ·
                    rfl

theorem cell21_1689270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1689270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689270 prefixEnd_1689270 := by exact prefixLift 1689270
  have htrace : WordTrace (prefixWord ++ tailWord_1689270) baseStart_1689270 baseEnd_1689270 := by
    simpa [prefixWord, tailWord_1689270, baseEnd_1689270] using wordTrace_append hprefix tailTrace_1689270
  have hstable : (prefixWord ++ tailWord_1689270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689270).length < 2 ^ (prefixWord ++ tailWord_1689270).sum := by decide
  have hdescent : baseEnd_1689270 < baseStart_1689270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689346 : List Nat := [3, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1689346 : Nat := 118140960795 + 1689346 * 2 ^ 59
def prefixEnd_1689346 : Nat := 4983230072969 + 3 ^ 40 * 1689346 * 2
def baseEnd_1689346 : Nat := 385531773222423404313709

theorem tailTrace_1689346 : CollatzResearch.WordTrace tailWord_1689346 prefixEnd_1689346 385531773222423404313709 := by
  unfold tailWord_1689346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15403877634448858542967973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41077007025196956114581261 15403877634448858542967973)
  ·
    refine ⟨2888227056459160976806495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15403877634448858542967973 2888227056459160976806495)
    ·
      refine ⟨4332340584688741465209743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2888227056459160976806495 4332340584688741465209743)
      ·
        refine ⟨6498510877033112197814615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4332340584688741465209743 6498510877033112197814615)
        ·
          refine ⟨9747766315549668296721923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6498510877033112197814615 9747766315549668296721923)
          ·
            refine ⟨14621649473324502445082885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9747766315549668296721923 14621649473324502445082885)
            ·
              refine ⟨2741559276248344208453041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14621649473324502445082885 2741559276248344208453041)
              ·
                refine ⟨2056169457186258156339781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2741559276248344208453041 2056169457186258156339781)
                ·
                  refine ⟨385531773222423404313709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2056169457186258156339781 385531773222423404313709)
                  ·
                    rfl

theorem cell21_1689346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1689346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689346 prefixEnd_1689346 := by exact prefixLift 1689346
  have htrace : WordTrace (prefixWord ++ tailWord_1689346) baseStart_1689346 baseEnd_1689346 := by
    simpa [prefixWord, tailWord_1689346, baseEnd_1689346] using wordTrace_append hprefix tailTrace_1689346
  have hstable : (prefixWord ++ tailWord_1689346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689346).length < 2 ^ (prefixWord ++ tailWord_1689346).sum := by decide
  have hdescent : baseEnd_1689346 < baseStart_1689346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689405 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 6]
def baseStart_1689405 : Nat := 118140960795 + 1689405 * 2 ^ 59
def prefixEnd_1689405 : Nat := 4983230072969 + 3 ^ 40 * 1689405 * 2
def baseEnd_1689405 : Nat := 385545237826252412830255

theorem tailTrace_1689405 : CollatzResearch.WordTrace tailWord_1689405 prefixEnd_1689405 385545237826252412830255 := by
  unfold tailWord_1689405
  simp only [CollatzResearch.WordTrace]
  refine ⟨61617662444581687248269669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41078441629721124832179779 61617662444581687248269669)
  ·
    refine ⟨11553311708359066359050563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61617662444581687248269669 11553311708359066359050563)
    ·
      refine ⟨17329967562538599538575845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11553311708359066359050563 17329967562538599538575845)
      ·
        refine ⟨3249368917975987413482971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17329967562538599538575845 3249368917975987413482971)
        ·
          refine ⟨4874053376963981120224457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3249368917975987413482971 4874053376963981120224457)
          ·
            refine ⟨3655540032722985840168343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4874053376963981120224457 3655540032722985840168343)
            ·
              refine ⟨5483310049084478760252515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655540032722985840168343 5483310049084478760252515)
              ·
                refine ⟨8224965073626718140378773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5483310049084478760252515 8224965073626718140378773)
                ·
                  refine ⟨385545237826252412830255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8224965073626718140378773 385545237826252412830255)
                  ·
                    rfl

theorem cell21_1689405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_1689405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689405 prefixEnd_1689405 := by exact prefixLift 1689405
  have htrace : WordTrace (prefixWord ++ tailWord_1689405) baseStart_1689405 baseEnd_1689405 := by
    simpa [prefixWord, tailWord_1689405, baseEnd_1689405] using wordTrace_append hprefix tailTrace_1689405
  have hstable : (prefixWord ++ tailWord_1689405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689405).length < 2 ^ (prefixWord ++ tailWord_1689405).sum := by decide
  have hdescent : baseEnd_1689405 < baseStart_1689405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689433 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 5]
def baseStart_1689433 : Nat := 118140960795 + 1689433 * 2 ^ 59
def prefixEnd_1689433 : Nat := 4983230072969 + 3 ^ 40 * 1689433 * 2
def baseEnd_1689433 : Nat := 385551627807730586363531

theorem tailTrace_1689433 : CollatzResearch.WordTrace tailWord_1689433 prefixEnd_1689433 385551627807730586363531 := by
  unfold tailWord_1689433
  simp only [CollatzResearch.WordTrace]
  refine ⟨61618683688480248030288953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41079122458986832020192635 61618683688480248030288953)
  ·
    refine ⟨46214012766360186022716715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61618683688480248030288953 46214012766360186022716715)
    ·
      refine ⟨69321019149540279034075073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46214012766360186022716715 69321019149540279034075073)
      ·
        refine ⟨51990764362155209275556305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69321019149540279034075073 51990764362155209275556305)
        ·
          refine ⟨38993073271616406956667229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51990764362155209275556305 38993073271616406956667229)
          ·
            refine ⟨14622402476856152608750211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38993073271616406956667229 14622402476856152608750211)
            ·
              refine ⟨21933603715284228913125317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14622402476856152608750211 21933603715284228913125317)
              ·
                refine ⟨4112550696615792921210997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21933603715284228913125317 4112550696615792921210997)
                ·
                  refine ⟨385551627807730586363531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4112550696615792921210997 385551627807730586363531)
                  ·
                    rfl

theorem cell21_1689433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_1689433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689433 prefixEnd_1689433 := by exact prefixLift 1689433
  have htrace : WordTrace (prefixWord ++ tailWord_1689433) baseStart_1689433 baseEnd_1689433 := by
    simpa [prefixWord, tailWord_1689433, baseEnd_1689433] using wordTrace_append hprefix tailTrace_1689433
  have hstable : (prefixWord ++ tailWord_1689433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689433).length < 2 ^ (prefixWord ++ tailWord_1689433).sum := by decide
  have hdescent : baseEnd_1689433 < baseStart_1689433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689436 : List Nat := [2, 2, 4, 2, 2, 1, 1, 7]
def baseStart_1689436 : Nat := 118140960795 + 1689436 * 2 ^ 59
def prefixEnd_1689436 : Nat := 4983230072969 + 3 ^ 40 * 1689436 * 2
def baseEnd_1689436 : Nat := 128517437482867749271175

theorem tailTrace_1689436 : CollatzResearch.WordTrace tailWord_1689436 prefixEnd_1689436 128517437482867749271175 := by
  unfold tailWord_1689436
  simp only [CollatzResearch.WordTrace]
  refine ⟨30809396553734689771324081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41079195404979586361765441 30809396553734689771324081)
  ·
    refine ⟨23107047415301017328493061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30809396553734689771324081 23107047415301017328493061)
    ·
      refine ⟨4332571390368940749092449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23107047415301017328493061 4332571390368940749092449)
      ·
        refine ⟨3249428542776705561819337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4332571390368940749092449 3249428542776705561819337)
        ·
          refine ⟨2437071407082529171364503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3249428542776705561819337 2437071407082529171364503)
          ·
            refine ⟨3655607110623793757046755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437071407082529171364503 3655607110623793757046755)
            ·
              refine ⟨5483410665935690635570133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655607110623793757046755 5483410665935690635570133)
              ·
                refine ⟨128517437482867749271175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5483410665935690635570133 128517437482867749271175)
                ·
                  rfl

theorem cell21_1689436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_1689436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689436 prefixEnd_1689436 := by exact prefixLift 1689436
  have htrace : WordTrace (prefixWord ++ tailWord_1689436) baseStart_1689436 baseEnd_1689436 := by
    simpa [prefixWord, tailWord_1689436, baseEnd_1689436] using wordTrace_append hprefix tailTrace_1689436
  have hstable : (prefixWord ++ tailWord_1689436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689436).length < 2 ^ (prefixWord ++ tailWord_1689436).sum := by decide
  have hdescent : baseEnd_1689436 < baseStart_1689436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689512 : List Nat := [2, 1, 6, 2, 1, 9]
def baseStart_1689512 : Nat := 118140960795 + 1689512 * 2 ^ 59
def prefixEnd_1689512 : Nat := 4983230072969 + 3 ^ 40 * 1689512 * 2
def baseEnd_1689512 : Nat := 14280357654964592760989

theorem tailTrace_1689512 : CollatzResearch.WordTrace tailWord_1689512 prefixEnd_1689512 14280357654964592760989 := by
  unfold tailWord_1689512
  simp only [CollatzResearch.WordTrace]
  refine ⟨30810782527597022261207395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41081043370129363014943193 30810782527597022261207395)
  ·
    refine ⟨46216173791395533391811093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30810782527597022261207395 46216173791395533391811093)
    ·
      refine ⟨2166383146471665627741145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46216173791395533391811093 2166383146471665627741145)
      ·
        refine ⟨1624787359853749220805859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2166383146471665627741145 1624787359853749220805859)
        ·
          refine ⟨2437181039780623831208789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624787359853749220805859 2437181039780623831208789)
          ·
            refine ⟨14280357654964592760989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2437181039780623831208789 14280357654964592760989)
            ·
              rfl

theorem cell21_1689512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 9].length) (baseStart_1689512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689512 prefixEnd_1689512 := by exact prefixLift 1689512
  have htrace : WordTrace (prefixWord ++ tailWord_1689512) baseStart_1689512 baseEnd_1689512 := by
    simpa [prefixWord, tailWord_1689512, baseEnd_1689512] using wordTrace_append hprefix tailTrace_1689512
  have hstable : (prefixWord ++ tailWord_1689512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689512).length < 2 ^ (prefixWord ++ tailWord_1689512).sum := by decide
  have hdescent : baseEnd_1689512 < baseStart_1689512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689518 : List Nat := [4, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_1689518 : Nat := 118140960795 + 1689518 * 2 ^ 59
def prefixEnd_1689518 : Nat := 4983230072969 + 3 ^ 40 * 1689518 * 2
def baseEnd_1689518 : Nat := 385571025965789327446691

theorem tailTrace_1689518 : CollatzResearch.WordTrace tailWord_1689518 prefixEnd_1689518 385571025965789327446691 := by
  unfold tailWord_1689518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7702722986646538443391651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41081189262114871698088805 7702722986646538443391651)
  ·
    refine ⟨11554084479969807665087477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7702722986646538443391651 11554084479969807665087477)
    ·
      refine ⟨1083195419997169468601951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11554084479969807665087477 1083195419997169468601951)
      ·
        refine ⟨1624793129995754202902927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1083195419997169468601951 1624793129995754202902927)
        ·
          refine ⟨2437189694993631304354391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624793129995754202902927 2437189694993631304354391)
          ·
            refine ⟨3655784542490446956531587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437189694993631304354391 3655784542490446956531587)
            ·
              refine ⟨5483676813735670434797381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655784542490446956531587 5483676813735670434797381)
              ·
                refine ⟨1028189402575438206524509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5483676813735670434797381 1028189402575438206524509)
                ·
                  refine ⟨385571025965789327446691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1028189402575438206524509 385571025965789327446691)
                  ·
                    rfl

theorem cell21_1689518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_1689518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689518 prefixEnd_1689518 := by exact prefixLift 1689518
  have htrace : WordTrace (prefixWord ++ tailWord_1689518) baseStart_1689518 baseEnd_1689518 := by
    simpa [prefixWord, tailWord_1689518, baseEnd_1689518] using wordTrace_append hprefix tailTrace_1689518
  have hstable : (prefixWord ++ tailWord_1689518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689518).length < 2 ^ (prefixWord ++ tailWord_1689518).sum := by decide
  have hdescent : baseEnd_1689518 < baseStart_1689518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689636 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 5]
def baseStart_1689636 : Nat := 118140960795 + 1689636 * 2 ^ 59
def prefixEnd_1689636 : Nat := 4983230072969 + 3 ^ 40 * 1689636 * 2
def baseEnd_1689636 : Nat := 385597955173447344479783

theorem tailTrace_1689636 : CollatzResearch.WordTrace tailWord_1689636 prefixEnd_1689636 385597955173447344479783 := by
  unfold tailWord_1689636
  simp only [CollatzResearch.WordTrace]
  refine ⟨30813043853372406849964381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41084058471163209133285841 30813043853372406849964381)
  ·
    refine ⟨11554891445014652568736643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30813043853372406849964381 11554891445014652568736643)
    ·
      refine ⟨17332337167521978853104965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11554891445014652568736643 17332337167521978853104965)
      ·
        refine ⟨3249813218910371034957181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17332337167521978853104965 3249813218910371034957181)
        ·
          refine ⟨1218679957091389138108943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3249813218910371034957181 1218679957091389138108943)
          ·
            refine ⟨1828019935637083707163415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218679957091389138108943 1828019935637083707163415)
            ·
              refine ⟨2742029903455625560745123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828019935637083707163415 2742029903455625560745123)
              ·
                refine ⟨4113044855183438341117685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2742029903455625560745123 4113044855183438341117685)
                ·
                  refine ⟨385597955173447344479783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4113044855183438341117685 385597955173447344479783)
                  ·
                    rfl

theorem cell21_1689636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_1689636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689636 prefixEnd_1689636 := by exact prefixLift 1689636
  have htrace : WordTrace (prefixWord ++ tailWord_1689636) baseStart_1689636 baseEnd_1689636 := by
    simpa [prefixWord, tailWord_1689636, baseEnd_1689636] using wordTrace_append hprefix tailTrace_1689636
  have hstable : (prefixWord ++ tailWord_1689636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689636).length < 2 ^ (prefixWord ++ tailWord_1689636).sum := by decide
  have hdescent : baseEnd_1689636 < baseStart_1689636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689650 : List Nat := [3, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_1689650 : Nat := 118140960795 + 1689650 * 2 ^ 59
def prefixEnd_1689650 : Nat := 4983230072969 + 3 ^ 40 * 1689650 * 2
def baseEnd_1689650 : Nat := 385601150164186431246421

theorem tailTrace_1689650 : CollatzResearch.WordTrace tailWord_1689650 prefixEnd_1689650 385601150164186431246421 := by
  unfold tailWord_1689650
  simp only [CollatzResearch.WordTrace]
  refine ⟨15406649582173523522734601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41084398885796062727292269 15406649582173523522734601)
  ·
    refine ⟨11554987186630142642050951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15406649582173523522734601 11554987186630142642050951)
    ·
      refine ⟨17332480779945213963076427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11554987186630142642050951 17332480779945213963076427)
      ·
        refine ⟨25998721169917820944614641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17332480779945213963076427 25998721169917820944614641)
        ·
          refine ⟨19499040877438365708460981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25998721169917820944614641 19499040877438365708460981)
          ·
            refine ⟨1828035082259846785168217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19499040877438365708460981 1828035082259846785168217)
            ·
              refine ⟨1371026311694885088876163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1828035082259846785168217 1371026311694885088876163)
              ·
                refine ⟨2056539467542327633314245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371026311694885088876163 2056539467542327633314245)
                ·
                  refine ⟨385601150164186431246421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2056539467542327633314245 385601150164186431246421)
                  ·
                    rfl

theorem cell21_1689650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_1689650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689650 prefixEnd_1689650 := by exact prefixLift 1689650
  have htrace : WordTrace (prefixWord ++ tailWord_1689650) baseStart_1689650 baseEnd_1689650 := by
    simpa [prefixWord, tailWord_1689650, baseEnd_1689650] using wordTrace_append hprefix tailTrace_1689650
  have hstable : (prefixWord ++ tailWord_1689650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689650).length < 2 ^ (prefixWord ++ tailWord_1689650).sum := by decide
  have hdescent : baseEnd_1689650 < baseStart_1689650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689661 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 7]
def baseStart_1689661 : Nat := 118140960795 + 1689661 * 2 ^ 59
def prefixEnd_1689661 : Nat := 4983230072969 + 3 ^ 40 * 1689661 * 2
def baseEnd_1689661 : Nat := 385603660514052856563065

theorem tailTrace_1689661 : CollatzResearch.WordTrace tailWord_1689661 prefixEnd_1689661 385603660514052856563065 := by
  unfold tailWord_1689661
  simp only [CollatzResearch.WordTrace]
  refine ⟨61626999531654242969588837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41084666354436161979725891 61626999531654242969588837)
  ·
    refine ⟨11555062412185170556797907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61626999531654242969588837 11555062412185170556797907)
    ·
      refine ⟨17332593618277755835196861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11555062412185170556797907 17332593618277755835196861)
      ·
        refine ⟨6499722606854158438198823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17332593618277755835196861 6499722606854158438198823)
        ·
          refine ⟨9749583910281237657298235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6499722606854158438198823 9749583910281237657298235)
          ·
            refine ⟨14624375865421856485947353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9749583910281237657298235 14624375865421856485947353)
            ·
              refine ⟨10968281899066392364460515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14624375865421856485947353 10968281899066392364460515)
              ·
                refine ⟨16452422848599588546690773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10968281899066392364460515 16452422848599588546690773)
                ·
                  refine ⟨385603660514052856563065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16452422848599588546690773 385603660514052856563065)
                  ·
                    rfl

theorem cell21_1689661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_1689661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689661 prefixEnd_1689661 := by exact prefixLift 1689661
  have htrace : WordTrace (prefixWord ++ tailWord_1689661) baseStart_1689661 baseEnd_1689661 := by
    simpa [prefixWord, tailWord_1689661, baseEnd_1689661] using wordTrace_append hprefix tailTrace_1689661
  have hstable : (prefixWord ++ tailWord_1689661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689661).length < 2 ^ (prefixWord ++ tailWord_1689661).sum := by decide
  have hdescent : baseEnd_1689661 < baseStart_1689661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689774 : List Nat := [4, 1, 4, 2, 1, 2, 2, 5]
def baseStart_1689774 : Nat := 118140960795 + 1689774 * 2 ^ 59
def prefixEnd_1689774 : Nat := 4983230072969 + 3 ^ 40 * 1689774 * 2
def baseEnd_1689774 : Nat := 128543149551196590393167

theorem tailTrace_1689774 : CollatzResearch.WordTrace tailWord_1689774 prefixEnd_1689774 128543149551196590393167 := by
  unfold tailWord_1689774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7703890122530607908556547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41087413986829908845634917 7703890122530607908556547)
  ·
    refine ⟨11555835183795911862834821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7703890122530607908556547 11555835183795911862834821)
    ·
      refine ⟨2166719096961733474281529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11555835183795911862834821 2166719096961733474281529)
      ·
        refine ⟨1625039322721300105711147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2166719096961733474281529 1625039322721300105711147)
        ·
          refine ⟨2437558984081950158566721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1625039322721300105711147 2437558984081950158566721)
          ·
            refine ⟨1828169238061462618925041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2437558984081950158566721 1828169238061462618925041)
            ·
              refine ⟨1371126928546096964193781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1828169238061462618925041 1371126928546096964193781)
              ·
                refine ⟨128543149551196590393167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1371126928546096964193781 128543149551196590393167)
                ·
                  rfl

theorem cell21_1689774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_1689774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689774 prefixEnd_1689774 := by exact prefixLift 1689774
  have htrace : WordTrace (prefixWord ++ tailWord_1689774) baseStart_1689774 baseEnd_1689774 := by
    simpa [prefixWord, tailWord_1689774, baseEnd_1689774] using wordTrace_append hprefix tailTrace_1689774
  have hstable : (prefixWord ++ tailWord_1689774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689774).length < 2 ^ (prefixWord ++ tailWord_1689774).sum := by decide
  have hdescent : baseEnd_1689774 < baseStart_1689774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689788 : List Nat := [2, 2, 2, 3, 3, 2, 1, 3, 3]
def baseStart_1689788 : Nat := 118140960795 + 1689788 * 2 ^ 59
def prefixEnd_1689788 : Nat := 4983230072969 + 3 ^ 40 * 1689788 * 2
def baseEnd_1689788 : Nat := 385632643644328857946139

theorem tailTrace_1689788 : CollatzResearch.WordTrace tailWord_1689788 prefixEnd_1689788 385632643644328857946139 := by
  unfold tailWord_1689788
  simp only [CollatzResearch.WordTrace]
  refine ⟨30815815801097071829731009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41087754401462762439641345 30815815801097071829731009)
  ·
    refine ⟨23111861850822803872298257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30815815801097071829731009 23111861850822803872298257)
    ·
      refine ⟨17333896388117102904223693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23111861850822803872298257 17333896388117102904223693)
      ·
        refine ⟨6500211145543913589083885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17333896388117102904223693 6500211145543913589083885)
        ·
          refine ⟨2437579179578967595906457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6500211145543913589083885 2437579179578967595906457)
          ·
            refine ⟨1828184384684225696929843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2437579179578967595906457 1828184384684225696929843)
            ·
              refine ⟨2742276577026338545394765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828184384684225696929843 2742276577026338545394765)
              ·
                refine ⟨1028353716384876954523037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2742276577026338545394765 1028353716384876954523037)
                ·
                  refine ⟨385632643644328857946139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1028353716384876954523037 385632643644328857946139)
                  ·
                    rfl

theorem cell21_1689788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_1689788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689788 prefixEnd_1689788 := by exact prefixLift 1689788
  have htrace : WordTrace (prefixWord ++ tailWord_1689788) baseStart_1689788 baseEnd_1689788 := by
    simpa [prefixWord, tailWord_1689788, baseEnd_1689788] using wordTrace_append hprefix tailTrace_1689788
  have hstable : (prefixWord ++ tailWord_1689788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689788).length < 2 ^ (prefixWord ++ tailWord_1689788).sum := by decide
  have hdescent : baseEnd_1689788 < baseStart_1689788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689864 : List Nat := [2, 1, 3, 2, 3, 3, 2, 2, 3]
def baseStart_1689864 : Nat := 118140960795 + 1689864 * 2 ^ 59
def prefixEnd_1689864 : Nat := 4983230072969 + 3 ^ 40 * 1689864 * 2
def baseEnd_1689864 : Nat := 385649987879769614679317

theorem tailTrace_1689864 : CollatzResearch.WordTrace tailWord_1689864 prefixEnd_1689864 385649987879769614679317 := by
  unfold tailWord_1689864
  simp only [CollatzResearch.WordTrace]
  refine ⟨30817201774959404319614323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41089602366612539092819097 30817201774959404319614323)
  ·
    refine ⟨46225802662439106479421485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30817201774959404319614323 46225802662439106479421485)
    ·
      refine ⟨17334675998414664929783057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46225802662439106479421485 17334675998414664929783057)
      ·
        refine ⟨13001006998810998697337293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17334675998414664929783057 13001006998810998697337293)
        ·
          refine ⟨4875377624554124511501485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13001006998810998697337293 4875377624554124511501485)
          ·
            refine ⟨1828266609207796691813057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4875377624554124511501485 1828266609207796691813057)
            ·
              refine ⟨1371199956905847518859793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1828266609207796691813057 1371199956905847518859793)
              ·
                refine ⟨1028399967679385639144845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371199956905847518859793 1028399967679385639144845)
                ·
                  refine ⟨385649987879769614679317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1028399967679385639144845 385649987879769614679317)
                  ·
                    rfl

theorem cell21_1689864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 3].length) (baseStart_1689864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689864 prefixEnd_1689864 := by exact prefixLift 1689864
  have htrace : WordTrace (prefixWord ++ tailWord_1689864) baseStart_1689864 baseEnd_1689864 := by
    simpa [prefixWord, tailWord_1689864, baseEnd_1689864] using wordTrace_append hprefix tailTrace_1689864
  have hstable : (prefixWord ++ tailWord_1689864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689864).length < 2 ^ (prefixWord ++ tailWord_1689864).sum := by decide
  have hdescent : baseEnd_1689864 < baseStart_1689864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689937 : List Nat := [1, 2, 2, 1, 4, 3, 3, 1, 4]
def baseStart_1689937 : Nat := 118140960795 + 1689937 * 2 ^ 59
def prefixEnd_1689937 : Nat := 4983230072969 + 3 ^ 40 * 1689937 * 2
def baseEnd_1689937 : Nat := 385666647474337709962501

theorem tailTrace_1689937 : CollatzResearch.WordTrace tailWord_1689937 prefixEnd_1689937 385666647474337709962501 := by
  unfold tailWord_1689937
  simp only [CollatzResearch.WordTrace]
  refine ⟨61637066078654342106636065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41091377385769561404424043 61637066078654342106636065)
  ·
    refine ⟨46227799558990756579977049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61637066078654342106636065 46227799558990756579977049)
    ·
      refine ⟨34670849669243067434982787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46227799558990756579977049 34670849669243067434982787)
      ·
        refine ⟨52006274503864601152474181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34670849669243067434982787 52006274503864601152474181)
        ·
          refine ⟨9751176469474612716088909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52006274503864601152474181 9751176469474612716088909)
          ·
            refine ⟨3656691176052979768533341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9751176469474612716088909 3656691176052979768533341)
            ·
              refine ⟨1371259191019867413200003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3656691176052979768533341 1371259191019867413200003)
              ·
                refine ⟨2056888786529801119800005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371259191019867413200003 2056888786529801119800005)
                ·
                  refine ⟨385666647474337709962501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2056888786529801119800005 385666647474337709962501)
                  ·
                    rfl

theorem cell21_1689937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_1689937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689937 prefixEnd_1689937 := by exact prefixLift 1689937
  have htrace : WordTrace (prefixWord ++ tailWord_1689937) baseStart_1689937 baseEnd_1689937 := by
    simpa [prefixWord, tailWord_1689937, baseEnd_1689937] using wordTrace_append hprefix tailTrace_1689937
  have hstable : (prefixWord ++ tailWord_1689937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689937).length < 2 ^ (prefixWord ++ tailWord_1689937).sum := by decide
  have hdescent : baseEnd_1689937 < baseStart_1689937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689979 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 6]
def baseStart_1689979 : Nat := 118140960795 + 1689979 * 2 ^ 59
def prefixEnd_1689979 : Nat := 4983230072969 + 3 ^ 40 * 1689979 * 2
def baseEnd_1689979 : Nat := 385676232446554970262415

theorem tailTrace_1689979 : CollatzResearch.WordTrace tailWord_1689979 prefixEnd_1689979 385676232446554970262415 := by
  unfold tailWord_1689979
  simp only [CollatzResearch.WordTrace]
  refine ⟨61638597944502183279664991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41092398629668122186443327 61638597944502183279664991)
  ·
    refine ⟨92457896916753274919497487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61638597944502183279664991 92457896916753274919497487)
    ·
      refine ⟨138686845375129912379246231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92457896916753274919497487 138686845375129912379246231)
      ·
        refine ⟨208030268062694868568869347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138686845375129912379246231 208030268062694868568869347)
        ·
          refine ⟨312045402094042302853304021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208030268062694868568869347 312045402094042302853304021)
          ·
            refine ⟨7313564111579116473124313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 312045402094042302853304021 7313564111579116473124313)
            ·
              refine ⟨5485173083684337354843235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7313564111579116473124313 5485173083684337354843235)
              ·
                refine ⟨8227759625526506032264853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5485173083684337354843235 8227759625526506032264853)
                ·
                  refine ⟨385676232446554970262415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8227759625526506032264853 385676232446554970262415)
                  ·
                    rfl

theorem cell21_1689979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 6].length) (baseStart_1689979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689979 prefixEnd_1689979 := by exact prefixLift 1689979
  have htrace : WordTrace (prefixWord ++ tailWord_1689979) baseStart_1689979 baseEnd_1689979 := by
    simpa [prefixWord, tailWord_1689979, baseEnd_1689979] using wordTrace_append hprefix tailTrace_1689979
  have hstable : (prefixWord ++ tailWord_1689979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689979).length < 2 ^ (prefixWord ++ tailWord_1689979).sum := by decide
  have hdescent : baseEnd_1689979 < baseStart_1689979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689996 : List Nat := [2, 2, 1, 2, 1, 5, 1, 3, 4]
def baseStart_1689996 : Nat := 118140960795 + 1689996 * 2 ^ 59
def prefixEnd_1689996 : Nat := 4983230072969 + 3 ^ 40 * 1689996 * 2
def baseEnd_1689996 : Nat := 385680112078166718479047

theorem tailTrace_1689996 : CollatzResearch.WordTrace tailWord_1689996 prefixEnd_1689996 385680112078166718479047 := by
  unfold tailWord_1689996
  simp only [CollatzResearch.WordTrace]
  refine ⟨30819608992720297591516921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41092811990293730122022561 30819608992720297591516921)
  ·
    refine ⟨23114706744540223193637691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30819608992720297591516921 23114706744540223193637691)
    ·
      refine ⟨34672060116810334790456537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23114706744540223193637691 34672060116810334790456537)
      ·
        refine ⟨26004045087607751092842403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34672060116810334790456537 26004045087607751092842403)
        ·
          refine ⟨39006067631411626639263605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26004045087607751092842403 39006067631411626639263605)
          ·
            refine ⟨3656818840444839997430963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39006067631411626639263605 3656818840444839997430963)
            ·
              refine ⟨5485228260667259996146445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656818840444839997430963 5485228260667259996146445)
              ·
                refine ⟨2056960597750222498554917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5485228260667259996146445 2056960597750222498554917)
                ·
                  refine ⟨385680112078166718479047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2056960597750222498554917 385680112078166718479047)
                  ·
                    rfl

theorem cell21_1689996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_1689996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1689996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1689996 prefixEnd_1689996 := by exact prefixLift 1689996
  have htrace : WordTrace (prefixWord ++ tailWord_1689996) baseStart_1689996 baseEnd_1689996 := by
    simpa [prefixWord, tailWord_1689996, baseEnd_1689996] using wordTrace_append hprefix tailTrace_1689996
  have hstable : (prefixWord ++ tailWord_1689996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689996).length < 2 ^ (prefixWord ++ tailWord_1689996).sum := by decide
  have hdescent : baseEnd_1689996 < baseStart_1689996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690010 : List Nat := [3, 1, 1, 4, 1, 2, 2, 7]
def baseStart_1690010 : Nat := 118140960795 + 1690010 * 2 ^ 59
def prefixEnd_1690010 : Nat := 4983230072969 + 3 ^ 40 * 1690010 * 2
def baseEnd_1690010 : Nat := 128561102356301935081895

theorem tailTrace_1690010 : CollatzResearch.WordTrace tailWord_1690010 prefixEnd_1690010 128561102356301935081895 := by
  unfold tailWord_1690010
  simp only [CollatzResearch.WordTrace]
  refine ⟨15409932151847468893510871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41093152404926583716028989 15409932151847468893510871)
  ·
    refine ⟨23114898227771203340266307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15409932151847468893510871 23114898227771203340266307)
    ·
      refine ⟨34672347341656805010399461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23114898227771203340266307 34672347341656805010399461)
      ·
        refine ⟨6501065126560650939449899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34672347341656805010399461 6501065126560650939449899)
        ·
          refine ⟨9751597689840976409174849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6501065126560650939449899 9751597689840976409174849)
          ·
            refine ⟨7313698267380732306881137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9751597689840976409174849 7313698267380732306881137)
            ·
              refine ⟨5485273700535549230160853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7313698267380732306881137 5485273700535549230160853)
              ·
                refine ⟨128561102356301935081895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5485273700535549230160853 128561102356301935081895)
                ·
                  rfl

theorem cell21_1690010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_1690010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690010 prefixEnd_1690010 := by exact prefixLift 1690010
  have htrace : WordTrace (prefixWord ++ tailWord_1690010) baseStart_1690010 baseEnd_1690010 := by
    simpa [prefixWord, tailWord_1690010, baseEnd_1690010] using wordTrace_append hprefix tailTrace_1690010
  have hstable : (prefixWord ++ tailWord_1690010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690010).length < 2 ^ (prefixWord ++ tailWord_1690010).sum := by decide
  have hdescent : baseEnd_1690010 < baseStart_1690010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690157 : List Nat := [1, 5, 4, 1, 2, 1, 2, 1, 4]
def baseStart_1690157 : Nat := 118140960795 + 1690157 * 2 ^ 59
def prefixEnd_1690157 : Nat := 4983230072969 + 3 ^ 40 * 1690157 * 2
def baseEnd_1690157 : Nat := 385716854471666216295385

theorem tailTrace_1690157 : CollatzResearch.WordTrace tailWord_1690157 prefixEnd_1690157 385716854471666216295385 := by
  unfold tailWord_1690157
  simp only [CollatzResearch.WordTrace]
  refine ⟨61645090137857319679644725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41096726758571546453096483 61645090137857319679644725)
  ·
    refine ⟨5779227200424123719966693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61645090137857319679644725 5779227200424123719966693)
    ·
      refine ⟨1083605100079523197493755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5779227200424123719966693 1083605100079523197493755)
      ·
        refine ⟨1625407650119284796240633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1083605100079523197493755 1625407650119284796240633)
        ·
          refine ⟨1219055737589463597180475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1625407650119284796240633 1219055737589463597180475)
          ·
            refine ⟨1828583606384195395770713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219055737589463597180475 1828583606384195395770713)
            ·
              refine ⟨1371437704788146546828035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1828583606384195395770713 1371437704788146546828035)
              ·
                refine ⟨2057156557182219820242053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371437704788146546828035 2057156557182219820242053)
                ·
                  refine ⟨385716854471666216295385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2057156557182219820242053 385716854471666216295385)
                  ·
                    rfl

theorem cell21_1690157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_1690157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690157 prefixEnd_1690157 := by exact prefixLift 1690157
  have htrace : WordTrace (prefixWord ++ tailWord_1690157) baseStart_1690157 baseEnd_1690157 := by
    simpa [prefixWord, tailWord_1690157, baseEnd_1690157] using wordTrace_append hprefix tailTrace_1690157
  have hstable : (prefixWord ++ tailWord_1690157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690157).length < 2 ^ (prefixWord ++ tailWord_1690157).sum := by decide
  have hdescent : baseEnd_1690157 < baseStart_1690157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690176 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 5]
def baseStart_1690176 : Nat := 118140960795 + 1690176 * 2 ^ 59
def prefixEnd_1690176 : Nat := 4983230072969 + 3 ^ 40 * 1690176 * 2
def baseEnd_1690176 : Nat := 385721190530526405478679

theorem tailTrace_1690176 : CollatzResearch.WordTrace tailWord_1690176 prefixEnd_1690176 385721190530526405478679 := by
  unfold tailWord_1690176
  simp only [CollatzResearch.WordTrace]
  refine ⟨30822891562394242962293191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41097188749858990616390921 30822891562394242962293191)
  ·
    refine ⟨46234337343591364443439787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30822891562394242962293191 46234337343591364443439787)
    ·
      refine ⟨69351506015387046665159681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46234337343591364443439787 69351506015387046665159681)
      ·
        refine ⟨52013629511540284998869761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69351506015387046665159681 52013629511540284998869761)
        ·
          refine ⟨39010222133655213749152321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52013629511540284998869761 39010222133655213749152321)
          ·
            refine ⟨29257666600241410311864241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39010222133655213749152321 29257666600241410311864241)
            ·
              refine ⟨21943249950181057733898181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29257666600241410311864241 21943249950181057733898181)
              ·
                refine ⟨4114359365658948325105909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21943249950181057733898181 4114359365658948325105909)
                ·
                  refine ⟨385721190530526405478679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4114359365658948325105909 385721190530526405478679)
                  ·
                    rfl

theorem cell21_1690176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_1690176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690176 prefixEnd_1690176 := by exact prefixLift 1690176
  have htrace : WordTrace (prefixWord ++ tailWord_1690176) baseStart_1690176 baseEnd_1690176 := by
    simpa [prefixWord, tailWord_1690176, baseEnd_1690176] using wordTrace_append hprefix tailTrace_1690176
  have hstable : (prefixWord ++ tailWord_1690176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690176).length < 2 ^ (prefixWord ++ tailWord_1690176).sum := by decide
  have hdescent : baseEnd_1690176 < baseStart_1690176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690286 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_1690286 : Nat := 118140960795 + 1690286 * 2 ^ 59
def prefixEnd_1690286 : Nat := 4983230072969 + 3 ^ 40 * 1690286 * 2
def baseEnd_1690286 : Nat := 385746294029190658645121

theorem tailTrace_1690286 : CollatzResearch.WordTrace tailWord_1690286 prefixEnd_1690286 385746294029190658645121 := by
  unfold tailWord_1690286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7706224394298746838886339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41099863436259983140727141 7706224394298746838886339)
  ·
    refine ⟨11559336591448120258329509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7706224394298746838886339 11559336591448120258329509)
    ·
      refine ⟨2167375610896522548436783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11559336591448120258329509 2167375610896522548436783)
      ·
        refine ⟨3251063416344783822655175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167375610896522548436783 3251063416344783822655175)
        ·
          refine ⟨4876595124517175733982763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3251063416344783822655175 4876595124517175733982763)
          ·
            refine ⟨7314892686775763600974145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4876595124517175733982763 7314892686775763600974145)
            ·
              refine ⟨5486169515081822700730609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7314892686775763600974145 5486169515081822700730609)
              ·
                refine ⟨4114627136311367025547957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5486169515081822700730609 4114627136311367025547957)
                ·
                  refine ⟨385746294029190658645121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4114627136311367025547957 385746294029190658645121)
                  ·
                    rfl

theorem cell21_1690286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_1690286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690286 prefixEnd_1690286 := by exact prefixLift 1690286
  have htrace : WordTrace (prefixWord ++ tailWord_1690286) baseStart_1690286 baseEnd_1690286 := by
    simpa [prefixWord, tailWord_1690286, baseEnd_1690286] using wordTrace_append hprefix tailTrace_1690286
  have hstable : (prefixWord ++ tailWord_1690286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690286).length < 2 ^ (prefixWord ++ tailWord_1690286).sum := by decide
  have hdescent : baseEnd_1690286 < baseStart_1690286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690289 : List Nat := [1, 2, 2, 6, 2, 1, 2, 5]
def baseStart_1690289 : Nat := 118140960795 + 1690289 * 2 ^ 59
def prefixEnd_1690289 : Nat := 4983230072969 + 3 ^ 40 * 1690289 * 2
def baseEnd_1690289 : Nat := 128582326223354440031705

theorem tailTrace_1690289 : CollatzResearch.WordTrace tailWord_1690289 prefixEnd_1690289 128582326223354440031705 := by
  unfold tailWord_1690289
  simp only [CollatzResearch.WordTrace]
  refine ⟨61649904573379106223449921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41099936382252737482299947 61649904573379106223449921)
  ·
    refine ⟨46237428430034329667587441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61649904573379106223449921 46237428430034329667587441)
    ·
      refine ⟨34678071322525747250690581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46237428430034329667587441 34678071322525747250690581)
      ·
        refine ⟨1625534593243394402376121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34678071322525747250690581 1625534593243394402376121)
        ·
          refine ⟨1219150944932545801782091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1625534593243394402376121 1219150944932545801782091)
          ·
            refine ⟨1828726417398818702673137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219150944932545801782091 1828726417398818702673137)
            ·
              refine ⟨1371544813049114027004853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1828726417398818702673137 1371544813049114027004853)
              ·
                refine ⟨128582326223354440031705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1371544813049114027004853 128582326223354440031705)
                ·
                  rfl

theorem cell21_1690289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 5].length) (baseStart_1690289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690289 prefixEnd_1690289 := by exact prefixLift 1690289
  have htrace : WordTrace (prefixWord ++ tailWord_1690289) baseStart_1690289 baseEnd_1690289 := by
    simpa [prefixWord, tailWord_1690289, baseEnd_1690289] using wordTrace_append hprefix tailTrace_1690289
  have hstable : (prefixWord ++ tailWord_1690289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690289).length < 2 ^ (prefixWord ++ tailWord_1690289).sum := by decide
  have hdescent : baseEnd_1690289 < baseStart_1690289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690314 : List Nat := [3, 1, 2, 1, 4, 3, 7]
def baseStart_1690314 : Nat := 118140960795 + 1690314 * 2 ^ 59
def prefixEnd_1690314 : Nat := 4983230072969 + 3 ^ 40 * 1690314 * 2
def baseEnd_1690314 : Nat := 42861409334518759130933

theorem tailTrace_1690314 : CollatzResearch.WordTrace tailWord_1690314 prefixEnd_1690314 42861409334518759130933 := by
  unfold tailWord_1690314
  simp only [CollatzResearch.WordTrace]
  refine ⟨15412704099572133873277499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41100544265525690328739997 15412704099572133873277499)
  ·
    refine ⟨23119056149358200809916249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15412704099572133873277499 23119056149358200809916249)
    ·
      refine ⟨17339292112018650607437187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23119056149358200809916249 17339292112018650607437187)
      ·
        refine ⟨26008938168027975911155781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17339292112018650607437187 26008938168027975911155781)
        ·
          refine ⟨4876675906505245483341709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26008938168027975911155781 4876675906505245483341709)
          ·
            refine ⟨1828753464939467056253141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4876675906505245483341709 1828753464939467056253141)
            ·
              refine ⟨42861409334518759130933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1828753464939467056253141 42861409334518759130933)
              ·
                rfl

theorem cell21_1690314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 7].length) (baseStart_1690314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690314 prefixEnd_1690314 := by exact prefixLift 1690314
  have htrace : WordTrace (prefixWord ++ tailWord_1690314) baseStart_1690314 baseEnd_1690314 := by
    simpa [prefixWord, tailWord_1690314, baseEnd_1690314] using wordTrace_append hprefix tailTrace_1690314
  have hstable : (prefixWord ++ tailWord_1690314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690314).length < 2 ^ (prefixWord ++ tailWord_1690314).sum := by decide
  have hdescent : baseEnd_1690314 < baseStart_1690314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690376 : List Nat := [2, 1, 3, 2, 2, 3, 2, 2, 4]
def baseStart_1690376 : Nat := 118140960795 + 1690376 * 2 ^ 59
def prefixEnd_1690376 : Nat := 4983230072969 + 3 ^ 40 * 1690376 * 2
def baseEnd_1690376 : Nat := 385766833255370502144937

theorem tailTrace_1690376 : CollatzResearch.WordTrace tailWord_1690376 prefixEnd_1690376 385766833255370502144937 := by
  unfold tailWord_1690376
  simp only [CollatzResearch.WordTrace]
  refine ⟨30826538862031960040933491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41102051816042613387911321 30826538862031960040933491)
  ·
    refine ⟨46239808293047940061400237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30826538862031960040933491 46239808293047940061400237)
    ·
      refine ⟨17339928109892977523025089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46239808293047940061400237 17339928109892977523025089)
      ·
        refine ⟨13004946082419733142268817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17339928109892977523025089 13004946082419733142268817)
        ·
          refine ⟨9753709561814799856701613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13004946082419733142268817 9753709561814799856701613)
          ·
            refine ⟨3657641085680549946263105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9753709561814799856701613 3657641085680549946263105)
            ·
              refine ⟨2743230814260412459697329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3657641085680549946263105 2743230814260412459697329)
              ·
                refine ⟨2057423110695309344772997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2743230814260412459697329 2057423110695309344772997)
                ·
                  refine ⟨385766833255370502144937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2057423110695309344772997 385766833255370502144937)
                  ·
                    rfl

theorem cell21_1690376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_1690376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690376 prefixEnd_1690376 := by exact prefixLift 1690376
  have htrace : WordTrace (prefixWord ++ tailWord_1690376) baseStart_1690376 baseEnd_1690376 := by
    simpa [prefixWord, tailWord_1690376, baseEnd_1690376] using wordTrace_append hprefix tailTrace_1690376
  have hstable : (prefixWord ++ tailWord_1690376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690376).length < 2 ^ (prefixWord ++ tailWord_1690376).sum := by decide
  have hdescent : baseEnd_1690376 < baseStart_1690376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690525 : List Nat := [1, 4, 2, 1, 2, 1, 1, 9]
def baseStart_1690525 : Nat := 118140960795 + 1690525 * 2 ^ 59
def prefixEnd_1690525 : Nat := 4983230072969 + 3 ^ 40 * 1690525 * 2
def baseEnd_1690525 : Nat := 128600279028459784720433

theorem tailTrace_1690525 : CollatzResearch.WordTrace tailWord_1690525 prefixEnd_1690525 128600279028459784720433 := by
  unfold tailWord_1690525
  simp only [CollatzResearch.WordTrace]
  refine ⟨61658512200524118529041029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41105674800349412352694019 61658512200524118529041029)
  ·
    refine ⟨11560971037598272224195193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61658512200524118529041029 11560971037598272224195193)
    ·
      refine ⟨8670728278198704168146395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11560971037598272224195193 8670728278198704168146395)
      ·
        refine ⟨13006092417298056252219593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8670728278198704168146395 13006092417298056252219593)
        ·
          refine ⟨9754569312973542189164695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13006092417298056252219593 9754569312973542189164695)
          ·
            refine ⟨14631853969460313283747043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9754569312973542189164695 14631853969460313283747043)
            ·
              refine ⟨21947780954190469925620565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14631853969460313283747043 21947780954190469925620565)
              ·
                refine ⟨128600279028459784720433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21947780954190469925620565 128600279028459784720433)
                ·
                  rfl

theorem cell21_1690525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 9].length) (baseStart_1690525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690525 prefixEnd_1690525 := by exact prefixLift 1690525
  have htrace : WordTrace (prefixWord ++ tailWord_1690525) baseStart_1690525 baseEnd_1690525 := by
    simpa [prefixWord, tailWord_1690525, baseEnd_1690525] using wordTrace_append hprefix tailTrace_1690525
  have hstable : (prefixWord ++ tailWord_1690525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690525).length < 2 ^ (prefixWord ++ tailWord_1690525).sum := by decide
  have hdescent : baseEnd_1690525 < baseStart_1690525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690539 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 7]
def baseStart_1690539 : Nat := 118140960795 + 1690539 * 2 ^ 59
def prefixEnd_1690539 : Nat := 4983230072969 + 3 ^ 40 * 1690539 * 2
def baseEnd_1690539 : Nat := 385804032076118440927937

theorem tailTrace_1690539 : CollatzResearch.WordTrace tailWord_1690539 prefixEnd_1690539 385804032076118440927937 := by
  unfold tailWord_1690539
  simp only [CollatzResearch.WordTrace]
  refine ⟨61659022822473398920050671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41106015214982265946700447 61659022822473398920050671)
  ·
    refine ⟨92488534233710098380076007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61659022822473398920050671 92488534233710098380076007)
    ·
      refine ⟨138732801350565147570114011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92488534233710098380076007 138732801350565147570114011)
      ·
        refine ⟨208099202025847721355171017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138732801350565147570114011 208099202025847721355171017)
        ·
          refine ⟨156074401519385791016378263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208099202025847721355171017 156074401519385791016378263)
          ·
            refine ⟨234111602279078686524567395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156074401519385791016378263 234111602279078686524567395)
            ·
              refine ⟨351167403418618029786851093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234111602279078686524567395 351167403418618029786851093)
              ·
                refine ⟨16460972035247720146258645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 351167403418618029786851093 16460972035247720146258645)
                ·
                  refine ⟨385804032076118440927937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16460972035247720146258645 385804032076118440927937)
                  ·
                    rfl

theorem cell21_1690539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_1690539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690539 prefixEnd_1690539 := by exact prefixLift 1690539
  have htrace : WordTrace (prefixWord ++ tailWord_1690539) baseStart_1690539 baseEnd_1690539 := by
    simpa [prefixWord, tailWord_1690539, baseEnd_1690539] using wordTrace_append hprefix tailTrace_1690539
  have hstable : (prefixWord ++ tailWord_1690539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690539).length < 2 ^ (prefixWord ++ tailWord_1690539).sum := by decide
  have hdescent : baseEnd_1690539 < baseStart_1690539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690542 : List Nat := [4, 1, 5, 11]
def baseStart_1690542 : Nat := 118140960795 + 1690542 * 2 ^ 59
def prefixEnd_1690542 : Nat := 4983230072969 + 3 ^ 40 * 1690542 * 2
def baseEnd_1690542 : Nat := 1587673731345642396617

theorem tailTrace_1690542 : CollatzResearch.WordTrace tailWord_1690542 prefixEnd_1690542 1587673731345642396617 := by
  unfold tailWord_1690542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7707391530182816304051235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41106088160975020288273253 7707391530182816304051235)
  ·
    refine ⟨11561087295274224456076853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7707391530182816304051235 11561087295274224456076853)
    ·
      refine ⟨1083851933931958542757205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11561087295274224456076853 1083851933931958542757205)
      ·
        refine ⟨1587673731345642396617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1083851933931958542757205 1587673731345642396617)
        ·
          rfl

theorem cell21_1690542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 11].length) (baseStart_1690542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690542 prefixEnd_1690542 := by exact prefixLift 1690542
  have htrace : WordTrace (prefixWord ++ tailWord_1690542) baseStart_1690542 baseEnd_1690542 := by
    simpa [prefixWord, tailWord_1690542, baseEnd_1690542] using wordTrace_append hprefix tailTrace_1690542
  have hstable : (prefixWord ++ tailWord_1690542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690542).length < 2 ^ (prefixWord ++ tailWord_1690542).sum := by decide
  have hdescent : baseEnd_1690542 < baseStart_1690542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690548 : List Nat := [2, 5, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1690548 : Nat := 118140960795 + 1690548 * 2 ^ 59
def prefixEnd_1690548 : Nat := 4983230072969 + 3 ^ 40 * 1690548 * 2
def baseEnd_1690548 : Nat := 385806085998736425277919

theorem tailTrace_1690548 : CollatzResearch.WordTrace tailWord_1690548 prefixEnd_1690548 385806085998736425277919 := by
  unfold tailWord_1690548
  simp only [CollatzResearch.WordTrace]
  refine ⟨30829675539720396728564149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41106234052960528971418865 30829675539720396728564149)
  ·
    refine ⟨2890282081848787193302889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30829675539720396728564149 2890282081848787193302889)
    ·
      refine ⟨2167711561386590394977167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2890282081848787193302889 2167711561386590394977167)
      ·
        refine ⟨3251567342079885592465751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167711561386590394977167 3251567342079885592465751)
        ·
          refine ⟨4877351013119828388698627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3251567342079885592465751 4877351013119828388698627)
          ·
            refine ⟨7316026519679742583047941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4877351013119828388698627 7316026519679742583047941)
            ·
              refine ⟨1371754972439951734321489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7316026519679742583047941 1371754972439951734321489)
              ·
                refine ⟨1028816229329963800741117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371754972439951734321489 1028816229329963800741117)
                ·
                  refine ⟨385806085998736425277919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1028816229329963800741117 385806085998736425277919)
                  ·
                    rfl

theorem cell21_1690548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1690548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690548 prefixEnd_1690548 := by exact prefixLift 1690548
  have htrace : WordTrace (prefixWord ++ tailWord_1690548) baseStart_1690548 baseEnd_1690548 := by
    simpa [prefixWord, tailWord_1690548, baseEnd_1690548] using wordTrace_append hprefix tailTrace_1690548
  have hstable : (prefixWord ++ tailWord_1690548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690548).length < 2 ^ (prefixWord ++ tailWord_1690548).sum := by decide
  have hdescent : baseEnd_1690548 < baseStart_1690548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690570 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_1690570 : Nat := 118140960795 + 1690570 * 2 ^ 59
def prefixEnd_1690570 : Nat := 4983230072969 + 3 ^ 40 * 1690570 * 2
def baseEnd_1690570 : Nat := 385811106698469275911207

theorem tailTrace_1690570 : CollatzResearch.WordTrace tailWord_1690570 prefixEnd_1690570 385811106698469275911207 := by
  unfold tailWord_1690570
  simp only [CollatzResearch.WordTrace]
  refine ⟨15415038371340272803607291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41106768990240727476286109 15415038371340272803607291)
  ·
    refine ⟨23122557557010409205410937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15415038371340272803607291 23122557557010409205410937)
    ·
      refine ⟨17341918167757806904058203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23122557557010409205410937 17341918167757806904058203)
      ·
        refine ⟨26012877251636710356087305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17341918167757806904058203 26012877251636710356087305)
        ·
          refine ⟨19509657938727532767065479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26012877251636710356087305 19509657938727532767065479)
          ·
            refine ⟨29264486908091299150598219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19509657938727532767065479 29264486908091299150598219)
            ·
              refine ⟨43896730362136948725897329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29264486908091299150598219 43896730362136948725897329)
              ·
                refine ⟨32922547771602711544422997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43896730362136948725897329 32922547771602711544422997)
                ·
                  refine ⟨385811106698469275911207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32922547771602711544422997 385811106698469275911207)
                  ·
                    rfl

theorem cell21_1690570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_1690570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690570 prefixEnd_1690570 := by exact prefixLift 1690570
  have htrace : WordTrace (prefixWord ++ tailWord_1690570) baseStart_1690570 baseEnd_1690570 := by
    simpa [prefixWord, tailWord_1690570, baseEnd_1690570] using wordTrace_append hprefix tailTrace_1690570
  have hstable : (prefixWord ++ tailWord_1690570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690570).length < 2 ^ (prefixWord ++ tailWord_1690570).sum := by decide
  have hdescent : baseEnd_1690570 < baseStart_1690570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690632 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 5]
def baseStart_1690632 : Nat := 118140960795 + 1690632 * 2 ^ 59
def prefixEnd_1690632 : Nat := 4983230072969 + 3 ^ 40 * 1690632 * 2
def baseEnd_1690632 : Nat := 385825255943170945877747

theorem tailTrace_1690632 : CollatzResearch.WordTrace tailWord_1690632 prefixEnd_1690632 385825255943170945877747 := by
  unfold tailWord_1690632
  simp only [CollatzResearch.WordTrace]
  refine ⟨30831207405568237901593075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41108276540757650535457433 30831207405568237901593075)
  ·
    refine ⟨46246811108352356852389613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30831207405568237901593075 46246811108352356852389613)
    ·
      refine ⟨17342554165632133819646105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46246811108352356852389613 17342554165632133819646105)
      ·
        refine ⟨13006915624224100364734579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17342554165632133819646105 13006915624224100364734579)
        ·
          refine ⟨19510373436336150547101869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13006915624224100364734579 19510373436336150547101869)
          ·
            refine ⟨7316390038626056455163201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19510373436336150547101869 7316390038626056455163201)
            ·
              refine ⟨5487292528969542341372401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7316390038626056455163201 5487292528969542341372401)
              ·
                refine ⟨4115469396727156756029301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5487292528969542341372401 4115469396727156756029301)
                ·
                  refine ⟨385825255943170945877747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4115469396727156756029301 385825255943170945877747)
                  ·
                    rfl

theorem cell21_1690632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_1690632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690632 prefixEnd_1690632 := by exact prefixLift 1690632
  have htrace : WordTrace (prefixWord ++ tailWord_1690632) baseStart_1690632 baseEnd_1690632 := by
    simpa [prefixWord, tailWord_1690632, baseEnd_1690632] using wordTrace_append hprefix tailTrace_1690632
  have hstable : (prefixWord ++ tailWord_1690632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690632).length < 2 ^ (prefixWord ++ tailWord_1690632).sum := by decide
  have hdescent : baseEnd_1690632 < baseStart_1690632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690649 : List Nat := [1, 2, 1, 2, 1, 1, 7, 3, 3]
def baseStart_1690649 : Nat := 118140960795 + 1690649 * 2 ^ 59
def prefixEnd_1690649 : Nat := 4983230072969 + 3 ^ 40 * 1690649 * 2
def baseEnd_1690649 : Nat := 385829135574782694094379

theorem tailTrace_1690649 : CollatzResearch.WordTrace tailWord_1690649 prefixEnd_1690649 385829135574782694094379 := by
  unfold tailWord_1690649
  simp only [CollatzResearch.WordTrace]
  refine ⟨61663034852074887706555001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41108689901383258471036667 61663034852074887706555001)
  ·
    refine ⟨46247276139056165779916251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61663034852074887706555001 46247276139056165779916251)
    ·
      refine ⟨69370914208584248669874377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46247276139056165779916251 69370914208584248669874377)
      ·
        refine ⟨52028185656438186502405783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69370914208584248669874377 52028185656438186502405783)
        ·
          refine ⟨78042278484657279753608675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52028185656438186502405783 78042278484657279753608675)
          ·
            refine ⟨117063417726985919630413013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78042278484657279753608675 117063417726985919630413013)
            ·
              refine ⟨2743673852976232491337805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 117063417726985919630413013 2743673852976232491337805)
              ·
                refine ⟨1028877694866087184251677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2743673852976232491337805 1028877694866087184251677)
                ·
                  refine ⟨385829135574782694094379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1028877694866087184251677 385829135574782694094379)
                  ·
                    rfl

theorem cell21_1690649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 3].length) (baseStart_1690649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690649 prefixEnd_1690649 := by exact prefixLift 1690649
  have htrace : WordTrace (prefixWord ++ tailWord_1690649) baseStart_1690649 baseEnd_1690649 := by
    simpa [prefixWord, tailWord_1690649, baseEnd_1690649] using wordTrace_append hprefix tailTrace_1690649
  have hstable : (prefixWord ++ tailWord_1690649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690649).length < 2 ^ (prefixWord ++ tailWord_1690649).sum := by decide
  have hdescent : baseEnd_1690649 < baseStart_1690649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690666 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_1690666 : Nat := 118140960795 + 1690666 * 2 ^ 59
def prefixEnd_1690666 : Nat := 4983230072969 + 3 ^ 40 * 1690666 * 2
def baseEnd_1690666 : Nat := 385833015206394442311011

theorem tailTrace_1690666 : CollatzResearch.WordTrace tailWord_1690666 prefixEnd_1690666 385833015206394442311011 := by
  unfold tailWord_1690666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15415913723253324902480963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41109103262008866406615901 15415913723253324902480963)
  ·
    refine ⟨23123870584879987353721445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15415913723253324902480963 23123870584879987353721445)
    ·
      refine ⟨4335725734664997628822771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23123870584879987353721445 4335725734664997628822771)
      ·
        refine ⟨6503588601997496443234157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4335725734664997628822771 6503588601997496443234157)
        ·
          refine ⟨2438845725749061166212809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6503588601997496443234157 2438845725749061166212809)
          ·
            refine ⟨1829134294311795874659607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2438845725749061166212809 1829134294311795874659607)
            ·
              refine ⟨2743701441467693811989411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829134294311795874659607 2743701441467693811989411)
              ·
                refine ⟨4115552162201540717984117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743701441467693811989411 4115552162201540717984117)
                ·
                  refine ⟨385833015206394442311011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4115552162201540717984117 385833015206394442311011)
                  ·
                    rfl

theorem cell21_1690666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_1690666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690666 prefixEnd_1690666 := by exact prefixLift 1690666
  have htrace : WordTrace (prefixWord ++ tailWord_1690666) baseStart_1690666 baseEnd_1690666 := by
    simpa [prefixWord, tailWord_1690666, baseEnd_1690666] using wordTrace_append hprefix tailTrace_1690666
  have hstable : (prefixWord ++ tailWord_1690666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690666).length < 2 ^ (prefixWord ++ tailWord_1690666).sum := by decide
  have hdescent : baseEnd_1690666 < baseStart_1690666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690680 : List Nat := [2, 1, 2, 1, 5, 1, 4, 1, 4]
def baseStart_1690680 : Nat := 118140960795 + 1690680 * 2 ^ 59
def prefixEnd_1690680 : Nat := 4983230072969 + 3 ^ 40 * 1690680 * 2
def baseEnd_1690680 : Nat := 385836210197133529077649

theorem tailTrace_1690680 : CollatzResearch.WordTrace tailWord_1690680 prefixEnd_1690680 385836210197133529077649 := by
  unfold tailWord_1690680
  simp only [CollatzResearch.WordTrace]
  refine ⟨30832082757481290000466747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41109443676641720000622329 30832082757481290000466747)
  ·
    refine ⟨46248124136221935000700121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30832082757481290000466747 46248124136221935000700121)
    ·
      refine ⟨34686093102166451250525091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46248124136221935000700121 34686093102166451250525091)
      ·
        refine ⟨52029139653249676875787637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34686093102166451250525091 52029139653249676875787637)
        ·
          refine ⟨4877731842492157207105091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52029139653249676875787637 4877731842492157207105091)
          ·
            refine ⟨7316597763738235810657637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4877731842492157207105091 7316597763738235810657637)
            ·
              refine ⟨1371862080700919214498307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7316597763738235810657637 1371862080700919214498307)
              ·
                refine ⟨2057793121051378821747461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371862080700919214498307 2057793121051378821747461)
                ·
                  refine ⟨385836210197133529077649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2057793121051378821747461 385836210197133529077649)
                  ·
                    rfl

theorem cell21_1690680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_1690680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690680 prefixEnd_1690680 := by exact prefixLift 1690680
  have htrace : WordTrace (prefixWord ++ tailWord_1690680) baseStart_1690680 baseEnd_1690680 := by
    simpa [prefixWord, tailWord_1690680, baseEnd_1690680] using wordTrace_append hprefix tailTrace_1690680
  have hstable : (prefixWord ++ tailWord_1690680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690680).length < 2 ^ (prefixWord ++ tailWord_1690680).sum := by decide
  have hdescent : baseEnd_1690680 < baseStart_1690680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690691 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 7]
def baseStart_1690691 : Nat := 118140960795 + 1690691 * 2 ^ 59
def prefixEnd_1690691 : Nat := 4983230072969 + 3 ^ 40 * 1690691 * 2
def baseEnd_1690691 : Nat := 385838720546999954394293

theorem tailTrace_1690691 : CollatzResearch.WordTrace tailWord_1690691 prefixEnd_1690691 385838720546999954394293 := by
  unfold tailWord_1690691
  simp only [CollatzResearch.WordTrace]
  refine ⟨61664566717922728879583927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41109711145281819253055951 61664566717922728879583927)
  ·
    refine ⟨92496850076884093319375891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61664566717922728879583927 92496850076884093319375891)
    ·
      refine ⟨138745275115326139979063837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92496850076884093319375891 138745275115326139979063837)
      ·
        refine ⟨52029478168247302492148939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138745275115326139979063837 52029478168247302492148939)
        ·
          refine ⟨78044217252370953738223409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52029478168247302492148939 78044217252370953738223409)
          ·
            refine ⟨58533162939278215303667557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78044217252370953738223409 58533162939278215303667557)
            ·
              refine ⟨10974968051114665369437667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58533162939278215303667557 10974968051114665369437667)
              ·
                refine ⟨16462452076671998054156501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10974968051114665369437667 16462452076671998054156501)
                ·
                  refine ⟨385838720546999954394293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16462452076671998054156501 385838720546999954394293)
                  ·
                    rfl

theorem cell21_1690691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_1690691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690691 prefixEnd_1690691 := by exact prefixLift 1690691
  have htrace : WordTrace (prefixWord ++ tailWord_1690691) baseStart_1690691 baseEnd_1690691 := by
    simpa [prefixWord, tailWord_1690691, baseEnd_1690691] using wordTrace_append hprefix tailTrace_1690691
  have hstable : (prefixWord ++ tailWord_1690691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690691).length < 2 ^ (prefixWord ++ tailWord_1690691).sum := by decide
  have hdescent : baseEnd_1690691 < baseStart_1690691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690717 : List Nat := [1, 4, 4, 1, 3, 1, 2, 2, 3]
def baseStart_1690717 : Nat := 118140960795 + 1690717 * 2 ^ 59
def prefixEnd_1690717 : Nat := 4983230072969 + 3 ^ 40 * 1690717 * 2
def baseEnd_1690717 : Nat := 385844654101229686960907

theorem tailTrace_1690717 : CollatzResearch.WordTrace tailWord_1690717 prefixEnd_1690717 385844654101229686960907 := by
  unfold tailWord_1690717
  simp only [CollatzResearch.WordTrace]
  refine ⟨61665515015828535320030405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41110343343885690213353603 61665515015828535320030405)
  ·
    refine ⟨11562284065467850372505701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61665515015828535320030405 11562284065467850372505701)
    ·
      refine ⟨2167928262275221944844819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11562284065467850372505701 2167928262275221944844819)
      ·
        refine ⟨3251892393412832917267229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167928262275221944844819 3251892393412832917267229)
        ·
          refine ⟨1219459647529812343975211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3251892393412832917267229 1219459647529812343975211)
          ·
            refine ⟨1829189471294718515962817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219459647529812343975211 1829189471294718515962817)
            ·
              refine ⟨1371892103471038886972113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829189471294718515962817 1371892103471038886972113)
              ·
                refine ⟨1028919077603279165229085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371892103471038886972113 1028919077603279165229085)
                ·
                  refine ⟨385844654101229686960907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1028919077603279165229085 385844654101229686960907)
                  ·
                    rfl

theorem cell21_1690717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_1690717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690717 prefixEnd_1690717 := by exact prefixLift 1690717
  have htrace : WordTrace (prefixWord ++ tailWord_1690717) baseStart_1690717 baseEnd_1690717 := by
    simpa [prefixWord, tailWord_1690717, baseEnd_1690717] using wordTrace_append hprefix tailTrace_1690717
  have hstable : (prefixWord ++ tailWord_1690717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690717).length < 2 ^ (prefixWord ++ tailWord_1690717).sum := by decide
  have hdescent : baseEnd_1690717 < baseStart_1690717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690725 : List Nat := [1, 3, 1, 3, 2, 1, 3, 4, 3]
def baseStart_1690725 : Nat := 118140960795 + 1690725 * 2 ^ 59
def prefixEnd_1690725 : Nat := 4983230072969 + 3 ^ 40 * 1690725 * 2
def baseEnd_1690725 : Nat := 385846479810223450827557

theorem tailTrace_1690725 : CollatzResearch.WordTrace tailWord_1690725 prefixEnd_1690725 385846479810223450827557 := by
  unfold tailWord_1690725
  simp only [CollatzResearch.WordTrace]
  refine ⟨61665806799799552686321629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41110537866533035124214419 61665806799799552686321629)
  ·
    refine ⟨23124677549924832257370611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61665806799799552686321629 23124677549924832257370611)
    ·
      refine ⟨34687016324887248386055917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23124677549924832257370611 34687016324887248386055917)
      ·
        refine ⟨13007631121832718144770969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34687016324887248386055917 13007631121832718144770969)
        ·
          refine ⟨9755723341374538608578227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13007631121832718144770969 9755723341374538608578227)
          ·
            refine ⟨14633585012061807912867341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9755723341374538608578227 14633585012061807912867341)
            ·
              refine ⟨5487594379523177967325253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14633585012061807912867341 5487594379523177967325253)
              ·
                refine ⟨1028923946160595868873485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5487594379523177967325253 1028923946160595868873485)
                ·
                  refine ⟨385846479810223450827557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1028923946160595868873485 385846479810223450827557)
                  ·
                    rfl

theorem cell21_1690725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_1690725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690725 prefixEnd_1690725 := by exact prefixLift 1690725
  have htrace : WordTrace (prefixWord ++ tailWord_1690725) baseStart_1690725 baseEnd_1690725 := by
    simpa [prefixWord, tailWord_1690725, baseEnd_1690725] using wordTrace_append hprefix tailTrace_1690725
  have hstable : (prefixWord ++ tailWord_1690725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690725).length < 2 ^ (prefixWord ++ tailWord_1690725).sum := by decide
  have hdescent : baseEnd_1690725 < baseStart_1690725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690728 : List Nat := [2, 1, 4, 4, 2, 1, 1, 6]
def baseStart_1690728 : Nat := 118140960795 + 1690728 * 2 ^ 59
def prefixEnd_1690728 : Nat := 4983230072969 + 3 ^ 40 * 1690728 * 2
def baseEnd_1690728 : Nat := 128615721483698704092517

theorem tailTrace_1690728 : CollatzResearch.WordTrace tailWord_1690728 prefixEnd_1690728 128615721483698704092517 := by
  unfold tailWord_1690728
  simp only [CollatzResearch.WordTrace]
  refine ⟨30832958109394342099340419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41110610812525789465787225 30832958109394342099340419)
  ·
    refine ⟨46249437164091513149010629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30832958109394342099340419 46249437164091513149010629)
    ·
      refine ⟨8671769468267158715439493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46249437164091513149010629 8671769468267158715439493)
      ·
        refine ⟨1625956775300092259144905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8671769468267158715439493 1625956775300092259144905)
        ·
          refine ⟨1219467581475069194358679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1625956775300092259144905 1219467581475069194358679)
          ·
            refine ⟨1829201372212603791538019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219467581475069194358679 1829201372212603791538019)
            ·
              refine ⟨2743802058318905687307029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829201372212603791538019 2743802058318905687307029)
              ·
                refine ⟨128615721483698704092517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2743802058318905687307029 128615721483698704092517)
                ·
                  rfl

theorem cell21_1690728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 6].length) (baseStart_1690728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690728 prefixEnd_1690728 := by exact prefixLift 1690728
  have htrace : WordTrace (prefixWord ++ tailWord_1690728) baseStart_1690728 baseEnd_1690728 := by
    simpa [prefixWord, tailWord_1690728, baseEnd_1690728] using wordTrace_append hprefix tailTrace_1690728
  have hstable : (prefixWord ++ tailWord_1690728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690728).length < 2 ^ (prefixWord ++ tailWord_1690728).sum := by decide
  have hdescent : baseEnd_1690728 < baseStart_1690728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690784 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 5]
def baseStart_1690784 : Nat := 118140960795 + 1690784 * 2 ^ 59
def prefixEnd_1690784 : Nat := 4983230072969 + 3 ^ 40 * 1690784 * 2
def baseEnd_1690784 : Nat := 385859944414052459344103

theorem tailTrace_1690784 : CollatzResearch.WordTrace tailWord_1690784 prefixEnd_1690784 385859944414052459344103 := by
  unfold tailWord_1690784
  simp only [CollatzResearch.WordTrace]
  refine ⟨30833979353292902881359703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41111972471057203841812937 30833979353292902881359703)
  ·
    refine ⟨46250969029939354322039555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30833979353292902881359703 46250969029939354322039555)
    ·
      refine ⟨69376453544909031483059333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46250969029939354322039555 69376453544909031483059333)
      ·
        refine ⟨13008085039670443403073625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69376453544909031483059333 13008085039670443403073625)
        ·
          refine ⟨9756063779752832552305219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13008085039670443403073625 9756063779752832552305219)
          ·
            refine ⟨14634095669629248828457829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9756063779752832552305219 14634095669629248828457829)
            ·
              refine ⟨2743892938055484155335843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14634095669629248828457829 2743892938055484155335843)
              ·
                refine ⟨4115839407083226233003765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743892938055484155335843 4115839407083226233003765)
                ·
                  refine ⟨385859944414052459344103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4115839407083226233003765 385859944414052459344103)
                  ·
                    rfl

theorem cell21_1690784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_1690784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690784 prefixEnd_1690784 := by exact prefixLift 1690784
  have htrace : WordTrace (prefixWord ++ tailWord_1690784) baseStart_1690784 baseEnd_1690784 := by
    simpa [prefixWord, tailWord_1690784, baseEnd_1690784] using wordTrace_append hprefix tailTrace_1690784
  have hstable : (prefixWord ++ tailWord_1690784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690784).length < 2 ^ (prefixWord ++ tailWord_1690784).sum := by decide
  have hdescent : baseEnd_1690784 < baseStart_1690784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690888 : List Nat := [2, 1, 3, 2, 13]
def baseStart_1690888 : Nat := 118140960795 + 1690888 * 2 ^ 59
def prefixEnd_1690888 : Nat := 4983230072969 + 3 ^ 40 * 1690888 * 2
def baseEnd_1690888 : Nat := 4763996032481128266797

theorem tailTrace_1690888 : CollatzResearch.WordTrace tailWord_1690888 prefixEnd_1690888 4763996032481128266797 := by
  unfold tailWord_1690888
  simp only [CollatzResearch.WordTrace]
  refine ⟨30835875949104515762252659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41114501265472687683003545 30835875949104515762252659)
  ·
    refine ⟨46253813923656773643378989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30835875949104515762252659 46253813923656773643378989)
    ·
      refine ⟨17345180221371290116267121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46253813923656773643378989 17345180221371290116267121)
      ·
        refine ⟨13008885166028467587200341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17345180221371290116267121 13008885166028467587200341)
        ·
          refine ⟨4763996032481128266797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 13008885166028467587200341 4763996032481128266797)
          ·
            rfl

theorem cell21_1690888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 13].length) (baseStart_1690888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690888 prefixEnd_1690888 := by exact prefixLift 1690888
  have htrace : WordTrace (prefixWord ++ tailWord_1690888) baseStart_1690888 baseEnd_1690888 := by
    simpa [prefixWord, tailWord_1690888, baseEnd_1690888] using wordTrace_append hprefix tailTrace_1690888
  have hstable : (prefixWord ++ tailWord_1690888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690888).length < 2 ^ (prefixWord ++ tailWord_1690888).sum := by decide
  have hdescent : baseEnd_1690888 < baseStart_1690888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690891 : List Nat := [1, 1, 1, 1, 5, 4, 2, 2, 4]
def baseStart_1690891 : Nat := 118140960795 + 1690891 * 2 ^ 59
def prefixEnd_1690891 : Nat := 4983230072969 + 3 ^ 40 * 1690891 * 2
def baseEnd_1690891 : Nat := 385884363271844051060551

theorem tailTrace_1690891 : CollatzResearch.WordTrace tailWord_1690891 prefixEnd_1690891 385884363271844051060551 := by
  unfold tailWord_1690891
  simp only [CollatzResearch.WordTrace]
  refine ⟨61671861317198163036864527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41114574211465442024576351 61671861317198163036864527)
  ·
    refine ⟨92507791975797244555296791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61671861317198163036864527 92507791975797244555296791)
    ·
      refine ⟨138761687963695866832945187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92507791975797244555296791 138761687963695866832945187)
      ·
        refine ⟨208142531945543800249417781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138761687963695866832945187 208142531945543800249417781)
        ·
          refine ⟨19513362369894731273382917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 208142531945543800249417781 19513362369894731273382917)
          ·
            refine ⟨3658755444355262113759297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19513362369894731273382917 3658755444355262113759297)
            ·
              refine ⟨2744066583266446585319473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3658755444355262113759297 2744066583266446585319473)
              ·
                refine ⟨2058049937449834938989605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2744066583266446585319473 2058049937449834938989605)
                ·
                  refine ⟨385884363271844051060551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2058049937449834938989605 385884363271844051060551)
                  ·
                    rfl

theorem cell21_1690891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 4].length) (baseStart_1690891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690891 prefixEnd_1690891 := by exact prefixLift 1690891
  have htrace : WordTrace (prefixWord ++ tailWord_1690891) baseStart_1690891 baseEnd_1690891 := by
    simpa [prefixWord, tailWord_1690891, baseEnd_1690891] using wordTrace_append hprefix tailTrace_1690891
  have hstable : (prefixWord ++ tailWord_1690891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690891).length < 2 ^ (prefixWord ++ tailWord_1690891).sum := by decide
  have hdescent : baseEnd_1690891 < baseStart_1690891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690894 : List Nat := [4, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_1690894 : Nat := 118140960795 + 1690894 * 2 ^ 59
def prefixEnd_1690894 : Nat := 4983230072969 + 3 ^ 40 * 1690894 * 2
def baseEnd_1690894 : Nat := 385885047912716712510545

theorem tailTrace_1690894 : CollatzResearch.WordTrace tailWord_1690894 prefixEnd_1690894 385885047912716712510545 := by
  unfold tailWord_1690894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7708996342023411818652967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41114647157458196366149157 7708996342023411818652967)
  ·
    refine ⟨11563494513035117727979451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7708996342023411818652967 11563494513035117727979451)
    ·
      refine ⟨17345241769552676591969177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11563494513035117727979451 17345241769552676591969177)
      ·
        refine ⟨13008931327164507443976883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17345241769552676591969177 13008931327164507443976883)
        ·
          refine ⟨19513396990746761165965325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13008931327164507443976883 19513396990746761165965325)
          ·
            refine ⟨7317523871530035437236997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19513396990746761165965325 7317523871530035437236997)
            ·
              refine ⟨1372035725911881644481937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7317523871530035437236997 1372035725911881644481937)
              ·
                refine ⟨1029026794433911233361453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1372035725911881644481937 1029026794433911233361453)
                ·
                  refine ⟨385885047912716712510545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029026794433911233361453 385885047912716712510545)
                  ·
                    rfl

theorem cell21_1690894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_1690894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690894 prefixEnd_1690894 := by exact prefixLift 1690894
  have htrace : WordTrace (prefixWord ++ tailWord_1690894) baseStart_1690894 baseEnd_1690894 := by
    simpa [prefixWord, tailWord_1690894, baseEnd_1690894] using wordTrace_append hprefix tailTrace_1690894
  have hstable : (prefixWord ++ tailWord_1690894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690894).length < 2 ^ (prefixWord ++ tailWord_1690894).sum := by decide
  have hdescent : baseEnd_1690894 < baseStart_1690894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690973 : List Nat := [1, 4, 5, 1, 1, 2, 2, 5]
def baseStart_1690973 : Nat := 118140960795 + 1690973 * 2 ^ 59
def prefixEnd_1690973 : Nat := 4983230072969 + 3 ^ 40 * 1690973 * 2
def baseEnd_1690973 : Nat := 128634358929676710231239

theorem tailTrace_1690973 : CollatzResearch.WordTrace tailWord_1690973 prefixEnd_1690973 128634358929676710231239 := by
  unfold tailWord_1690973
  simp only [CollatzResearch.WordTrace]
  refine ⟨61674852102901091041349573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41116568068600727360899715 61674852102901091041349573)
  ·
    refine ⟨11564034769293954570253045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61674852102901091041349573 11564034769293954570253045)
    ·
      refine ⟨1084128259621308240961223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11564034769293954570253045 1084128259621308240961223)
      ·
        refine ⟨1626192389431962361441835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084128259621308240961223 1626192389431962361441835)
        ·
          refine ⟨2439288584147943542162753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626192389431962361441835 2439288584147943542162753)
          ·
            refine ⟨1829466438110957656622065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2439288584147943542162753 1829466438110957656622065)
            ·
              refine ⟨1372099828583218242466549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829466438110957656622065 1372099828583218242466549)
              ·
                refine ⟨128634358929676710231239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1372099828583218242466549 128634358929676710231239)
                ·
                  rfl

theorem cell21_1690973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 5].length) (baseStart_1690973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1690973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1690973 prefixEnd_1690973 := by exact prefixLift 1690973
  have htrace : WordTrace (prefixWord ++ tailWord_1690973) baseStart_1690973 baseEnd_1690973 := by
    simpa [prefixWord, tailWord_1690973, baseEnd_1690973] using wordTrace_append hprefix tailTrace_1690973
  have hstable : (prefixWord ++ tailWord_1690973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690973).length < 2 ^ (prefixWord ++ tailWord_1690973).sum := by decide
  have hdescent : baseEnd_1690973 < baseStart_1690973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691012 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 5]
def baseStart_1691012 : Nat := 118140960795 + 1691012 * 2 ^ 59
def prefixEnd_1691012 : Nat := 4983230072969 + 3 ^ 40 * 1691012 * 2
def baseEnd_1691012 : Nat := 385911977120374729543637

theorem tailTrace_1691012 : CollatzResearch.WordTrace tailWord_1691012 prefixEnd_1691012 385911977120374729543637 := by
  unfold tailWord_1691012
  simp only [CollatzResearch.WordTrace]
  refine ⟨30838137274879900351009645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41117516366506533801346193 30838137274879900351009645)
  ·
    refine ⟨11564301478079962631628617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30838137274879900351009645 11564301478079962631628617)
    ·
      refine ⟨8673226108559971973721463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11564301478079962631628617 8673226108559971973721463)
      ·
        refine ⟨13009839162839957960582195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8673226108559971973721463 13009839162839957960582195)
        ·
          refine ⟨19514758744259936940873293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13009839162839957960582195 19514758744259936940873293)
          ·
            refine ⟨7318034529097476352827485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19514758744259936940873293 7318034529097476352827485)
            ·
              refine ⟨2744262948411553632310307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7318034529097476352827485 2744262948411553632310307)
              ·
                refine ⟨4116394422617330448465461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744262948411553632310307 4116394422617330448465461)
                ·
                  refine ⟨385911977120374729543637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4116394422617330448465461 385911977120374729543637)
                  ·
                    rfl

theorem cell21_1691012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_1691012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691012 prefixEnd_1691012 := by exact prefixLift 1691012
  have htrace : WordTrace (prefixWord ++ tailWord_1691012) baseStart_1691012 baseEnd_1691012 := by
    simpa [prefixWord, tailWord_1691012, baseEnd_1691012] using wordTrace_append hprefix tailTrace_1691012
  have hstable : (prefixWord ++ tailWord_1691012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691012).length < 2 ^ (prefixWord ++ tailWord_1691012).sum := by decide
  have hdescent : baseEnd_1691012 < baseStart_1691012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691040 : List Nat := [2, 1, 1, 4, 1, 2, 1, 9]
def baseStart_1691040 : Nat := 118140960795 + 1691040 * 2 ^ 59
def prefixEnd_1691040 : Nat := 4983230072969 + 3 ^ 40 * 1691040 * 2
def baseEnd_1691040 : Nat := 128639455700617634358971

theorem tailTrace_1691040 : CollatzResearch.WordTrace tailWord_1691040 prefixEnd_1691040 128639455700617634358971 := by
  unfold tailWord_1691040
  simp only [CollatzResearch.WordTrace]
  refine ⟨30838647896829180742019287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41118197195772240989359049 30838647896829180742019287)
  ·
    refine ⟨46257971845243771113028931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30838647896829180742019287 46257971845243771113028931)
    ·
      refine ⟨69386957767865656669543397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46257971845243771113028931 69386957767865656669543397)
      ·
        refine ⟨13010054581474810625539387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69386957767865656669543397 13010054581474810625539387)
        ·
          refine ⟨19515081872212215938309081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13010054581474810625539387 19515081872212215938309081)
          ·
            refine ⟨14636311404159161953731811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19515081872212215938309081 14636311404159161953731811)
            ·
              refine ⟨21954467106238742930597717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14636311404159161953731811 21954467106238742930597717)
              ·
                refine ⟨128639455700617634358971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21954467106238742930597717 128639455700617634358971)
                ·
                  rfl

theorem cell21_1691040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_1691040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691040 prefixEnd_1691040 := by exact prefixLift 1691040
  have htrace : WordTrace (prefixWord ++ tailWord_1691040) baseStart_1691040 baseEnd_1691040 := by
    simpa [prefixWord, tailWord_1691040, baseEnd_1691040] using wordTrace_append hprefix tailTrace_1691040
  have hstable : (prefixWord ++ tailWord_1691040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691040).length < 2 ^ (prefixWord ++ tailWord_1691040).sum := by decide
  have hdescent : baseEnd_1691040 < baseStart_1691040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691105 : List Nat := [1, 2, 3, 1, 2, 4, 2, 3, 3]
def baseStart_1691105 : Nat := 118140960795 + 1691105 * 2 ^ 59
def prefixEnd_1691105 : Nat := 4983230072969 + 3 ^ 40 * 1691105 * 2
def baseEnd_1691105 : Nat := 385933200987427234493447

theorem tailTrace_1691105 : CollatzResearch.WordTrace tailWord_1691105 prefixEnd_1691105 385933200987427234493447 := by
  unfold tailWord_1691105
  simp only [CollatzResearch.WordTrace]
  refine ⟨61679666538422877585154769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41119777692281918390103179 61679666538422877585154769)
  ·
    refine ⟨46259749903817158188866077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61679666538422877585154769 46259749903817158188866077)
    ·
      refine ⟨17347406213931434320824779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46259749903817158188866077 17347406213931434320824779)
      ·
        refine ⟨26021109320897151481237169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17347406213931434320824779 26021109320897151481237169)
        ·
          refine ⟨19515831990672863610927877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26021109320897151481237169 19515831990672863610927877)
          ·
            refine ⟨3659218498251161927048977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19515831990672863610927877 3659218498251161927048977)
            ·
              refine ⟨2744413873688371445286733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3659218498251161927048977 2744413873688371445286733)
              ·
                refine ⟨1029155202633139291982525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2744413873688371445286733 1029155202633139291982525)
                ·
                  refine ⟨385933200987427234493447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029155202633139291982525 385933200987427234493447)
                  ·
                    rfl

theorem cell21_1691105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 3].length) (baseStart_1691105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691105 prefixEnd_1691105 := by exact prefixLift 1691105
  have htrace : WordTrace (prefixWord ++ tailWord_1691105) baseStart_1691105 baseEnd_1691105 := by
    simpa [prefixWord, tailWord_1691105, baseEnd_1691105] using wordTrace_append hprefix tailTrace_1691105
  have hstable : (prefixWord ++ tailWord_1691105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691105).length < 2 ^ (prefixWord ++ tailWord_1691105).sum := by decide
  have hdescent : baseEnd_1691105 < baseStart_1691105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691142 : List Nat := [6, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1691142 : Nat := 118140960795 + 1691142 * 2 ^ 59
def prefixEnd_1691142 : Nat := 4983230072969 + 3 ^ 40 * 1691142 * 2
def baseEnd_1691142 : Nat := 128647214963841130792235

theorem tailTrace_1691142 : CollatzResearch.WordTrace tailWord_1691142 prefixEnd_1691142 128647214963841130792235 := by
  unfold tailWord_1691142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1927531751227776028257865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41120677359525888602834453 1927531751227776028257865)
  ·
    refine ⟨1445648813420832021193399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1927531751227776028257865 1445648813420832021193399)
    ·
      refine ⟨2168473220131248031790099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1445648813420832021193399 2168473220131248031790099)
      ·
        refine ⟨3252709830196872047685149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2168473220131248031790099 3252709830196872047685149)
        ·
          refine ⟨1219766186323827017881931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3252709830196872047685149 1219766186323827017881931)
          ·
            refine ⟨1829649279485740526822897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219766186323827017881931 1829649279485740526822897)
            ·
              refine ⟨1372236959614305395117173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829649279485740526822897 1372236959614305395117173)
              ·
                refine ⟨128647214963841130792235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1372236959614305395117173 128647214963841130792235)
                ·
                  rfl

theorem cell21_1691142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1691142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691142 prefixEnd_1691142 := by exact prefixLift 1691142
  have htrace : WordTrace (prefixWord ++ tailWord_1691142) baseStart_1691142 baseEnd_1691142 := by
    simpa [prefixWord, tailWord_1691142, baseEnd_1691142] using wordTrace_append hprefix tailTrace_1691142
  have hstable : (prefixWord ++ tailWord_1691142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691142).length < 2 ^ (prefixWord ++ tailWord_1691142).sum := by decide
  have hdescent : baseEnd_1691142 < baseStart_1691142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691156 : List Nat := [2, 4, 3, 1, 3, 1, 1, 3, 3]
def baseStart_1691156 : Nat := 118140960795 + 1691156 * 2 ^ 59
def prefixEnd_1691156 : Nat := 4983230072969 + 3 ^ 40 * 1691156 * 2
def baseEnd_1691156 : Nat := 385944839882262479143343

theorem tailTrace_1691156 : CollatzResearch.WordTrace tailWord_1691156 prefixEnd_1691156 385944839882262479143343 := by
  unfold tailWord_1691156
  simp only [CollatzResearch.WordTrace]
  refine ⟨30840763330619056647630661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41121017774158742196840881 30840763330619056647630661)
  ·
    refine ⟨5782643124491073121430749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30840763330619056647630661 5782643124491073121430749)
    ·
      refine ⟨2168491171684152420536531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5782643124491073121430749 2168491171684152420536531)
      ·
        refine ⟨3252736757526228630804797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2168491171684152420536531 3252736757526228630804797)
        ·
          refine ⟨1219776284072335736551799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3252736757526228630804797 1219776284072335736551799)
          ·
            refine ⟨1829664426108503604827699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219776284072335736551799 1829664426108503604827699)
            ·
              refine ⟨2744496639162755407241549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829664426108503604827699 2744496639162755407241549)
              ·
                refine ⟨1029186239686033277715581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2744496639162755407241549 1029186239686033277715581)
                ·
                  refine ⟨385944839882262479143343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029186239686033277715581 385944839882262479143343)
                  ·
                    rfl

theorem cell21_1691156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_1691156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691156 prefixEnd_1691156 := by exact prefixLift 1691156
  have htrace : WordTrace (prefixWord ++ tailWord_1691156) baseStart_1691156 baseEnd_1691156 := by
    simpa [prefixWord, tailWord_1691156, baseEnd_1691156] using wordTrace_append hprefix tailTrace_1691156
  have hstable : (prefixWord ++ tailWord_1691156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691156).length < 2 ^ (prefixWord ++ tailWord_1691156).sum := by decide
  have hdescent : baseEnd_1691156 < baseStart_1691156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691178 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_1691178 : Nat := 118140960795 + 1691178 * 2 ^ 59
def prefixEnd_1691178 : Nat := 4983230072969 + 3 ^ 40 * 1691178 * 2
def baseEnd_1691178 : Nat := 385949860581995329776631

theorem tailTrace_1691178 : CollatzResearch.WordTrace tailWord_1691178 prefixEnd_1691178 385949860581995329776631 := by
  unfold tailWord_1691178
  simp only [CollatzResearch.WordTrace]
  refine ⟨15420582266789602763140547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41121552711438940701708125 15420582266789602763140547)
  ·
    refine ⟨23130873400184404144710821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15420582266789602763140547 23130873400184404144710821)
    ·
      refine ⟨4337038762534575777133279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23130873400184404144710821 4337038762534575777133279)
      ·
        refine ⟨6505558143801863665699919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4337038762534575777133279 6505558143801863665699919)
        ·
          refine ⟨9758337215702795498549879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6505558143801863665699919 9758337215702795498549879)
          ·
            refine ⟨14637505823554193247824819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9758337215702795498549879 14637505823554193247824819)
            ·
              refine ⟨21956258735331289871737229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14637505823554193247824819 21956258735331289871737229)
              ·
                refine ⟨8233597025749233701901461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21956258735331289871737229 8233597025749233701901461)
                ·
                  refine ⟨385949860581995329776631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8233597025749233701901461 385949860581995329776631)
                  ·
                    rfl

theorem cell21_1691178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_1691178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691178 prefixEnd_1691178 := by exact prefixLift 1691178
  have htrace : WordTrace (prefixWord ++ tailWord_1691178) baseStart_1691178 baseEnd_1691178 := by
    simpa [prefixWord, tailWord_1691178, baseEnd_1691178] using wordTrace_append hprefix tailTrace_1691178
  have hstable : (prefixWord ++ tailWord_1691178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691178).length < 2 ^ (prefixWord ++ tailWord_1691178).sum := by decide
  have hdescent : baseEnd_1691178 < baseStart_1691178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691192 : List Nat := [2, 1, 2, 1, 4, 2, 1, 8]
def baseStart_1691192 : Nat := 118140960795 + 1691192 * 2 ^ 59
def prefixEnd_1691192 : Nat := 4983230072969 + 3 ^ 40 * 1691192 * 2
def baseEnd_1691192 : Nat := 128651018524244805514423

theorem tailTrace_1691192 : CollatzResearch.WordTrace tailWord_1691192 prefixEnd_1691192 128651018524244805514423 := by
  unfold tailWord_1691192
  simp only [CollatzResearch.WordTrace]
  refine ⟨30841419844553845721785915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41121893126071794295714553 30841419844553845721785915)
  ·
    refine ⟨46262129766830768582678873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30841419844553845721785915 46262129766830768582678873)
    ·
      refine ⟨34696597325123076437009155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46262129766830768582678873 34696597325123076437009155)
      ·
        refine ⟨52044895987684614655513733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34696597325123076437009155 52044895987684614655513733)
        ·
          refine ⟨9758417997690865247908825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52044895987684614655513733 9758417997690865247908825)
          ·
            refine ⟨7318813498268148935931619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9758417997690865247908825 7318813498268148935931619)
            ·
              refine ⟨10978220247402223403897429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7318813498268148935931619 10978220247402223403897429)
              ·
                refine ⟨128651018524244805514423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10978220247402223403897429 128651018524244805514423)
                ·
                  rfl

theorem cell21_1691192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_1691192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691192 prefixEnd_1691192 := by exact prefixLift 1691192
  have htrace : WordTrace (prefixWord ++ tailWord_1691192) baseStart_1691192 baseEnd_1691192 := by
    simpa [prefixWord, tailWord_1691192, baseEnd_1691192] using wordTrace_append hprefix tailTrace_1691192
  have hstable : (prefixWord ++ tailWord_1691192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691192).length < 2 ^ (prefixWord ++ tailWord_1691192).sum := by decide
  have hdescent : baseEnd_1691192 < baseStart_1691192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691229 : List Nat := [1, 4, 4, 2, 1, 1, 2, 2, 4]
def baseStart_1691229 : Nat := 118140960795 + 1691229 * 2 ^ 59
def prefixEnd_1691229 : Nat := 4983230072969 + 3 ^ 40 * 1691229 * 2
def baseEnd_1691229 : Nat := 385961499476830574426527

theorem tailTrace_1691229 : CollatzResearch.WordTrace tailWord_1691229 prefixEnd_1691229 385961499476830574426527 := by
  unfold tailWord_1691229
  simp only [CollatzResearch.WordTrace]
  refine ⟨61684189189973646762668741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41122792793315764508445827 61684189189973646762668741)
  ·
    refine ⟨11565785473120058768000389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61684189189973646762668741 11565785473120058768000389)
    ·
      refine ⟨2168584776210011019000073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11565785473120058768000389 2168584776210011019000073)
      ·
        refine ⟨1626438582157508264250055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2168584776210011019000073 1626438582157508264250055)
        ·
          refine ⟨2439657873236262396375083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626438582157508264250055 2439657873236262396375083)
          ·
            refine ⟨3659486809854393594562625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2439657873236262396375083 3659486809854393594562625)
            ·
              refine ⟨2744615107390795195921969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3659486809854393594562625 2744615107390795195921969)
              ·
                refine ⟨2058461330543096396941477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2744615107390795195921969 2058461330543096396941477)
                ·
                  refine ⟨385961499476830574426527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2058461330543096396941477 385961499476830574426527)
                  ·
                    rfl

theorem cell21_1691229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_1691229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691229 prefixEnd_1691229 := by exact prefixLift 1691229
  have htrace : WordTrace (prefixWord ++ tailWord_1691229) baseStart_1691229 baseEnd_1691229 := by
    simpa [prefixWord, tailWord_1691229, baseEnd_1691229] using wordTrace_append hprefix tailTrace_1691229
  have hstable : (prefixWord ++ tailWord_1691229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691229).length < 2 ^ (prefixWord ++ tailWord_1691229).sum := by decide
  have hdescent : baseEnd_1691229 < baseStart_1691229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691299 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 5]
def baseStart_1691299 : Nat := 118140960795 + 1691299 * 2 ^ 59
def prefixEnd_1691299 : Nat := 4983230072969 + 3 ^ 40 * 1691299 * 2
def baseEnd_1691299 : Nat := 385977474430526008259717

theorem tailTrace_1691299 : CollatzResearch.WordTrace tailWord_1691299 prefixEnd_1691299 385977474430526008259717 := by
  unfold tailWord_1691299
  simp only [CollatzResearch.WordTrace]
  refine ⟨61686742299720048717716951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41124494866480032478477967 61686742299720048717716951)
  ·
    refine ⟨92530113449580073076575427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61686742299720048717716951 92530113449580073076575427)
    ·
      refine ⟨138795170174370109614863141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92530113449580073076575427 138795170174370109614863141)
      ·
        refine ⟨26024094407694395552786839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138795170174370109614863141 26024094407694395552786839)
        ·
          refine ⟨39036141611541593329180259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26024094407694395552786839 39036141611541593329180259)
          ·
            refine ⟨58554212417312389993770389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39036141611541593329180259 58554212417312389993770389)
            ·
              refine ⟨2744728707061518280957987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58554212417312389993770389 2744728707061518280957987)
              ·
                refine ⟨4117093060592277421436981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744728707061518280957987 4117093060592277421436981)
                ·
                  refine ⟨385977474430526008259717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4117093060592277421436981 385977474430526008259717)
                  ·
                    rfl

theorem cell21_1691299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 5].length) (baseStart_1691299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691299 prefixEnd_1691299 := by exact prefixLift 1691299
  have htrace : WordTrace (prefixWord ++ tailWord_1691299) baseStart_1691299 baseEnd_1691299 := by
    simpa [prefixWord, tailWord_1691299, baseEnd_1691299] using wordTrace_append hprefix tailTrace_1691299
  have hstable : (prefixWord ++ tailWord_1691299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691299).length < 2 ^ (prefixWord ++ tailWord_1691299).sum := by decide
  have hdescent : baseEnd_1691299 < baseStart_1691299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691361 : List Nat := [1, 2, 3, 1, 5, 1, 2, 6]
def baseStart_1691361 : Nat := 118140960795 + 1691361 * 2 ^ 59
def prefixEnd_1691361 : Nat := 4983230072969 + 3 ^ 40 * 1691361 * 2
def baseEnd_1691361 : Nat := 128663874558409226075419

theorem tailTrace_1691361 : CollatzResearch.WordTrace tailWord_1691361 prefixEnd_1691361 128663874558409226075419 := by
  unfold tailWord_1691361
  simp only [CollatzResearch.WordTrace]
  refine ⟨61689003625495433306473937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41126002416996955537649291 61689003625495433306473937)
  ·
    refine ⟨46266752719121574979855453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61689003625495433306473937 46266752719121574979855453)
    ·
      refine ⟨17350032269670590617445795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46266752719121574979855453 17350032269670590617445795)
      ·
        refine ⟨26025048404505885926168693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17350032269670590617445795 26025048404505885926168693)
        ·
          refine ⟨2439848287922426805578315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26025048404505885926168693 2439848287922426805578315)
          ·
            refine ⟨3659772431883640208367473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2439848287922426805578315 3659772431883640208367473)
            ·
              refine ⟨2744829323912730156275605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3659772431883640208367473 2744829323912730156275605)
              ·
                refine ⟨128663874558409226075419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2744829323912730156275605 128663874558409226075419)
                ·
                  rfl

theorem cell21_1691361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 6].length) (baseStart_1691361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691361 prefixEnd_1691361 := by exact prefixLift 1691361
  have htrace : WordTrace (prefixWord ++ tailWord_1691361) baseStart_1691361 baseEnd_1691361 := by
    simpa [prefixWord, tailWord_1691361, baseEnd_1691361] using wordTrace_append hprefix tailTrace_1691361
  have hstable : (prefixWord ++ tailWord_1691361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691361).length < 2 ^ (prefixWord ++ tailWord_1691361).sum := by decide
  have hdescent : baseEnd_1691361 < baseStart_1691361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691389 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 6]
def baseStart_1691389 : Nat := 118140960795 + 1691389 * 2 ^ 59
def prefixEnd_1691389 : Nat := 4983230072969 + 3 ^ 40 * 1691389 * 2
def baseEnd_1691389 : Nat := 385998013656705851759533

theorem tailTrace_1691389 : CollatzResearch.WordTrace tailWord_1691389 prefixEnd_1691389 385998013656705851759533 := by
  unfold tailWord_1691389
  simp only [CollatzResearch.WordTrace]
  refine ⟨61690024869393994088493221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41126683246262662725662147 61690024869393994088493221)
  ·
    refine ⟨11566879663011373891592479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61690024869393994088493221 11566879663011373891592479)
    ·
      refine ⟨17350319494517060837388719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11566879663011373891592479 17350319494517060837388719)
      ·
        refine ⟨26025479241775591256083079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17350319494517060837388719 26025479241775591256083079)
        ·
          refine ⟨39038218862663386884124619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26025479241775591256083079 39038218862663386884124619)
          ·
            refine ⟨58557328293995080326186929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39038218862663386884124619 58557328293995080326186929)
            ·
              refine ⟨43917996220496310244640197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58557328293995080326186929 43917996220496310244640197)
              ·
                refine ⟨8234624291343058170870037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43917996220496310244640197 8234624291343058170870037)
                ·
                  refine ⟨385998013656705851759533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8234624291343058170870037 385998013656705851759533)
                  ·
                    rfl

theorem cell21_1691389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_1691389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691389 prefixEnd_1691389 := by exact prefixLift 1691389
  have htrace : WordTrace (prefixWord ++ tailWord_1691389) baseStart_1691389 baseEnd_1691389 := by
    simpa [prefixWord, tailWord_1691389, baseEnd_1691389] using wordTrace_append hprefix tailTrace_1691389
  have hstable : (prefixWord ++ tailWord_1691389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691389).length < 2 ^ (prefixWord ++ tailWord_1691389).sum := by decide
  have hdescent : baseEnd_1691389 < baseStart_1691389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691406 : List Nat := [4, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1691406 : Nat := 118140960795 + 1691406 * 2 ^ 59
def prefixEnd_1691406 : Nat := 4983230072969 + 3 ^ 40 * 1691406 * 2
def baseEnd_1691406 : Nat := 386001893288317599976165

theorem tailTrace_1691406 : CollatzResearch.WordTrace tailWord_1691406 prefixEnd_1691406 386001893288317599976165 := by
  unfold tailWord_1691406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7711330613791550748982759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41127096606888270661241381 7711330613791550748982759)
  ·
    refine ⟨11566995920687326123474139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7711330613791550748982759 11566995920687326123474139)
    ·
      refine ⟨17350493881030989185211209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11566995920687326123474139 17350493881030989185211209)
      ·
        refine ⟨13012870410773241888908407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17350493881030989185211209 13012870410773241888908407)
        ·
          refine ⟨19519305616159862833362611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13012870410773241888908407 19519305616159862833362611)
          ·
            refine ⟨29278958424239794250043917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19519305616159862833362611 29278958424239794250043917)
            ·
              refine ⟨10979609409089922843766469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29278958424239794250043917 10979609409089922843766469)
              ·
                refine ⟨2058676764204360533206213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10979609409089922843766469 2058676764204360533206213)
                ·
                  refine ⟨386001893288317599976165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2058676764204360533206213 386001893288317599976165)
                  ·
                    rfl

theorem cell21_1691406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1691406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691406 prefixEnd_1691406 := by exact prefixLift 1691406
  have htrace : WordTrace (prefixWord ++ tailWord_1691406) baseStart_1691406 baseEnd_1691406 := by
    simpa [prefixWord, tailWord_1691406, baseEnd_1691406] using wordTrace_append hprefix tailTrace_1691406
  have hstable : (prefixWord ++ tailWord_1691406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691406).length < 2 ^ (prefixWord ++ tailWord_1691406).sum := by decide
  have hdescent : baseEnd_1691406 < baseStart_1691406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691412 : List Nat := [2, 4, 4, 1, 1, 2, 1, 6]
def baseStart_1691412 : Nat := 118140960795 + 1691412 * 2 ^ 59
def prefixEnd_1691412 : Nat := 4983230072969 + 3 ^ 40 * 1691412 * 2
def baseEnd_1691412 : Nat := 128667754190020974292051

theorem tailTrace_1691412 : CollatzResearch.WordTrace tailWord_1691412 prefixEnd_1691412 128667754190020974292051 := by
  unfold tailWord_1691412
  simp only [CollatzResearch.WordTrace]
  refine ⟨30845431874155334508290245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41127242498873779344386993 30845431874155334508290245)
  ·
    refine ⟨5783518476404125220304421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30845431874155334508290245 5783518476404125220304421)
    ·
      refine ⟨1084409714325773478807079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5783518476404125220304421 1084409714325773478807079)
      ·
        refine ⟨1626614571488660218210619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084409714325773478807079 1626614571488660218210619)
        ·
          refine ⟨2439921857232990327315929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626614571488660218210619 2439921857232990327315929)
          ·
            refine ⟨1829941392924742745486947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2439921857232990327315929 1829941392924742745486947)
            ·
              refine ⟨2744912089387114118230421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829941392924742745486947 2744912089387114118230421)
              ·
                refine ⟨128667754190020974292051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2744912089387114118230421 128667754190020974292051)
                ·
                  rfl

theorem cell21_1691412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 6].length) (baseStart_1691412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691412 prefixEnd_1691412 := by exact prefixLift 1691412
  have htrace : WordTrace (prefixWord ++ tailWord_1691412) baseStart_1691412 baseEnd_1691412 := by
    simpa [prefixWord, tailWord_1691412, baseEnd_1691412] using wordTrace_append hprefix tailTrace_1691412
  have hstable : (prefixWord ++ tailWord_1691412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691412).length < 2 ^ (prefixWord ++ tailWord_1691412).sum := by decide
  have hdescent : baseEnd_1691412 < baseStart_1691412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691465 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 6]
def baseStart_1691465 : Nat := 118140960795 + 1691465 * 2 ^ 59
def prefixEnd_1691465 : Nat := 4983230072969 + 3 ^ 40 * 1691465 * 2
def baseEnd_1691465 : Nat := 386015357892146608492711

theorem tailTrace_1691465 : CollatzResearch.WordTrace tailWord_1691465 prefixEnd_1691465 386015357892146608492711 := by
  unfold tailWord_1691465
  simp only [CollatzResearch.WordTrace]
  refine ⟨61692796817118659068259849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41128531211412439378839899 61692796817118659068259849)
  ·
    refine ⟨46269597612838994301194887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61692796817118659068259849 46269597612838994301194887)
    ·
      refine ⟨69404396419258491451792331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46269597612838994301194887 69404396419258491451792331)
      ·
        refine ⟨104106594628887737177688497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69404396419258491451792331 104106594628887737177688497)
        ·
          refine ⟨78079945971665802883266373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104106594628887737177688497 78079945971665802883266373)
          ·
            refine ⟨14639989869687338040612445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78079945971665802883266373 14639989869687338040612445)
            ·
              refine ⟨5489996201132751765229667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14639989869687338040612445 5489996201132751765229667)
              ·
                refine ⟨8234994301699127647844501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5489996201132751765229667 8234994301699127647844501)
                ·
                  refine ⟨386015357892146608492711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8234994301699127647844501 386015357892146608492711)
                  ·
                    rfl

theorem cell21_1691465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_1691465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691465 prefixEnd_1691465 := by exact prefixLift 1691465
  have htrace : WordTrace (prefixWord ++ tailWord_1691465) baseStart_1691465 baseEnd_1691465 := by
    simpa [prefixWord, tailWord_1691465, baseEnd_1691465] using wordTrace_append hprefix tailTrace_1691465
  have hstable : (prefixWord ++ tailWord_1691465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691465).length < 2 ^ (prefixWord ++ tailWord_1691465).sum := by decide
  have hdescent : baseEnd_1691465 < baseStart_1691465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691468 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 5]
def baseStart_1691468 : Nat := 118140960795 + 1691468 * 2 ^ 59
def prefixEnd_1691468 : Nat := 4983230072969 + 3 ^ 40 * 1691468 * 2
def baseEnd_1691468 : Nat := 386016042533019269942705

theorem tailTrace_1691468 : CollatzResearch.WordTrace tailWord_1691468 prefixEnd_1691468 386016042533019269942705 := by
  unfold tailWord_1691468
  simp only [CollatzResearch.WordTrace]
  refine ⟨30846453118053895290309529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41128604157405193720412705 30846453118053895290309529)
  ·
    refine ⟨23134839838540421467732147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30846453118053895290309529 23134839838540421467732147)
    ·
      refine ⟨34702259757810632201598221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23134839838540421467732147 34702259757810632201598221)
      ·
        refine ⟨13013347409178987075599333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34702259757810632201598221 13013347409178987075599333)
        ·
          refine ⟨2440002639221060076674875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13013347409178987075599333 2440002639221060076674875)
          ·
            refine ⟨3660003958831590115012313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440002639221060076674875 3660003958831590115012313)
            ·
              refine ⟨2745002969123692586259235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3660003958831590115012313 2745002969123692586259235)
              ·
                refine ⟨4117504453685538879388853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2745002969123692586259235 4117504453685538879388853)
                ·
                  refine ⟨386016042533019269942705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4117504453685538879388853 386016042533019269942705)
                  ·
                    rfl

theorem cell21_1691468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_1691468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691468 prefixEnd_1691468 := by exact prefixLift 1691468
  have htrace : WordTrace (prefixWord ++ tailWord_1691468) baseStart_1691468 baseEnd_1691468 := by
    simpa [prefixWord, tailWord_1691468, baseEnd_1691468] using wordTrace_append hprefix tailTrace_1691468
  have hstable : (prefixWord ++ tailWord_1691468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691468).length < 2 ^ (prefixWord ++ tailWord_1691468).sum := by decide
  have hdescent : baseEnd_1691468 < baseStart_1691468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691496 : List Nat := [2, 1, 4, 2, 1, 1, 3, 7]
def baseStart_1691496 : Nat := 118140960795 + 1691496 * 2 ^ 59
def prefixEnd_1691496 : Nat := 4983230072969 + 3 ^ 40 * 1691496 * 2
def baseEnd_1691496 : Nat := 128674144171499147825327

theorem tailTrace_1691496 : CollatzResearch.WordTrace tailWord_1691496 prefixEnd_1691496 128674144171499147825327 := by
  unfold tailWord_1691496
  simp only [CollatzResearch.WordTrace]
  refine ⟨30846963740003175681319171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41129284986670900908425561 30846963740003175681319171)
  ·
    refine ⟨46270445610004763521978757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30846963740003175681319171 46270445610004763521978757)
    ·
      refine ⟨8675708551875893160371017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46270445610004763521978757 8675708551875893160371017)
      ·
        refine ⟨6506781413906919870278263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8675708551875893160371017 6506781413906919870278263)
        ·
          refine ⟨9760172120860379805417395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6506781413906919870278263 9760172120860379805417395)
          ·
            refine ⟨14640258181290569708126093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9760172120860379805417395 14640258181290569708126093)
            ·
              refine ⟨5490096817983963640547285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14640258181290569708126093 5490096817983963640547285)
              ·
                refine ⟨128674144171499147825327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5490096817983963640547285 128674144171499147825327)
                ·
                  rfl

theorem cell21_1691496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_1691496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691496 prefixEnd_1691496 := by exact prefixLift 1691496
  have htrace : WordTrace (prefixWord ++ tailWord_1691496) baseStart_1691496 baseEnd_1691496 := by
    simpa [prefixWord, tailWord_1691496, baseEnd_1691496] using wordTrace_append hprefix tailTrace_1691496
  have hstable : (prefixWord ++ tailWord_1691496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691496).length < 2 ^ (prefixWord ++ tailWord_1691496).sum := by decide
  have hdescent : baseEnd_1691496 < baseStart_1691496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691502 : List Nat := [4, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_1691502 : Nat := 118140960795 + 1691502 * 2 ^ 59
def prefixEnd_1691502 : Nat := 4983230072969 + 3 ^ 40 * 1691502 * 2
def baseEnd_1691502 : Nat := 386023801796242766375969

theorem tailTrace_1691502 : CollatzResearch.WordTrace tailWord_1691502 prefixEnd_1691502 386023801796242766375969 := by
  unfold tailWord_1691502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7711768289748076798419595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41129430878656409591571173 7711768289748076798419595)
  ·
    refine ⟨11567652434622115197629393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7711768289748076798419595 11567652434622115197629393)
    ·
      refine ⟨8675739325966586398222045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11567652434622115197629393 8675739325966586398222045)
      ·
        refine ⟨3253402247237469899333267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8675739325966586398222045 3253402247237469899333267)
        ·
          refine ⟨4880103370856204848999901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253402247237469899333267 4880103370856204848999901)
          ·
            refine ⟨1830038764071076818374963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4880103370856204848999901 1830038764071076818374963)
            ·
              refine ⟨2745058146106615227562445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830038764071076818374963 2745058146106615227562445)
              ·
                refine ⟨1029396804789980710335917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2745058146106615227562445 1029396804789980710335917)
                ·
                  refine ⟨386023801796242766375969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029396804789980710335917 386023801796242766375969)
                  ·
                    rfl

theorem cell21_1691502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_1691502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691502 prefixEnd_1691502 := by exact prefixLift 1691502
  have htrace : WordTrace (prefixWord ++ tailWord_1691502) baseStart_1691502 baseEnd_1691502 := by
    simpa [prefixWord, tailWord_1691502, baseEnd_1691502] using wordTrace_append hprefix tailTrace_1691502
  have hstable : (prefixWord ++ tailWord_1691502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691502).length < 2 ^ (prefixWord ++ tailWord_1691502).sum := by decide
  have hdescent : baseEnd_1691502 < baseStart_1691502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691620 : List Nat := [2, 3, 1, 1, 1, 1, 6, 3, 3]
def baseStart_1691620 : Nat := 118140960795 + 1691620 * 2 ^ 59
def prefixEnd_1691620 : Nat := 4983230072969 + 3 ^ 40 * 1691620 * 2
def baseEnd_1691620 : Nat := 386050731003900783409061

theorem tailTrace_1691620 : CollatzResearch.WordTrace tailWord_1691620 prefixEnd_1691620 386050731003900783409061 := by
  unfold tailWord_1691620
  simp only [CollatzResearch.WordTrace]
  refine ⟨30849225065778560270076157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41132300087704747026768209 30849225065778560270076157)
  ·
    refine ⟨11568459399666960101278559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30849225065778560270076157 11568459399666960101278559)
    ·
      refine ⟨17352689099500440151917839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11568459399666960101278559 17352689099500440151917839)
      ·
        refine ⟨26029033649250660227876759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17352689099500440151917839 26029033649250660227876759)
        ·
          refine ⟨39043550473875990341815139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26029033649250660227876759 39043550473875990341815139)
          ·
            refine ⟨58565325710813985512722709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39043550473875990341815139 58565325710813985512722709)
            ·
              refine ⟨2745249642694405570908877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58565325710813985512722709 2745249642694405570908877)
              ·
                refine ⟨1029468616010402089090829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2745249642694405570908877 1029468616010402089090829)
                ·
                  refine ⟨386050731003900783409061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029468616010402089090829 386050731003900783409061)
                  ·
                    rfl

theorem cell21_1691620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_1691620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691620 prefixEnd_1691620 := by exact prefixLift 1691620
  have htrace : WordTrace (prefixWord ++ tailWord_1691620) baseStart_1691620 baseEnd_1691620 := by
    simpa [prefixWord, tailWord_1691620, baseEnd_1691620] using wordTrace_append hprefix tailTrace_1691620
  have hstable : (prefixWord ++ tailWord_1691620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691620).length < 2 ^ (prefixWord ++ tailWord_1691620).sum := by decide
  have hdescent : baseEnd_1691620 < baseStart_1691620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691631 : List Nat := [1, 1, 2, 1, 4, 2, 10]
def baseStart_1691631 : Nat := 118140960795 + 1691631 * 2 ^ 59
def prefixEnd_1691631 : Nat := 4983230072969 + 3 ^ 40 * 1691631 * 2
def baseEnd_1691631 : Nat := 42894804594863023191745

theorem tailTrace_1691631 : CollatzResearch.WordTrace tailWord_1691631 prefixEnd_1691631 42894804594863023191745 := by
  unfold tailWord_1691631
  simp only [CollatzResearch.WordTrace]
  refine ⟨61698851334517269418802747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41132567556344846279201831 61698851334517269418802747)
  ·
    refine ⟨92548277001775904128204121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61698851334517269418802747 92548277001775904128204121)
    ·
      refine ⟨69411207751331928096153091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92548277001775904128204121 69411207751331928096153091)
      ·
        refine ⟨104116811626997892144229637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69411207751331928096153091 104116811626997892144229637)
        ·
          refine ⟨19521902180062104777043057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104116811626997892144229637 19521902180062104777043057)
          ·
            refine ⟨14641426635046578582782293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19521902180062104777043057 14641426635046578582782293)
            ·
              refine ⟨42894804594863023191745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14641426635046578582782293 42894804594863023191745)
              ·
                rfl

theorem cell21_1691631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 10].length) (baseStart_1691631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691631 prefixEnd_1691631 := by exact prefixLift 1691631
  have htrace : WordTrace (prefixWord ++ tailWord_1691631) baseStart_1691631 baseEnd_1691631 := by
    simpa [prefixWord, tailWord_1691631, baseEnd_1691631] using wordTrace_append hprefix tailTrace_1691631
  have hstable : (prefixWord ++ tailWord_1691631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691631).length < 2 ^ (prefixWord ++ tailWord_1691631).sum := by decide
  have hdescent : baseEnd_1691631 < baseStart_1691631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691783 : List Nat := [1, 1, 4, 2, 1, 1, 2, 9]
def baseStart_1691783 : Nat := 118140960795 + 1691783 * 2 ^ 59
def prefixEnd_1691783 : Nat := 4983230072969 + 3 ^ 40 * 1691783 * 2
def baseEnd_1691783 : Nat := 128695976608216240730687

theorem tailTrace_1691783 : CollatzResearch.WordTrace tailWord_1691783 prefixEnd_1691783 128695976608216240730687 := by
  unfold tailWord_1691783
  simp only [CollatzResearch.WordTrace]
  refine ⟨61704395229966599378336003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41136263486644399585557335 61704395229966599378336003)
  ·
    refine ⟨92556592844949899067504005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61704395229966599378336003 92556592844949899067504005)
    ·
      refine ⟨17354361158428106075157001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92556592844949899067504005 17354361158428106075157001)
      ·
        refine ⟨13015770868821079556367751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17354361158428106075157001 13015770868821079556367751)
        ·
          refine ⟨19523656303231619334551627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13015770868821079556367751 19523656303231619334551627)
          ·
            refine ⟨29285484454847429001827441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19523656303231619334551627 29285484454847429001827441)
            ·
              refine ⟨21964113341135571751370581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29285484454847429001827441 21964113341135571751370581)
              ·
                refine ⟨128695976608216240730687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21964113341135571751370581 128695976608216240730687)
                ·
                  rfl

theorem cell21_1691783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 9].length) (baseStart_1691783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691783 prefixEnd_1691783 := by exact prefixLift 1691783
  have htrace : WordTrace (prefixWord ++ tailWord_1691783) baseStart_1691783 baseEnd_1691783 := by
    simpa [prefixWord, tailWord_1691783, baseEnd_1691783] using wordTrace_append hprefix tailTrace_1691783
  have hstable : (prefixWord ++ tailWord_1691783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691783).length < 2 ^ (prefixWord ++ tailWord_1691783).sum := by decide
  have hdescent : baseEnd_1691783 < baseStart_1691783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691800 : List Nat := [2, 1, 2, 4, 3, 1, 8]
def baseStart_1691800 : Nat := 118140960795 + 1691800 * 2 ^ 59
def prefixEnd_1691800 : Nat := 4983230072969 + 3 ^ 40 * 1691800 * 2
def baseEnd_1691800 : Nat := 42899089939584496712077

theorem tailTrace_1691800 : CollatzResearch.WordTrace tailWord_1691800 prefixEnd_1691800 42899089939584496712077 := by
  unfold tailWord_1691800
  simp only [CollatzResearch.WordTrace]
  refine ⟨30852507635452505640852427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41136676847270007521136569 30852507635452505640852427)
  ·
    refine ⟨46278761453178758461278641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30852507635452505640852427 46278761453178758461278641)
    ·
      refine ⟨34709071089884068845958981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46278761453178758461278641 34709071089884068845958981)
      ·
        refine ⟨6507950829353262908617309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34709071089884068845958981 6507950829353262908617309)
        ·
          refine ⟨2440481561007473590731491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6507950829353262908617309 2440481561007473590731491)
          ·
            refine ⟨3660722341511210386097237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440481561007473590731491 3660722341511210386097237)
            ·
              refine ⟨42899089939584496712077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3660722341511210386097237 42899089939584496712077)
              ·
                rfl

theorem cell21_1691800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 8].length) (baseStart_1691800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691800 prefixEnd_1691800 := by exact prefixLift 1691800
  have htrace : WordTrace (prefixWord ++ tailWord_1691800) baseStart_1691800 baseEnd_1691800 := by
    simpa [prefixWord, tailWord_1691800, baseEnd_1691800] using wordTrace_append hprefix tailTrace_1691800
  have hstable : (prefixWord ++ tailWord_1691800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691800).length < 2 ^ (prefixWord ++ tailWord_1691800).sum := by decide
  have hdescent : baseEnd_1691800 < baseStart_1691800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691879 : List Nat := [1, 1, 5, 3, 1, 1, 4, 1, 4]
def baseStart_1691879 : Nat := 118140960795 + 1691879 * 2 ^ 59
def prefixEnd_1691879 : Nat := 4983230072969 + 3 ^ 40 * 1691879 * 2
def baseEnd_1691879 : Nat := 386109838332573888591865

theorem tailTrace_1691879 : CollatzResearch.WordTrace tailWord_1691879 prefixEnd_1691879 386109838332573888591865 := by
  unfold tailWord_1691879
  simp only [CollatzResearch.WordTrace]
  refine ⟨61707896637618807773830691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41138597758412538515887127 61707896637618807773830691)
  ·
    refine ⟨92561844956428211660746037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61707896637618807773830691 92561844956428211660746037)
    ·
      refine ⟨8677672964665144843194941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92561844956428211660746037 8677672964665144843194941)
      ·
        refine ⟨3254127361749429316198103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8677672964665144843194941 3254127361749429316198103)
        ·
          refine ⟨4881191042624143974297155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3254127361749429316198103 4881191042624143974297155)
          ·
            refine ⟨7321786563936215961445733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4881191042624143974297155 7321786563936215961445733)
            ·
              refine ⟨1372834980738040492771075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7321786563936215961445733 1372834980738040492771075)
              ·
                refine ⟨2059252471107060739156613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372834980738040492771075 2059252471107060739156613)
                ·
                  refine ⟨386109838332573888591865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2059252471107060739156613 386109838332573888591865)
                  ·
                    rfl

theorem cell21_1691879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 4].length) (baseStart_1691879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691879 prefixEnd_1691879 := by exact prefixLift 1691879
  have htrace : WordTrace (prefixWord ++ tailWord_1691879) baseStart_1691879 baseEnd_1691879 := by
    simpa [prefixWord, tailWord_1691879, baseEnd_1691879] using wordTrace_append hprefix tailTrace_1691879
  have hstable : (prefixWord ++ tailWord_1691879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691879).length < 2 ^ (prefixWord ++ tailWord_1691879).sum := by decide
  have hdescent : baseEnd_1691879 < baseStart_1691879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691904 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 8]
def baseStart_1691904 : Nat := 118140960795 + 1691904 * 2 ^ 59
def prefixEnd_1691904 : Nat := 4983230072969 + 3 ^ 40 * 1691904 * 2
def baseEnd_1691904 : Nat := 386115543673179400675147

theorem tailTrace_1691904 : CollatzResearch.WordTrace tailWord_1691904 prefixEnd_1691904 386115543673179400675147 := by
  unfold tailWord_1691904
  simp only [CollatzResearch.WordTrace]
  refine ⟨30854404231264118521745383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41139205641685491362327177 30854404231264118521745383)
  ·
    refine ⟨46281606346896177782618075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30854404231264118521745383 46281606346896177782618075)
    ·
      refine ⟨69422409520344266673927113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46281606346896177782618075 69422409520344266673927113)
      ·
        refine ⟨52066807140258200005445335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69422409520344266673927113 52066807140258200005445335)
        ·
          refine ⟨78100210710387300008168003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52066807140258200005445335 78100210710387300008168003)
          ·
            refine ⟨117150316065580950012252005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78100210710387300008168003 117150316065580950012252005)
            ·
              refine ⟨21965684262296428127297251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117150316065580950012252005 21965684262296428127297251)
              ·
                refine ⟨32948526393444642190945877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21965684262296428127297251 32948526393444642190945877)
                ·
                  refine ⟨386115543673179400675147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32948526393444642190945877 386115543673179400675147)
                  ·
                    rfl

theorem cell21_1691904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_1691904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691904 prefixEnd_1691904 := by exact prefixLift 1691904
  have htrace : WordTrace (prefixWord ++ tailWord_1691904) baseStart_1691904 baseEnd_1691904 := by
    simpa [prefixWord, tailWord_1691904, baseEnd_1691904] using wordTrace_append hprefix tailTrace_1691904
  have hstable : (prefixWord ++ tailWord_1691904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691904).length < 2 ^ (prefixWord ++ tailWord_1691904).sum := by decide
  have hdescent : baseEnd_1691904 < baseStart_1691904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691907 : List Nat := [1, 1, 1, 3, 2, 3, 2, 5, 3]
def baseStart_1691907 : Nat := 118140960795 + 1691907 * 2 ^ 59
def prefixEnd_1691907 : Nat := 4983230072969 + 3 ^ 40 * 1691907 * 2
def baseEnd_1691907 : Nat := 386116228314052062125141

theorem tailTrace_1691907 : CollatzResearch.WordTrace tailWord_1691907 prefixEnd_1691907 386116228314052062125141 := by
  unfold tailWord_1691907
  simp only [CollatzResearch.WordTrace]
  refine ⟨61708917881517368555849975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41139278587678245703899983 61708917881517368555849975)
  ·
    refine ⟨92563376822276052833774963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61708917881517368555849975 92563376822276052833774963)
    ·
      refine ⟨138845065233414079250662445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92563376822276052833774963 138845065233414079250662445)
      ·
        refine ⟨52066899462530279718998417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138845065233414079250662445 52066899462530279718998417)
        ·
          refine ⟨39050174596897709789248813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52066899462530279718998417 39050174596897709789248813)
          ·
            refine ⟨14643815473836641170968305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39050174596897709789248813 14643815473836641170968305)
            ·
              refine ⟨10982861605377480878226229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14643815473836641170968305 10982861605377480878226229)
              ·
                refine ⟨1029643275504138832333709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10982861605377480878226229 1029643275504138832333709)
                ·
                  refine ⟨386116228314052062125141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029643275504138832333709 386116228314052062125141)
                  ·
                    rfl

theorem cell21_1691907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 3].length) (baseStart_1691907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691907 prefixEnd_1691907 := by exact prefixLift 1691907
  have htrace : WordTrace (prefixWord ++ tailWord_1691907) baseStart_1691907 baseEnd_1691907 := by
    simpa [prefixWord, tailWord_1691907, baseEnd_1691907] using wordTrace_append hprefix tailTrace_1691907
  have hstable : (prefixWord ++ tailWord_1691907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691907).length < 2 ^ (prefixWord ++ tailWord_1691907).sum := by decide
  have hdescent : baseEnd_1691907 < baseStart_1691907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691921 : List Nat := [1, 2, 2, 1, 1, 5, 1, 4, 4]
def baseStart_1691921 : Nat := 118140960795 + 1691921 * 2 ^ 59
def prefixEnd_1691921 : Nat := 4983230072969 + 3 ^ 40 * 1691921 * 2
def baseEnd_1691921 : Nat := 386119423304791148891779

theorem tailTrace_1691921 : CollatzResearch.WordTrace tailWord_1691921 prefixEnd_1691921 386119423304791148891779 := by
  unfold tailWord_1691921
  simp only [CollatzResearch.WordTrace]
  refine ⟨61709428503466648946859617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41139619002311099297906411 61709428503466648946859617)
  ·
    refine ⟨46282071377599986710144713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61709428503466648946859617 46282071377599986710144713)
    ·
      refine ⟨34711553533199990032608535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46282071377599986710144713 34711553533199990032608535)
      ·
        refine ⟨52067330299799985048912803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34711553533199990032608535 52067330299799985048912803)
        ·
          refine ⟨78100995449699977573369205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52067330299799985048912803 78100995449699977573369205)
          ·
            refine ⟨7321968323409372897503363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78100995449699977573369205 7321968323409372897503363)
            ·
              refine ⟨10982952485114059346255045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7321968323409372897503363 10982952485114059346255045)
              ·
                refine ⟨2059303590958886127422821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10982952485114059346255045 2059303590958886127422821)
                ·
                  refine ⟨386119423304791148891779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2059303590958886127422821 386119423304791148891779)
                  ·
                    rfl

theorem cell21_1691921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_1691921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691921 prefixEnd_1691921 := by exact prefixLift 1691921
  have htrace : WordTrace (prefixWord ++ tailWord_1691921) baseStart_1691921 baseEnd_1691921 := by
    simpa [prefixWord, tailWord_1691921, baseEnd_1691921] using wordTrace_append hprefix tailTrace_1691921
  have hstable : (prefixWord ++ tailWord_1691921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691921).length < 2 ^ (prefixWord ++ tailWord_1691921).sum := by decide
  have hdescent : baseEnd_1691921 < baseStart_1691921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691938 : List Nat := [3, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_1691938 : Nat := 118140960795 + 1691938 * 2 ^ 59
def prefixEnd_1691938 : Nat := 4983230072969 + 3 ^ 40 * 1691938 * 2
def baseEnd_1691938 : Nat := 386123302936402897108411

theorem tailTrace_1691938 : CollatzResearch.WordTrace tailWord_1691938 prefixEnd_1691938 386123302936402897108411 := by
  unfold tailWord_1691938
  simp only [CollatzResearch.WordTrace]
  refine ⟨15427512136101265212557117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41140032362936707233485645 15427512136101265212557117)
  ·
    refine ⟨5785317051037974454708919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15427512136101265212557117 5785317051037974454708919)
    ·
      refine ⟨8677975576556961682063379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5785317051037974454708919 8677975576556961682063379)
      ·
        refine ⟨13016963364835442523095069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8677975576556961682063379 13016963364835442523095069)
        ·
          refine ⟨4881361261813290946160651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13016963364835442523095069 4881361261813290946160651)
          ·
            refine ⟨7322041892719936419240977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4881361261813290946160651 7322041892719936419240977)
            ·
              refine ⟨5491531419539952314430733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7322041892719936419240977 5491531419539952314430733)
              ·
                refine ⟨2059324282327482117911525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5491531419539952314430733 2059324282327482117911525)
                ·
                  refine ⟨386123302936402897108411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2059324282327482117911525 386123302936402897108411)
                  ·
                    rfl

theorem cell21_1691938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_1691938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691938 prefixEnd_1691938 := by exact prefixLift 1691938
  have htrace : WordTrace (prefixWord ++ tailWord_1691938) baseStart_1691938 baseEnd_1691938 := by
    simpa [prefixWord, tailWord_1691938, baseEnd_1691938] using wordTrace_append hprefix tailTrace_1691938
  have hstable : (prefixWord ++ tailWord_1691938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691938).length < 2 ^ (prefixWord ++ tailWord_1691938).sum := by decide
  have hdescent : baseEnd_1691938 < baseStart_1691938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691972 : List Nat := [2, 3, 4, 1, 2, 2, 1, 2, 4]
def baseStart_1691972 : Nat := 118140960795 + 1691972 * 2 ^ 59
def prefixEnd_1691972 : Nat := 4983230072969 + 3 ^ 40 * 1691972 * 2
def baseEnd_1691972 : Nat := 386131062199626393541675

theorem tailTrace_1691972 : CollatzResearch.WordTrace tailWord_1691972 prefixEnd_1691972 386131062199626393541675 := by
  unfold tailWord_1691972
  simp only [CollatzResearch.WordTrace]
  refine ⟨30855644313140942328483085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41140859084187923104644113 30855644313140942328483085)
  ·
    refine ⟨11570866617427853373181157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30855644313140942328483085 11570866617427853373181157)
    ·
      refine ⟨2169537490767722507471467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11570866617427853373181157 2169537490767722507471467)
      ·
        refine ⟨3254306236151583761207201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2169537490767722507471467 3254306236151583761207201)
        ·
          refine ⟨2440729677113687820905401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3254306236151583761207201 2440729677113687820905401)
          ·
            refine ⟨1830547257835265865679051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2440729677113687820905401 1830547257835265865679051)
            ·
              refine ⟨2745820886752898798518577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830547257835265865679051 2745820886752898798518577)
              ·
                refine ⟨2059365665064674098888933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2745820886752898798518577 2059365665064674098888933)
                ·
                  refine ⟨386131062199626393541675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2059365665064674098888933 386131062199626393541675)
                  ·
                    rfl

theorem cell21_1691972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_1691972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1691972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1691972 prefixEnd_1691972 := by exact prefixLift 1691972
  have htrace : WordTrace (prefixWord ++ tailWord_1691972) baseStart_1691972 baseEnd_1691972 := by
    simpa [prefixWord, tailWord_1691972, baseEnd_1691972] using wordTrace_append hprefix tailTrace_1691972
  have hstable : (prefixWord ++ tailWord_1691972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691972).length < 2 ^ (prefixWord ++ tailWord_1691972).sum := by decide
  have hdescent : baseEnd_1691972 < baseStart_1691972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692034 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1692034 : Nat := 118140960795 + 1692034 * 2 ^ 59
def prefixEnd_1692034 : Nat := 4983230072969 + 3 ^ 40 * 1692034 * 2
def baseEnd_1692034 : Nat := 386145211444328063508215

theorem tailTrace_1692034 : CollatzResearch.WordTrace tailWord_1692034 prefixEnd_1692034 386145211444328063508215 := by
  unfold tailWord_1692034
  simp only [CollatzResearch.WordTrace]
  refine ⟨15428387488014317311430789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41142366634704846163815437 15428387488014317311430789)
  ·
    refine ⟨2892822654002684495893273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15428387488014317311430789 2892822654002684495893273)
    ·
      refine ⟨2169616990502013371919955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2892822654002684495893273 2169616990502013371919955)
      ·
        refine ⟨3254425485753020057879933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2169616990502013371919955 3254425485753020057879933)
        ·
          refine ⟨1220409557157382521704975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3254425485753020057879933 1220409557157382521704975)
          ·
            refine ⟨1830614335736073782557463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220409557157382521704975 1830614335736073782557463)
            ·
              refine ⟨2745921503604110673836195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830614335736073782557463 2745921503604110673836195)
              ·
                refine ⟨4118882255406166010754293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2745921503604110673836195 4118882255406166010754293)
                ·
                  refine ⟨386145211444328063508215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4118882255406166010754293 386145211444328063508215)
                  ·
                    rfl

theorem cell21_1692034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1692034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692034 prefixEnd_1692034 := by exact prefixLift 1692034
  have htrace : WordTrace (prefixWord ++ tailWord_1692034) baseStart_1692034 baseEnd_1692034 := by
    simpa [prefixWord, tailWord_1692034, baseEnd_1692034] using wordTrace_append hprefix tailTrace_1692034
  have hstable : (prefixWord ++ tailWord_1692034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692034).length < 2 ^ (prefixWord ++ tailWord_1692034).sum := by decide
  have hdescent : baseEnd_1692034 < baseStart_1692034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692093 : List Nat := [1, 4, 1, 2, 2, 4, 2, 2, 3]
def baseStart_1692093 : Nat := 118140960795 + 1692093 * 2 ^ 59
def prefixEnd_1692093 : Nat := 4983230072969 + 3 ^ 40 * 1692093 * 2
def baseEnd_1692093 : Nat := 386158676048157072024761

theorem tailTrace_1692093 : CollatzResearch.WordTrace tailWord_1692093 prefixEnd_1692093 386158676048157072024761 := by
  unfold tailWord_1692093
  simp only [CollatzResearch.WordTrace]
  refine ⟨61715701858843522322120933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41143801239229014881413955 61715701858843522322120933)
  ·
    refine ⟨11571694098533160435397675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61715701858843522322120933 11571694098533160435397675)
    ·
      refine ⟨17357541147799740653096513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11571694098533160435397675 17357541147799740653096513)
      ·
        refine ⟨13018155860849805489822385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17357541147799740653096513 13018155860849805489822385)
        ·
          refine ⟨9763616895637354117366789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13018155860849805489822385 9763616895637354117366789)
          ·
            refine ⟨1830678167932003897006273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9763616895637354117366789 1830678167932003897006273)
            ·
              refine ⟨1373008625949002922754705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830678167932003897006273 1373008625949002922754705)
              ·
                refine ⟨1029756469461752192066029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373008625949002922754705 1029756469461752192066029)
                ·
                  refine ⟨386158676048157072024761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029756469461752192066029 386158676048157072024761)
                  ·
                    rfl

theorem cell21_1692093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_1692093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692093 prefixEnd_1692093 := by exact prefixLift 1692093
  have htrace : WordTrace (prefixWord ++ tailWord_1692093) baseStart_1692093 baseEnd_1692093 := by
    simpa [prefixWord, tailWord_1692093, baseEnd_1692093] using wordTrace_append hprefix tailTrace_1692093
  have hstable : (prefixWord ++ tailWord_1692093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692093).length < 2 ^ (prefixWord ++ tailWord_1692093).sum := by decide
  have hdescent : baseEnd_1692093 < baseStart_1692093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692101 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 11]
def baseStart_1692101 : Nat := 118140960795 + 1692101 * 2 ^ 59
def prefixEnd_1692101 : Nat := 4983230072969 + 3 ^ 40 * 1692101 * 2
def baseEnd_1692101 : Nat := 386160501757150835891411

theorem tailTrace_1692101 : CollatzResearch.WordTrace tailWord_1692101 prefixEnd_1692101 386160501757150835891411 := by
  unfold tailWord_1692101
  simp only [CollatzResearch.WordTrace]
  refine ⟨61715993642814539688412157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41143995761876359792274771 61715993642814539688412157)
  ·
    refine ⟨23143497616055452383154559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61715993642814539688412157 23143497616055452383154559)
    ·
      refine ⟨34715246424083178574731839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23143497616055452383154559 34715246424083178574731839)
      ·
        refine ⟨52072869636124767862097759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34715246424083178574731839 52072869636124767862097759)
        ·
          refine ⟨78109304454187151793146639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52072869636124767862097759 78109304454187151793146639)
          ·
            refine ⟨117163956681280727689719959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78109304454187151793146639 117163956681280727689719959)
            ·
              refine ⟨175745935021921091534579939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117163956681280727689719959 175745935021921091534579939)
              ·
                refine ⟨263618902532881637301869909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175745935021921091534579939 263618902532881637301869909)
                ·
                  refine ⟨386160501757150835891411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 263618902532881637301869909 386160501757150835891411)
                  ·
                    rfl

theorem cell21_1692101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_1692101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692101 prefixEnd_1692101 := by exact prefixLift 1692101
  have htrace : WordTrace (prefixWord ++ tailWord_1692101) baseStart_1692101 baseEnd_1692101 := by
    simpa [prefixWord, tailWord_1692101, baseEnd_1692101] using wordTrace_append hprefix tailTrace_1692101
  have hstable : (prefixWord ++ tailWord_1692101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692101).length < 2 ^ (prefixWord ++ tailWord_1692101).sum := by decide
  have hdescent : baseEnd_1692101 < baseStart_1692101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692104 : List Nat := [2, 1, 3, 1, 3, 4, 1, 6]
def baseStart_1692104 : Nat := 118140960795 + 1692104 * 2 ^ 59
def prefixEnd_1692104 : Nat := 4983230072969 + 3 ^ 40 * 1692104 * 2
def baseEnd_1692104 : Nat := 128720395466007832447135

theorem tailTrace_1692104 : CollatzResearch.WordTrace tailWord_1692104 prefixEnd_1692104 128720395466007832447135 := by
  unfold tailWord_1692104
  simp only [CollatzResearch.WordTrace]
  refine ⟨30858051530901835600385683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41144068707869114133847577 30858051530901835600385683)
  ·
    refine ⟨46287077296352753400578525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30858051530901835600385683 46287077296352753400578525)
    ·
      refine ⟨17357653986132282525216947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46287077296352753400578525 17357653986132282525216947)
      ·
        refine ⟨26036480979198423787825421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17357653986132282525216947 26036480979198423787825421)
        ·
          refine ⟨9763680367199408920434533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26036480979198423787825421 9763680367199408920434533)
          ·
            refine ⟨1830690068849889172581475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9763680367199408920434533 1830690068849889172581475)
            ·
              refine ⟨2746035103274833758872213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830690068849889172581475 2746035103274833758872213)
              ·
                refine ⟨128720395466007832447135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2746035103274833758872213 128720395466007832447135)
                ·
                  rfl

theorem cell21_1692104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 6].length) (baseStart_1692104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692104 prefixEnd_1692104 := by exact prefixLift 1692104
  have htrace : WordTrace (prefixWord ++ tailWord_1692104) baseStart_1692104 baseEnd_1692104 := by
    simpa [prefixWord, tailWord_1692104, baseEnd_1692104] using wordTrace_append hprefix tailTrace_1692104
  have hstable : (prefixWord ++ tailWord_1692104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692104).length < 2 ^ (prefixWord ++ tailWord_1692104).sum := by decide
  have hdescent : baseEnd_1692104 < baseStart_1692104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692177 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 7]
def baseStart_1692177 : Nat := 118140960795 + 1692177 * 2 ^ 59
def prefixEnd_1692177 : Nat := 4983230072969 + 3 ^ 40 * 1692177 * 2
def baseEnd_1692177 : Nat := 386177845992591592624589

theorem tailTrace_1692177 : CollatzResearch.WordTrace tailWord_1692177 prefixEnd_1692177 386177845992591592624589 := by
  unfold tailWord_1692177
  simp only [CollatzResearch.WordTrace]
  refine ⟨61718765590539204668178785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41145843727026136445452523 61718765590539204668178785)
  ·
    refine ⟨46289074192904403501134089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61718765590539204668178785 46289074192904403501134089)
    ·
      refine ⟨34716805644678302625850567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46289074192904403501134089 34716805644678302625850567)
      ·
        refine ⟨52075208467017453938775851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34716805644678302625850567 52075208467017453938775851)
        ·
          refine ⟨78112812700526180908163777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52075208467017453938775851 78112812700526180908163777)
          ·
            refine ⟨58584609525394635681122833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78112812700526180908163777 58584609525394635681122833)
            ·
              refine ⟨43938457144045976760842125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58584609525394635681122833 43938457144045976760842125)
              ·
                refine ⟨16476921429017241285315797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43938457144045976760842125 16476921429017241285315797)
                ·
                  refine ⟨386177845992591592624589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16476921429017241285315797 386177845992591592624589)
                  ·
                    rfl

theorem cell21_1692177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_1692177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692177 prefixEnd_1692177 := by exact prefixLift 1692177
  have htrace : WordTrace (prefixWord ++ tailWord_1692177) baseStart_1692177 baseEnd_1692177 := by
    simpa [prefixWord, tailWord_1692177, baseEnd_1692177] using wordTrace_append hprefix tailTrace_1692177
  have hstable : (prefixWord ++ tailWord_1692177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692177).length < 2 ^ (prefixWord ++ tailWord_1692177).sum := by decide
  have hdescent : baseEnd_1692177 < baseStart_1692177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692208 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 6]
def baseStart_1692208 : Nat := 118140960795 + 1692208 * 2 ^ 59
def prefixEnd_1692208 : Nat := 4983230072969 + 3 ^ 40 * 1692208 * 2
def baseEnd_1692208 : Nat := 386184920614942427607859

theorem tailTrace_1692208 : CollatzResearch.WordTrace tailWord_1692208 prefixEnd_1692208 386184920614942427607859 := by
  unfold tailWord_1692208
  simp only [CollatzResearch.WordTrace]
  refine ⟨30859948126713448481278639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41146597502284597975038185 30859948126713448481278639)
  ·
    refine ⟨46289922190070172721917959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30859948126713448481278639 46289922190070172721917959)
    ·
      refine ⟨69434883285105259082876939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46289922190070172721917959 69434883285105259082876939)
      ·
        refine ⟨104152324927657888624315409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69434883285105259082876939 104152324927657888624315409)
        ·
          refine ⟨78114243695743416468236557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104152324927657888624315409 78114243695743416468236557)
          ·
            refine ⟨29292841385903781175588709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78114243695743416468236557 29292841385903781175588709)
            ·
              refine ⟨5492407759856958970422883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29292841385903781175588709 5492407759856958970422883)
              ·
                refine ⟨8238611639785438455634325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5492407759856958970422883 8238611639785438455634325)
                ·
                  refine ⟨386184920614942427607859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8238611639785438455634325 386184920614942427607859)
                  ·
                    rfl

theorem cell21_1692208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_1692208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692208 prefixEnd_1692208 := by exact prefixLift 1692208
  have htrace : WordTrace (prefixWord ++ tailWord_1692208) baseStart_1692208 baseEnd_1692208 := by
    simpa [prefixWord, tailWord_1692208, baseEnd_1692208] using wordTrace_append hprefix tailTrace_1692208
  have hstable : (prefixWord ++ tailWord_1692208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692208).length < 2 ^ (prefixWord ++ tailWord_1692208).sum := by decide
  have hdescent : baseEnd_1692208 < baseStart_1692208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692329 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 5]
def baseStart_1692329 : Nat := 118140960795 + 1692329 * 2 ^ 59
def prefixEnd_1692329 : Nat := 4983230072969 + 3 ^ 40 * 1692329 * 2
def baseEnd_1692329 : Nat := 386212534463473106090945

theorem tailTrace_1692329 : CollatzResearch.WordTrace tailWord_1692329 prefixEnd_1692329 386212534463473106090945 := by
  unfold tailWord_1692329
  simp only [CollatzResearch.WordTrace]
  refine ⟨61724309485988534627712041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41149539657325689751808027 61724309485988534627712041)
  ·
    refine ⟨46293232114491400970784031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61724309485988534627712041 46293232114491400970784031)
    ·
      refine ⟨69439848171737101456176047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46293232114491400970784031 69439848171737101456176047)
      ·
        refine ⟨104159772257605652184264071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69439848171737101456176047 104159772257605652184264071)
        ·
          refine ⟨156239658386408478276396107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104159772257605652184264071 156239658386408478276396107)
          ·
            refine ⟨234359487579612717414594161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156239658386408478276396107 234359487579612717414594161)
            ·
              refine ⟨175769615684709538060945621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234359487579612717414594161 175769615684709538060945621)
              ·
                refine ⟨4119600367610379798303413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 175769615684709538060945621 4119600367610379798303413)
                ·
                  refine ⟨386212534463473106090945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4119600367610379798303413 386212534463473106090945)
                  ·
                    rfl

theorem cell21_1692329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_1692329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692329 prefixEnd_1692329 := by exact prefixLift 1692329
  have htrace : WordTrace (prefixWord ++ tailWord_1692329) baseStart_1692329 baseEnd_1692329 := by
    simpa [prefixWord, tailWord_1692329, baseEnd_1692329] using wordTrace_append hprefix tailTrace_1692329
  have hstable : (prefixWord ++ tailWord_1692329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692329).length < 2 ^ (prefixWord ++ tailWord_1692329).sum := by decide
  have hdescent : baseEnd_1692329 < baseStart_1692329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692360 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 6]
def baseStart_1692360 : Nat := 118140960795 + 1692360 * 2 ^ 59
def prefixEnd_1692360 : Nat := 4983230072969 + 3 ^ 40 * 1692360 * 2
def baseEnd_1692360 : Nat := 386219609085823941074215

theorem tailTrace_1692360 : CollatzResearch.WordTrace tailWord_1692360 prefixEnd_1692360 386219609085823941074215 := by
  unfold tailWord_1692360
  simp only [CollatzResearch.WordTrace]
  refine ⟨30862720074438113461045267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41150293432584151281393689 30862720074438113461045267)
  ·
    refine ⟨46294080111657170191567901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30862720074438113461045267 46294080111657170191567901)
    ·
      refine ⟨17360280041871438821837963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46294080111657170191567901 17360280041871438821837963)
      ·
        refine ⟨26040420062807158232756945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17360280041871438821837963 26040420062807158232756945)
        ·
          refine ⟨19530315047105368674567709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26040420062807158232756945 19530315047105368674567709)
          ·
            refine ⟨7323868142664513252962891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19530315047105368674567709 7323868142664513252962891)
            ·
              refine ⟨10985802213996769879444337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7323868142664513252962891 10985802213996769879444337)
              ·
                refine ⟨8239351660497577409583253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10985802213996769879444337 8239351660497577409583253)
                ·
                  refine ⟨386219609085823941074215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8239351660497577409583253 386219609085823941074215)
                  ·
                    rfl

theorem cell21_1692360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_1692360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692360 prefixEnd_1692360 := by exact prefixLift 1692360
  have htrace : WordTrace (prefixWord ++ tailWord_1692360) baseStart_1692360 baseEnd_1692360 := by
    simpa [prefixWord, tailWord_1692360, baseEnd_1692360] using wordTrace_append hprefix tailTrace_1692360
  have hstable : (prefixWord ++ tailWord_1692360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692360).length < 2 ^ (prefixWord ++ tailWord_1692360).sum := by decide
  have hdescent : baseEnd_1692360 < baseStart_1692360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692380 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 5]
def baseStart_1692380 : Nat := 118140960795 + 1692380 * 2 ^ 59
def prefixEnd_1692380 : Nat := 4983230072969 + 3 ^ 40 * 1692380 * 2
def baseEnd_1692380 : Nat := 386224173358308350740841

theorem tailTrace_1692380 : CollatzResearch.WordTrace tailWord_1692380 prefixEnd_1692380 386224173358308350740841 := by
  unfold tailWord_1692380
  simp only [CollatzResearch.WordTrace]
  refine ⟨30863084804401885168909297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41150779739202513558545729 30863084804401885168909297)
  ·
    refine ⟨23147313603301413876681973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30863084804401885168909297 23147313603301413876681973)
    ·
      refine ⟨2170060650309507550938935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23147313603301413876681973 2170060650309507550938935)
      ·
        refine ⟨3255090975464261326408403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2170060650309507550938935 3255090975464261326408403)
        ·
          refine ⟨4882636463196391989612605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3255090975464261326408403 4882636463196391989612605)
          ·
            refine ⟨1830988673698646996104727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4882636463196391989612605 1830988673698646996104727)
            ·
              refine ⟨2746483010547970494157091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830988673698646996104727 2746483010547970494157091)
              ·
                refine ⟨4119724515821955741235637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2746483010547970494157091 4119724515821955741235637)
                ·
                  refine ⟨386224173358308350740841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4119724515821955741235637 386224173358308350740841)
                  ·
                    rfl

theorem cell21_1692380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_1692380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692380 prefixEnd_1692380 := by exact prefixLift 1692380
  have htrace : WordTrace (prefixWord ++ tailWord_1692380) baseStart_1692380 baseEnd_1692380 := by
    simpa [prefixWord, tailWord_1692380, baseEnd_1692380] using wordTrace_append hprefix tailTrace_1692380
  have hstable : (prefixWord ++ tailWord_1692380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692380).length < 2 ^ (prefixWord ++ tailWord_1692380).sum := by decide
  have hdescent : baseEnd_1692380 < baseStart_1692380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692498 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_1692498 : Nat := 118140960795 + 1692498 * 2 ^ 59
def prefixEnd_1692498 : Nat := 4983230072969 + 3 ^ 40 * 1692498 * 2
def baseEnd_1692498 : Nat := 386251102565966367773933

theorem tailTrace_1692498 : CollatzResearch.WordTrace tailWord_1692498 prefixEnd_1692498 386251102565966367773933 := by
  unfold tailWord_1692498
  simp only [CollatzResearch.WordTrace]
  refine ⟨15432618355594069122653537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41153648948250850993742765 15432618355594069122653537)
  ·
    refine ⟨11574463766695551841990153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15432618355594069122653537 11574463766695551841990153)
    ·
      refine ⟨8680847825021663881492615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11574463766695551841990153 8680847825021663881492615)
      ·
        refine ⟨13021271737532495822238923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8680847825021663881492615 13021271737532495822238923)
        ·
          refine ⟨19531907606298743733358385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13021271737532495822238923 19531907606298743733358385)
          ·
            refine ⟨14648930704724057800018789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19531907606298743733358385 14648930704724057800018789)
            ·
              refine ⟨2746674507135760837503523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14648930704724057800018789 2746674507135760837503523)
              ·
                refine ⟨4120011760703641256255285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2746674507135760837503523 4120011760703641256255285)
                ·
                  refine ⟨386251102565966367773933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4120011760703641256255285 386251102565966367773933)
                  ·
                    rfl

theorem cell21_1692498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_1692498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692498 prefixEnd_1692498 := by exact prefixLift 1692498
  have htrace : WordTrace (prefixWord ++ tailWord_1692498) baseStart_1692498 baseEnd_1692498 := by
    simpa [prefixWord, tailWord_1692498, baseEnd_1692498] using wordTrace_append hprefix tailTrace_1692498
  have hstable : (prefixWord ++ tailWord_1692498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692498).length < 2 ^ (prefixWord ++ tailWord_1692498).sum := by decide
  have hdescent : baseEnd_1692498 < baseStart_1692498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692608 : List Nat := [2, 1, 1, 2, 3, 5, 2, 2, 3]
def baseStart_1692608 : Nat := 118140960795 + 1692608 * 2 ^ 59
def prefixEnd_1692608 : Nat := 4983230072969 + 3 ^ 40 * 1692608 * 2
def baseEnd_1692608 : Nat := 386276206064630620940375

theorem tailTrace_1692608 : CollatzResearch.WordTrace tailWord_1692608 prefixEnd_1692608 386276206064630620940375 := by
  unfold tailWord_1692608
  simp only [CollatzResearch.WordTrace]
  refine ⟨30867242725988882638559239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41156323634651843518078985 30867242725988882638559239)
  ·
    refine ⟨46300864088983323957838859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30867242725988882638559239 46300864088983323957838859)
    ·
      refine ⟨69451296133474985936758289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46300864088983323957838859 69451296133474985936758289)
      ·
        refine ⟨52088472100106239452568717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69451296133474985936758289 52088472100106239452568717)
        ·
          refine ⟨19533177037539839794713269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52088472100106239452568717 19533177037539839794713269)
          ·
            refine ⟨1831235347269359980754369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19533177037539839794713269 1831235347269359980754369)
            ·
              refine ⟨1373426510452019985565777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831235347269359980754369 1373426510452019985565777)
              ·
                refine ⟨1030069882839014989174333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373426510452019985565777 1030069882839014989174333)
                ·
                  refine ⟨386276206064630620940375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030069882839014989174333 386276206064630620940375)
                  ·
                    rfl

theorem cell21_1692608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 3].length) (baseStart_1692608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692608 prefixEnd_1692608 := by exact prefixLift 1692608
  have htrace : WordTrace (prefixWord ++ tailWord_1692608) baseStart_1692608 baseEnd_1692608 := by
    simpa [prefixWord, tailWord_1692608, baseEnd_1692608] using wordTrace_append hprefix tailTrace_1692608
  have hstable : (prefixWord ++ tailWord_1692608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692608).length < 2 ^ (prefixWord ++ tailWord_1692608).sum := by decide
  have hdescent : baseEnd_1692608 < baseStart_1692608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692619 : List Nat := [1, 1, 1, 1, 3, 7, 1, 6]
def baseStart_1692619 : Nat := 118140960795 + 1692619 * 2 ^ 59
def prefixEnd_1692619 : Nat := 4983230072969 + 3 ^ 40 * 1692619 * 2
def baseEnd_1692619 : Nat := 128759572138165682085673

theorem tailTrace_1692619 : CollatzResearch.WordTrace tailWord_1692619 prefixEnd_1692619 128759572138165682085673 := by
  unfold tailWord_1692619
  simp only [CollatzResearch.WordTrace]
  refine ⟨61734886654937914155768911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41156591103291942770512607 61734886654937914155768911)
  ·
    refine ⟨92602329982406871233653367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61734886654937914155768911 92602329982406871233653367)
    ·
      refine ⟨138903494973610306850480051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92602329982406871233653367 138903494973610306850480051)
      ·
        refine ⟨208355242460415460275720077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138903494973610306850480051 208355242460415460275720077)
        ·
          refine ⟨78133215922655797603395029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208355242460415460275720077 78133215922655797603395029)
          ·
            refine ⟨1831247248187245256329571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 78133215922655797603395029 1831247248187245256329571)
            ·
              refine ⟨2746870872280867884494357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831247248187245256329571 2746870872280867884494357)
              ·
                refine ⟨128759572138165682085673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2746870872280867884494357 128759572138165682085673)
                ·
                  rfl

theorem cell21_1692619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 6].length) (baseStart_1692619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692619 prefixEnd_1692619 := by exact prefixLift 1692619
  have htrace : WordTrace (prefixWord ++ tailWord_1692619) baseStart_1692619 baseEnd_1692619 := by
    simpa [prefixWord, tailWord_1692619, baseEnd_1692619] using wordTrace_append hprefix tailTrace_1692619
  have hstable : (prefixWord ++ tailWord_1692619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692619).length < 2 ^ (prefixWord ++ tailWord_1692619).sum := by decide
  have hdescent : baseEnd_1692619 < baseStart_1692619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692633 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 7]
def baseStart_1692633 : Nat := 118140960795 + 1692633 * 2 ^ 59
def prefixEnd_1692633 : Nat := 4983230072969 + 3 ^ 40 * 1692633 * 2
def baseEnd_1692633 : Nat := 386281911405236133023657

theorem tailTrace_1692633 : CollatzResearch.WordTrace tailWord_1692633 prefixEnd_1692633 386281911405236133023657 := by
  unfold tailWord_1692633
  simp only [CollatzResearch.WordTrace]
  refine ⟨61735397276887194546778553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41156931517924796364519035 61735397276887194546778553)
  ·
    refine ⟨46301547957665395910083915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61735397276887194546778553 46301547957665395910083915)
    ·
      refine ⟨69452321936498093865125873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46301547957665395910083915 69452321936498093865125873)
      ·
        refine ⟨52089241452373570398844405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69452321936498093865125873 52089241452373570398844405)
        ·
          refine ⟨4883366386160022224891663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52089241452373570398844405 4883366386160022224891663)
          ·
            refine ⟨7325049579240033337337495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883366386160022224891663 7325049579240033337337495)
            ·
              refine ⟨10987574368860050006006243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7325049579240033337337495 10987574368860050006006243)
              ·
                refine ⟨16481361553290075009009365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10987574368860050006006243 16481361553290075009009365)
                ·
                  refine ⟨386281911405236133023657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16481361553290075009009365 386281911405236133023657)
                  ·
                    rfl

theorem cell21_1692633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_1692633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692633 prefixEnd_1692633 := by exact prefixLift 1692633
  have htrace : WordTrace (prefixWord ++ tailWord_1692633) baseStart_1692633 baseEnd_1692633 := by
    simpa [prefixWord, tailWord_1692633, baseEnd_1692633] using wordTrace_append hprefix tailTrace_1692633
  have hstable : (prefixWord ++ tailWord_1692633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692633).length < 2 ^ (prefixWord ++ tailWord_1692633).sum := by decide
  have hdescent : baseEnd_1692633 < baseStart_1692633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692695 : List Nat := [1, 1, 3, 5, 1, 2, 1, 7]
def baseStart_1692695 : Nat := 118140960795 + 1692695 * 2 ^ 59
def prefixEnd_1692695 : Nat := 4983230072969 + 3 ^ 40 * 1692695 * 2
def baseEnd_1692695 : Nat := 128765353549979267663399

theorem tailTrace_1692695 : CollatzResearch.WordTrace tailWord_1692695 prefixEnd_1692695 128765353549979267663399 := by
  unfold tailWord_1692695
  simp only [CollatzResearch.WordTrace]
  refine ⟨61737658602662579135535539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41158439068441719423690359 61737658602662579135535539)
  ·
    refine ⟨92606487903993868703303309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61737658602662579135535539 92606487903993868703303309)
    ·
      refine ⟨34727432963997700763738741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92606487903993868703303309 34727432963997700763738741)
      ·
        refine ⟨3255696840374784446600507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34727432963997700763738741 3255696840374784446600507)
        ·
          refine ⟨4883545260562176669900761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3255696840374784446600507 4883545260562176669900761)
          ·
            refine ⟨3662658945421632502425571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4883545260562176669900761 3662658945421632502425571)
            ·
              refine ⟨5493988418132448753638357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3662658945421632502425571 5493988418132448753638357)
              ·
                refine ⟨128765353549979267663399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5493988418132448753638357 128765353549979267663399)
                ·
                  rfl

theorem cell21_1692695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 7].length) (baseStart_1692695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692695 prefixEnd_1692695 := by exact prefixLift 1692695
  have htrace : WordTrace (prefixWord ++ tailWord_1692695) baseStart_1692695 baseEnd_1692695 := by
    simpa [prefixWord, tailWord_1692695, baseEnd_1692695] using wordTrace_append hprefix tailTrace_1692695
  have hstable : (prefixWord ++ tailWord_1692695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692695).length < 2 ^ (prefixWord ++ tailWord_1692695).sum := by decide
  have hdescent : baseEnd_1692695 < baseStart_1692695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692701 : List Nat := [1, 4, 2, 2, 4, 1, 1, 3, 3]
def baseStart_1692701 : Nat := 118140960795 + 1692701 * 2 ^ 59
def prefixEnd_1692701 : Nat := 4983230072969 + 3 ^ 40 * 1692701 * 2
def baseEnd_1692701 : Nat := 386297429931683125890185

theorem tailTrace_1692701 : CollatzResearch.WordTrace tailWord_1692701 prefixEnd_1692701 386297429931683125890185 := by
  unfold tailWord_1692701
  simp only [CollatzResearch.WordTrace]
  refine ⟨61737877440640842160253957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41158584960427228106835971 61737877440640842160253957)
  ·
    refine ⟨11575852020120157905047617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61737877440640842160253957 11575852020120157905047617)
    ·
      refine ⟨8681889015090118428785713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11575852020120157905047617 8681889015090118428785713)
      ·
        refine ⟨6511416761317588821589285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8681889015090118428785713 6511416761317588821589285)
        ·
          refine ⟨1220890642747047904047991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6511416761317588821589285 1220890642747047904047991)
          ·
            refine ⟨1831335964120571856071987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220890642747047904047991 1831335964120571856071987)
            ·
              refine ⟨2747003946180857784107981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831335964120571856071987 2747003946180857784107981)
              ·
                refine ⟨1030126479817821669040493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2747003946180857784107981 1030126479817821669040493)
                ·
                  refine ⟨386297429931683125890185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030126479817821669040493 386297429931683125890185)
                  ·
                    rfl

theorem cell21_1692701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_1692701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692701 prefixEnd_1692701 := by exact prefixLift 1692701
  have htrace : WordTrace (prefixWord ++ tailWord_1692701) baseStart_1692701 baseEnd_1692701 := by
    simpa [prefixWord, tailWord_1692701, baseEnd_1692701] using wordTrace_append hprefix tailTrace_1692701
  have hstable : (prefixWord ++ tailWord_1692701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692701).length < 2 ^ (prefixWord ++ tailWord_1692701).sum := by decide
  have hdescent : baseEnd_1692701 < baseStart_1692701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692861 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 5]
def baseStart_1692861 : Nat := 118140960795 + 1692861 * 2 ^ 59
def prefixEnd_1692861 : Nat := 4983230072969 + 3 ^ 40 * 1692861 * 2
def baseEnd_1692861 : Nat := 386333944111558403223191

theorem tailTrace_1692861 : CollatzResearch.WordTrace tailWord_1692861 prefixEnd_1692861 386333944111558403223191 := by
  unfold tailWord_1692861
  simp only [CollatzResearch.WordTrace]
  refine ⟨61743713120061189486078437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41162475413374126324052291 61743713120061189486078437)
  ·
    refine ⟨11576946210011473028639707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61743713120061189486078437 11576946210011473028639707)
    ·
      refine ⟨17365419315017209542959561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11576946210011473028639707 17365419315017209542959561)
      ·
        refine ⟨13024064486262907157219671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17365419315017209542959561 13024064486262907157219671)
        ·
          refine ⟨19536096729394360735829507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13024064486262907157219671 19536096729394360735829507)
          ·
            refine ⟨29304145094091541103744261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19536096729394360735829507 29304145094091541103744261)
            ·
              refine ⟨5494527205142163956952049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29304145094091541103744261 5494527205142163956952049)
              ·
                refine ⟨4120895403856622967714037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5494527205142163956952049 4120895403856622967714037)
                ·
                  refine ⟨386333944111558403223191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4120895403856622967714037 386333944111558403223191)
                  ·
                    rfl

theorem cell21_1692861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_1692861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692861 prefixEnd_1692861 := by exact prefixLift 1692861
  have htrace : WordTrace (prefixWord ++ tailWord_1692861) baseStart_1692861 baseEnd_1692861 := by
    simpa [prefixWord, tailWord_1692861, baseEnd_1692861] using wordTrace_append hprefix tailTrace_1692861
  have hstable : (prefixWord ++ tailWord_1692861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692861).length < 2 ^ (prefixWord ++ tailWord_1692861).sum := by decide
  have hdescent : baseEnd_1692861 < baseStart_1692861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692864 : List Nat := [2, 1, 1, 2, 6, 2, 2, 5]
def baseStart_1692864 : Nat := 118140960795 + 1692864 * 2 ^ 59
def prefixEnd_1692864 : Nat := 4983230072969 + 3 ^ 40 * 1692864 * 2
def baseEnd_1692864 : Nat := 128778209584143688224395

theorem tailTrace_1692864 : CollatzResearch.WordTrace tailWord_1692864 prefixEnd_1692864 128778209584143688224395 := by
  unfold tailWord_1692864
  simp only [CollatzResearch.WordTrace]
  refine ⟨30871911269525160499218823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41162548359366880665625097 30871911269525160499218823)
  ·
    refine ⟨46307866904287740748828235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30871911269525160499218823 46307866904287740748828235)
    ·
      refine ⟨69461800356431611123242353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46307866904287740748828235 69461800356431611123242353)
      ·
        refine ⟨52096350267323708342431765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69461800356431611123242353 52096350267323708342431765)
        ·
          refine ⟨2442016418780798828551489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52096350267323708342431765 2442016418780798828551489)
          ·
            refine ⟨1831512314085599121413617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2442016418780798828551489 1831512314085599121413617)
            ·
              refine ⟨1373634235564199341060213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831512314085599121413617 1373634235564199341060213)
              ·
                refine ⟨128778209584143688224395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1373634235564199341060213 128778209584143688224395)
                ·
                  rfl

theorem cell21_1692864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 5].length) (baseStart_1692864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692864 prefixEnd_1692864 := by exact prefixLift 1692864
  have htrace : WordTrace (prefixWord ++ tailWord_1692864) baseStart_1692864 baseEnd_1692864 := by
    simpa [prefixWord, tailWord_1692864, baseEnd_1692864] using wordTrace_append hprefix tailTrace_1692864
  have hstable : (prefixWord ++ tailWord_1692864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692864).length < 2 ^ (prefixWord ++ tailWord_1692864).sum := by decide
  have hdescent : baseEnd_1692864 < baseStart_1692864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692906 : List Nat := [3, 1, 3, 1, 1, 3, 1, 8]
def baseStart_1692906 : Nat := 118140960795 + 1692906 * 2 ^ 59
def prefixEnd_1692906 : Nat := 4983230072969 + 3 ^ 40 * 1692906 * 2
def baseEnd_1692906 : Nat := 128781404574882774991033

theorem tailTrace_1692906 : CollatzResearch.WordTrace tailWord_1692906 prefixEnd_1692906 128781404574882774991033 := by
  unfold tailWord_1692906
  simp only [CollatzResearch.WordTrace]
  refine ⟨15436338601224540542866643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41163569603265441447644381 15436338601224540542866643)
  ·
    refine ⟨23154507901836810814299965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15436338601224540542866643 23154507901836810814299965)
    ·
      refine ⟨8682940463188804055362487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23154507901836810814299965 8682940463188804055362487)
      ·
        refine ⟨13024410694783206083043731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8682940463188804055362487 13024410694783206083043731)
        ·
          refine ⟨19536616042174809124565597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13024410694783206083043731 19536616042174809124565597)
          ·
            refine ⟨7326231015815553421712099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19536616042174809124565597 7326231015815553421712099)
            ·
              refine ⟨10989346523723330132568149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7326231015815553421712099 10989346523723330132568149)
              ·
                refine ⟨128781404574882774991033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10989346523723330132568149 128781404574882774991033)
                ·
                  rfl

theorem cell21_1692906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_1692906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692906 prefixEnd_1692906 := by exact prefixLift 1692906
  have htrace : WordTrace (prefixWord ++ tailWord_1692906) baseStart_1692906 baseEnd_1692906 := by
    simpa [prefixWord, tailWord_1692906, baseEnd_1692906] using wordTrace_append hprefix tailTrace_1692906
  have hstable : (prefixWord ++ tailWord_1692906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692906).length < 2 ^ (prefixWord ++ tailWord_1692906).sum := by decide
  have hdescent : baseEnd_1692906 < baseStart_1692906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692909 : List Nat := [1, 5, 1, 2, 2, 2, 1, 3, 4]
def baseStart_1692909 : Nat := 118140960795 + 1692909 * 2 ^ 59
def prefixEnd_1692909 : Nat := 4983230072969 + 3 ^ 40 * 1692909 * 2
def baseEnd_1692909 : Nat := 386344898365520986423093

theorem tailTrace_1692909 : CollatzResearch.WordTrace tailWord_1692909 prefixEnd_1692909 386344898365520986423093 := by
  unfold tailWord_1692909
  simp only [CollatzResearch.WordTrace]
  refine ⟨61745463823887293683825781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41163642549258195789217187 61745463823887293683825781)
  ·
    refine ⟨5788637233489433782858667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61745463823887293683825781 5788637233489433782858667)
    ·
      refine ⟨8682955850234150674288001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5788637233489433782858667 8682955850234150674288001)
      ·
        refine ⟨6512216887675613005716001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8682955850234150674288001 6512216887675613005716001)
        ·
          refine ⟨4884162665756709754287001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6512216887675613005716001 4884162665756709754287001)
          ·
            refine ⟨3663121999317532315715251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4884162665756709754287001 3663121999317532315715251)
            ·
              refine ⟨5494682998976298473572877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663121999317532315715251 5494682998976298473572877)
              ·
                refine ⟨2060506124616111927589829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5494682998976298473572877 2060506124616111927589829)
                ·
                  refine ⟨386344898365520986423093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2060506124616111927589829 386344898365520986423093)
                  ·
                    rfl

theorem cell21_1692909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_1692909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692909 prefixEnd_1692909 := by exact prefixLift 1692909
  have htrace : WordTrace (prefixWord ++ tailWord_1692909) baseStart_1692909 baseEnd_1692909 := by
    simpa [prefixWord, tailWord_1692909, baseEnd_1692909] using wordTrace_append hprefix tailTrace_1692909
  have hstable : (prefixWord ++ tailWord_1692909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692909).length < 2 ^ (prefixWord ++ tailWord_1692909).sum := by decide
  have hdescent : baseEnd_1692909 < baseStart_1692909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692946 : List Nat := [3, 2, 4, 2, 1, 2, 2, 2, 3]
def baseStart_1692946 : Nat := 118140960795 + 1692946 * 2 ^ 59
def prefixEnd_1692946 : Nat := 4983230072969 + 3 ^ 40 * 1692946 * 2
def baseEnd_1692946 : Nat := 386353342269617144306351

theorem tailTrace_1692946 : CollatzResearch.WordTrace tailWord_1692946 prefixEnd_1692946 386353342269617144306351 := by
  unfold tailWord_1692946
  simp only [CollatzResearch.WordTrace]
  refine ⟨15436703331188312250730673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41164542216502166001948461 15436703331188312250730673)
  ·
    refine ⟨11577527498391234188048005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15436703331188312250730673 11577527498391234188048005)
    ·
      refine ⟨2170786405948356410259001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11577527498391234188048005 2170786405948356410259001)
      ·
        refine ⟨1628089804461267307694251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2170786405948356410259001 1628089804461267307694251)
        ·
          refine ⟨2442134706691900961541377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628089804461267307694251 2442134706691900961541377)
          ·
            refine ⟨1831601030018925721156033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2442134706691900961541377 1831601030018925721156033)
            ·
              refine ⟨1373700772514194290867025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831601030018925721156033 1373700772514194290867025)
              ·
                refine ⟨1030275579385645718150269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373700772514194290867025 1030275579385645718150269)
                ·
                  refine ⟨386353342269617144306351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030275579385645718150269 386353342269617144306351)
                  ·
                    rfl

theorem cell21_1692946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_1692946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1692946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1692946 prefixEnd_1692946 := by exact prefixLift 1692946
  have htrace : WordTrace (prefixWord ++ tailWord_1692946) baseStart_1692946 baseEnd_1692946 := by
    simpa [prefixWord, tailWord_1692946, baseEnd_1692946] using wordTrace_append hprefix tailTrace_1692946
  have hstable : (prefixWord ++ tailWord_1692946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692946).length < 2 ^ (prefixWord ++ tailWord_1692946).sum := by decide
  have hdescent : baseEnd_1692946 < baseStart_1692946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693013 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 5]
def baseStart_1693013 : Nat := 118140960795 + 1693013 * 2 ^ 59
def prefixEnd_1693013 : Nat := 4983230072969 + 3 ^ 40 * 1693013 * 2
def baseEnd_1693013 : Nat := 386368632582439916689547

theorem tailTrace_1693013 : CollatzResearch.WordTrace tailWord_1693013 prefixEnd_1693013 386368632582439916689547 := by
  unfold tailWord_1693013
  simp only [CollatzResearch.WordTrace]
  refine ⟨61749257015510519445611693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41166171343673679630407795 61749257015510519445611693)
  ·
    refine ⟨23155971380816444792104385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61749257015510519445611693 23155971380816444792104385)
    ·
      refine ⟨17366978535612333594078289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23155971380816444792104385 17366978535612333594078289)
      ·
        refine ⟨13025233901709250195558717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17366978535612333594078289 13025233901709250195558717)
        ·
          refine ⟨4884462713140968823334519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13025233901709250195558717 4884462713140968823334519)
          ·
            refine ⟨7326694069711453235001779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4884462713140968823334519 7326694069711453235001779)
            ·
              refine ⟨10990041104567179852502669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7326694069711453235001779 10990041104567179852502669)
              ·
                refine ⟨4121265414212692444688501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10990041104567179852502669 4121265414212692444688501)
                ·
                  refine ⟨386368632582439916689547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4121265414212692444688501 386368632582439916689547)
                  ·
                    rfl

theorem cell21_1693013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_1693013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693013 prefixEnd_1693013 := by exact prefixLift 1693013
  have htrace : WordTrace (prefixWord ++ tailWord_1693013) baseStart_1693013 baseEnd_1693013 := by
    simpa [prefixWord, tailWord_1693013, baseEnd_1693013] using wordTrace_append hprefix tailTrace_1693013
  have hstable : (prefixWord ++ tailWord_1693013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693013).length < 2 ^ (prefixWord ++ tailWord_1693013).sum := by decide
  have hdescent : baseEnd_1693013 < baseStart_1693013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693134 : List Nat := [4, 1, 1, 1, 2, 1, 5, 6]
def baseStart_1693134 : Nat := 118140960795 + 1693134 * 2 ^ 59
def prefixEnd_1693134 : Nat := 4983230072969 + 3 ^ 40 * 1693134 * 2
def baseEnd_1693134 : Nat := 128798748810323531724211

theorem tailTrace_1693134 : CollatzResearch.WordTrace tailWord_1693134 prefixEnd_1693134 128798748810323531724211 := by
  unfold tailWord_1693134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7719208781009019638845807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41169113498714771407177637 7719208781009019638845807)
  ·
    refine ⟨11578813171513529458268711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7719208781009019638845807 11578813171513529458268711)
    ·
      refine ⟨17368219757270294187403067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11578813171513529458268711 17368219757270294187403067)
      ·
        refine ⟨26052329635905441281104601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17368219757270294187403067 26052329635905441281104601)
        ·
          refine ⟨19539247226929080960828451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26052329635905441281104601 19539247226929080960828451)
          ·
            refine ⟨29308870840393621441242677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19539247226929080960828451 29308870840393621441242677)
            ·
              refine ⟨2747706641286902010116501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29308870840393621441242677 2747706641286902010116501)
              ·
                refine ⟨128798748810323531724211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2747706641286902010116501 128798748810323531724211)
                ·
                  rfl

theorem cell21_1693134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_1693134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693134 prefixEnd_1693134 := by exact prefixLift 1693134
  have htrace : WordTrace (prefixWord ++ tailWord_1693134) baseStart_1693134 baseEnd_1693134 := by
    simpa [prefixWord, tailWord_1693134, baseEnd_1693134] using wordTrace_append hprefix tailTrace_1693134
  have hstable : (prefixWord ++ tailWord_1693134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693134).length < 2 ^ (prefixWord ++ tailWord_1693134).sum := by decide
  have hdescent : baseEnd_1693134 < baseStart_1693134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693193 : List Nat := [1, 2, 1, 1, 3, 1, 4, 8]
def baseStart_1693193 : Nat := 118140960795 + 1693193 * 2 ^ 59
def prefixEnd_1693193 : Nat := 4983230072969 + 3 ^ 40 * 1693193 * 2
def baseEnd_1693193 : Nat := 128803237011599867896393

theorem tailTrace_1693193 : CollatzResearch.WordTrace tailWord_1693193 prefixEnd_1693193 128803237011599867896393 := by
  unfold tailWord_1693193
  simp only [CollatzResearch.WordTrace]
  refine ⟨61755822154858410187164233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41170548103238940124776155 61755822154858410187164233)
  ·
    refine ⟨46316866616143807640373175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61755822154858410187164233 46316866616143807640373175)
    ·
      refine ⟨69475299924215711460559763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46316866616143807640373175 69475299924215711460559763)
      ·
        refine ⟨104212949886323567190839645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69475299924215711460559763 104212949886323567190839645)
        ·
          refine ⟨39079856207371337696564867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104212949886323567190839645 39079856207371337696564867)
          ·
            refine ⟨58619784311057006544847301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39079856207371337696564867 58619784311057006544847301)
            ·
              refine ⟨10991209558323188727158869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58619784311057006544847301 10991209558323188727158869)
              ·
                refine ⟨128803237011599867896393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10991209558323188727158869 128803237011599867896393)
                ·
                  rfl

theorem cell21_1693193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 8].length) (baseStart_1693193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693193 prefixEnd_1693193 := by exact prefixLift 1693193
  have htrace : WordTrace (prefixWord ++ tailWord_1693193) baseStart_1693193 baseEnd_1693193 := by
    simpa [prefixWord, tailWord_1693193, baseEnd_1693193] using wordTrace_append hprefix tailTrace_1693193
  have hstable : (prefixWord ++ tailWord_1693193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693193).length < 2 ^ (prefixWord ++ tailWord_1693193).sum := by decide
  have hdescent : baseEnd_1693193 < baseStart_1693193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693241 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 5]
def baseStart_1693241 : Nat := 118140960795 + 1693241 * 2 ^ 59
def prefixEnd_1693241 : Nat := 4983230072969 + 3 ^ 40 * 1693241 * 2
def baseEnd_1693241 : Nat := 386420665288762186889081

theorem tailTrace_1693241 : CollatzResearch.WordTrace tailWord_1693241 prefixEnd_1693241 386420665288762186889081 := by
  unfold tailWord_1693241
  simp only [CollatzResearch.WordTrace]
  refine ⟨61757572858684514384911577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41171715239123009589941051 61757572858684514384911577)
  ·
    refine ⟨46318179644013385788683683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61757572858684514384911577 46318179644013385788683683)
    ·
      refine ⟨69477269466020078683025525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46318179644013385788683683 69477269466020078683025525)
      ·
        refine ⟨6513494012439382376533643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69477269466020078683025525 6513494012439382376533643)
        ·
          refine ⟨9770241018659073564800465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6513494012439382376533643 9770241018659073564800465)
          ·
            refine ⟨7327680763994305173600349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9770241018659073564800465 7327680763994305173600349)
            ·
              refine ⟨2747880286497864440100131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7327680763994305173600349 2747880286497864440100131)
              ·
                refine ⟨4121820429746796660150197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2747880286497864440100131 4121820429746796660150197)
                ·
                  refine ⟨386420665288762186889081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4121820429746796660150197 386420665288762186889081)
                  ·
                    rfl

theorem cell21_1693241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_1693241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693241 prefixEnd_1693241 := by exact prefixLift 1693241
  have htrace : WordTrace (prefixWord ++ tailWord_1693241) baseStart_1693241 baseEnd_1693241 := by
    simpa [prefixWord, tailWord_1693241, baseEnd_1693241] using wordTrace_append hprefix tailTrace_1693241
  have hstable : (prefixWord ++ tailWord_1693241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693241).length < 2 ^ (prefixWord ++ tailWord_1693241).sum := by decide
  have hdescent : baseEnd_1693241 < baseStart_1693241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693320 : List Nat := [2, 1, 3, 5, 1, 1, 3, 5]
def baseStart_1693320 : Nat := 118140960795 + 1693320 * 2 ^ 59
def prefixEnd_1693320 : Nat := 4983230072969 + 3 ^ 40 * 1693320 * 2
def baseEnd_1693320 : Nat := 128812898055025201690751

theorem tailTrace_1693320 : CollatzResearch.WordTrace tailWord_1693320 prefixEnd_1693320 128812898055025201690751 := by
  unfold tailWord_1693320
  simp only [CollatzResearch.WordTrace]
  refine ⟨30880227112699155438518707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41173636150265540584691609 30880227112699155438518707)
  ·
    refine ⟨46320340669048733157778061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30880227112699155438518707 46320340669048733157778061)
    ·
      refine ⟨17370127750893274934166773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46320340669048733157778061 17370127750893274934166773)
      ·
        refine ⟨1628449476646244525078135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17370127750893274934166773 1628449476646244525078135)
        ·
          refine ⟨2442674214969366787617203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628449476646244525078135 2442674214969366787617203)
          ·
            refine ⟨3664011322454050181425805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442674214969366787617203 3664011322454050181425805)
            ·
              refine ⟨1374004245920268818034677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3664011322454050181425805 1374004245920268818034677)
              ·
                refine ⟨128812898055025201690751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1374004245920268818034677 128812898055025201690751)
                ·
                  rfl

theorem cell21_1693320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 5].length) (baseStart_1693320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693320 prefixEnd_1693320 := by exact prefixLift 1693320
  have htrace : WordTrace (prefixWord ++ tailWord_1693320) baseStart_1693320 baseEnd_1693320 := by
    simpa [prefixWord, tailWord_1693320, baseEnd_1693320] using wordTrace_append hprefix tailTrace_1693320
  have hstable : (prefixWord ++ tailWord_1693320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693320).length < 2 ^ (prefixWord ++ tailWord_1693320).sum := by decide
  have hdescent : baseEnd_1693320 < baseStart_1693320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693348 : List Nat := [2, 3, 1, 2, 2, 2, 3, 2, 4]
def baseStart_1693348 : Nat := 118140960795 + 1693348 * 2 ^ 59
def prefixEnd_1693348 : Nat := 4983230072969 + 3 ^ 40 * 1693348 * 2
def baseEnd_1693348 : Nat := 386445084146553778605529

theorem tailTrace_1693348 : CollatzResearch.WordTrace tailWord_1693348 prefixEnd_1693348 386445084146553778605529 := by
  unfold tailWord_1693348
  simp only [CollatzResearch.WordTrace]
  refine ⟨30880737734648435829528349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41174316979531247772704465 30880737734648435829528349)
  ·
    refine ⟨11580276650493163436073131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30880737734648435829528349 11580276650493163436073131)
    ·
      refine ⟨17370414975739745154109697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11580276650493163436073131 17370414975739745154109697)
      ·
        refine ⟨13027811231804808865582273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17370414975739745154109697 13027811231804808865582273)
        ·
          refine ⟨9770858423853606649186705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13027811231804808865582273 9770858423853606649186705)
          ·
            refine ⟨7328143817890204986890029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9770858423853606649186705 7328143817890204986890029)
            ·
              refine ⟨2748053931708826870083761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7328143817890204986890029 2748053931708826870083761)
              ·
                refine ⟨2061040448781620152562821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2748053931708826870083761 2061040448781620152562821)
                ·
                  refine ⟨386445084146553778605529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2061040448781620152562821 386445084146553778605529)
                  ·
                    rfl

theorem cell21_1693348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_1693348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693348 prefixEnd_1693348 := by exact prefixLift 1693348
  have htrace : WordTrace (prefixWord ++ tailWord_1693348) baseStart_1693348 baseEnd_1693348 := by
    simpa [prefixWord, tailWord_1693348, baseEnd_1693348] using wordTrace_append hprefix tailTrace_1693348
  have hstable : (prefixWord ++ tailWord_1693348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693348).length < 2 ^ (prefixWord ++ tailWord_1693348).sum := by decide
  have hdescent : baseEnd_1693348 < baseStart_1693348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693376 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 5]
def baseStart_1693376 : Nat := 118140960795 + 1693376 * 2 ^ 59
def prefixEnd_1693376 : Nat := 4983230072969 + 3 ^ 40 * 1693376 * 2
def baseEnd_1693376 : Nat := 386451474128031952138805

theorem tailTrace_1693376 : CollatzResearch.WordTrace tailWord_1693376 prefixEnd_1693376 386451474128031952138805 := by
  unfold tailWord_1693376
  simp only [CollatzResearch.WordTrace]
  refine ⟨30881248356597716220537991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41174997808796954960717321 30881248356597716220537991)
  ·
    refine ⟨46321872534896574330806987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30881248356597716220537991 46321872534896574330806987)
    ·
      refine ⟨69482808802344861496210481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46321872534896574330806987 69482808802344861496210481)
      ·
        refine ⟨52112106601758646122157861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69482808802344861496210481 52112106601758646122157861)
        ·
          refine ⟨9771019987829746147904599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52112106601758646122157861 9771019987829746147904599)
          ·
            refine ⟨14656529981744619221856899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9771019987829746147904599 14656529981744619221856899)
            ·
              refine ⟨21984794972616928832785349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14656529981744619221856899 21984794972616928832785349)
              ·
                refine ⟨4122149057365674156147253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21984794972616928832785349 4122149057365674156147253)
                ·
                  refine ⟨386451474128031952138805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4122149057365674156147253 386451474128031952138805)
                  ·
                    rfl

theorem cell21_1693376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_1693376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693376 prefixEnd_1693376 := by exact prefixLift 1693376
  have htrace : WordTrace (prefixWord ++ tailWord_1693376) baseStart_1693376 baseEnd_1693376 := by
    simpa [prefixWord, tailWord_1693376, baseEnd_1693376] using wordTrace_append hprefix tailTrace_1693376
  have hstable : (prefixWord ++ tailWord_1693376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693376).length < 2 ^ (prefixWord ++ tailWord_1693376).sum := by decide
  have hdescent : baseEnd_1693376 < baseStart_1693376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693407 : List Nat := [1, 1, 2, 3, 2, 2, 2, 4, 4]
def baseStart_1693407 : Nat := 118140960795 + 1693407 * 2 ^ 59
def prefixEnd_1693407 : Nat := 4983230072969 + 3 ^ 40 * 1693407 * 2
def baseEnd_1693407 : Nat := 386458548750382787122075

theorem tailTrace_1693407 : CollatzResearch.WordTrace tailWord_1693407 prefixEnd_1693407 386458548750382787122075 := by
  unfold tailWord_1693407
  simp only [CollatzResearch.WordTrace]
  refine ⟨61763627376083124735454475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41175751584055416490302983 61763627376083124735454475)
  ·
    refine ⟨92645441064124687103181713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61763627376083124735454475 92645441064124687103181713)
    ·
      refine ⟨69484080798093515327386285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92645441064124687103181713 69484080798093515327386285)
      ·
        refine ⟨26056530299285068247769857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69484080798093515327386285 26056530299285068247769857)
        ·
          refine ⟨19542397724463801185827393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26056530299285068247769857 19542397724463801185827393)
          ·
            refine ⟨14656798293347850889370545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19542397724463801185827393 14656798293347850889370545)
            ·
              refine ⟨10992598720010888167027909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14656798293347850889370545 10992598720010888167027909)
              ·
                refine ⟨2061112260002041531317733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10992598720010888167027909 2061112260002041531317733)
                ·
                  refine ⟨386458548750382787122075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2061112260002041531317733 386458548750382787122075)
                  ·
                    rfl

theorem cell21_1693407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 4].length) (baseStart_1693407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693407 prefixEnd_1693407 := by exact prefixLift 1693407
  have htrace : WordTrace (prefixWord ++ tailWord_1693407) baseStart_1693407 baseEnd_1693407 := by
    simpa [prefixWord, tailWord_1693407, baseEnd_1693407] using wordTrace_append hprefix tailTrace_1693407
  have hstable : (prefixWord ++ tailWord_1693407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693407).length < 2 ^ (prefixWord ++ tailWord_1693407).sum := by decide
  have hdescent : baseEnd_1693407 < baseStart_1693407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693486 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_1693486 : Nat := 118140960795 + 1693486 * 2 ^ 59
def prefixEnd_1693486 : Nat := 4983230072969 + 3 ^ 40 * 1693486 * 2
def baseEnd_1693486 : Nat := 386476577626696205305247

theorem tailTrace_1693486 : CollatzResearch.WordTrace tailWord_1693486 prefixEnd_1693486 386476577626696205305247 := by
  unfold tailWord_1693486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7720813592849615153447539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41177672495197947485053541 7720813592849615153447539)
  ·
    refine ⟨11581220389274422730171309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7720813592849615153447539 11581220389274422730171309)
    ·
      refine ⟨4342957645977908523814241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11581220389274422730171309 4342957645977908523814241)
      ·
        refine ⟨3257218234483431392860681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4342957645977908523814241 3257218234483431392860681)
        ·
          refine ⟨2442913675862573544645511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3257218234483431392860681 2442913675862573544645511)
          ·
            refine ⟨3664370513793860316968267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442913675862573544645511 3664370513793860316968267)
            ·
              refine ⟨5496555770690790475452401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3664370513793860316968267 5496555770690790475452401)
              ·
                refine ⟨4122416828018092856589301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5496555770690790475452401 4122416828018092856589301)
                ·
                  refine ⟨386476577626696205305247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4122416828018092856589301 386476577626696205305247)
                  ·
                    rfl

theorem cell21_1693486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_1693486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693486 prefixEnd_1693486 := by exact prefixLift 1693486
  have htrace : WordTrace (prefixWord ++ tailWord_1693486) baseStart_1693486 baseEnd_1693486 := by
    simpa [prefixWord, tailWord_1693486, baseEnd_1693486] using wordTrace_append hprefix tailTrace_1693486
  have hstable : (prefixWord ++ tailWord_1693486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693486).length < 2 ^ (prefixWord ++ tailWord_1693486).sum := by decide
  have hdescent : baseEnd_1693486 < baseStart_1693486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693517 : List Nat := [1, 6, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1693517 : Nat := 118140960795 + 1693517 * 2 ^ 59
def prefixEnd_1693517 : Nat := 4983230072969 + 3 ^ 40 * 1693517 * 2
def baseEnd_1693517 : Nat := 386483652249047040288517

theorem tailTrace_1693517 : CollatzResearch.WordTrace tailWord_1693517 prefixEnd_1693517 386483652249047040288517 := by
  unfold tailWord_1693517
  simp only [CollatzResearch.WordTrace]
  refine ⟨61767639405684613521958805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41178426270456409014639203 61767639405684613521958805)
  ·
    refine ⟨2895358097141466258841819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61767639405684613521958805 2895358097141466258841819)
    ·
      refine ⟨4343037145712199388262729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2895358097141466258841819 4343037145712199388262729)
      ·
        refine ⟨3257277859284149541197047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4343037145712199388262729 3257277859284149541197047)
        ·
          refine ⟨4885916788926224311795571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3257277859284149541197047 4885916788926224311795571)
          ·
            refine ⟨7328875183389336467693357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4885916788926224311795571 7328875183389336467693357)
            ·
              refine ⟨2748328193771001175385009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7328875183389336467693357 2748328193771001175385009)
              ·
                refine ⟨2061246145328250881538757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2748328193771001175385009 2061246145328250881538757)
                ·
                  refine ⟨386483652249047040288517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2061246145328250881538757 386483652249047040288517)
                  ·
                    rfl

theorem cell21_1693517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1693517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693517 prefixEnd_1693517 := by exact prefixLift 1693517
  have htrace : WordTrace (prefixWord ++ tailWord_1693517) baseStart_1693517 baseEnd_1693517 := by
    simpa [prefixWord, tailWord_1693517, baseEnd_1693517] using wordTrace_append hprefix tailTrace_1693517
  have hstable : (prefixWord ++ tailWord_1693517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693517).length < 2 ^ (prefixWord ++ tailWord_1693517).sum := by decide
  have hdescent : baseEnd_1693517 < baseStart_1693517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693618 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_1693618 : Nat := 118140960795 + 1693618 * 2 ^ 59
def prefixEnd_1693618 : Nat := 4983230072969 + 3 ^ 40 * 1693618 * 2
def baseEnd_1693618 : Nat := 386506701825093309104977

theorem tailTrace_1693618 : CollatzResearch.WordTrace tailWord_1693618 prefixEnd_1693618 386506701825093309104977 := by
  unfold tailWord_1693618
  simp only [CollatzResearch.WordTrace]
  refine ⟨15442830794579676942846377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41180882118879138514257005 15442830794579676942846377)
  ·
    refine ⟨11582123095934757707134783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15442830794579676942846377 11582123095934757707134783)
    ·
      refine ⟨17373184643902136560702175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11582123095934757707134783 17373184643902136560702175)
      ·
        refine ⟨26059776965853204841053263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17373184643902136560702175 26059776965853204841053263)
        ·
          refine ⟨39089665448779807261579895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26059776965853204841053263 39089665448779807261579895)
          ·
            refine ⟨58634498173169710892369843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39089665448779807261579895 58634498173169710892369843)
            ·
              refine ⟨87951747259754566338554765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58634498173169710892369843 87951747259754566338554765)
              ·
                refine ⟨32981905222407962376958037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87951747259754566338554765 32981905222407962376958037)
                ·
                  refine ⟨386506701825093309104977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32981905222407962376958037 386506701825093309104977)
                  ·
                    rfl

theorem cell21_1693618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_1693618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693618 prefixEnd_1693618 := by exact prefixLift 1693618
  have htrace : WordTrace (prefixWord ++ tailWord_1693618) baseStart_1693618 baseEnd_1693618 := by
    simpa [prefixWord, tailWord_1693618, baseEnd_1693618] using wordTrace_append hprefix tailTrace_1693618
  have hstable : (prefixWord ++ tailWord_1693618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693618).length < 2 ^ (prefixWord ++ tailWord_1693618).sum := by decide
  have hdescent : baseEnd_1693618 < baseStart_1693618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693686 : List Nat := [5, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_1693686 : Nat := 118140960795 + 1693686 * 2 ^ 59
def prefixEnd_1693686 : Nat := 4983230072969 + 3 ^ 40 * 1693686 * 2
def baseEnd_1693686 : Nat := 386522220351540301971505

theorem tailTrace_1693686 : CollatzResearch.WordTrace tailWord_1693686 prefixEnd_1693686 386522220351540301971505 := by
  unfold tailWord_1693686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3860862708879522211553807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41182535561381570256573941 3860862708879522211553807)
  ·
    refine ⟨5791294063319283317330711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3860862708879522211553807 5791294063319283317330711)
    ·
      refine ⟨8686941094978924975996067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5791294063319283317330711 8686941094978924975996067)
      ·
        refine ⟨13030411642468387463994101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8686941094978924975996067 13030411642468387463994101)
        ·
          refine ⟨1221601091481411324749447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13030411642468387463994101 1221601091481411324749447)
          ·
            refine ⟨1832401637222116987124171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221601091481411324749447 1832401637222116987124171)
            ·
              refine ⟨2748602455833175480686257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832401637222116987124171 2748602455833175480686257)
              ·
                refine ⟨2061451841874881610514693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2748602455833175480686257 2061451841874881610514693)
                ·
                  refine ⟨386522220351540301971505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2061451841874881610514693 386522220351540301971505)
                  ·
                    rfl

theorem cell21_1693686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_1693686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693686 prefixEnd_1693686 := by exact prefixLift 1693686
  have htrace : WordTrace (prefixWord ++ tailWord_1693686) baseStart_1693686 baseEnd_1693686 := by
    simpa [prefixWord, tailWord_1693686, baseEnd_1693686] using wordTrace_append hprefix tailTrace_1693686
  have hstable : (prefixWord ++ tailWord_1693686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693686).length < 2 ^ (prefixWord ++ tailWord_1693686).sum := by decide
  have hdescent : baseEnd_1693686 < baseStart_1693686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693697 : List Nat := [1, 2, 4, 1, 2, 1, 1, 6, 3]
def baseStart_1693697 : Nat := 118140960795 + 1693697 * 2 ^ 59
def prefixEnd_1693697 : Nat := 4983230072969 + 3 ^ 40 * 1693697 * 2
def baseEnd_1693697 : Nat := 386524730701406727288149

theorem tailTrace_1693697 : CollatzResearch.WordTrace tailWord_1693697 prefixEnd_1693697 386524730701406727288149 := by
  unfold tailWord_1693697
  simp only [CollatzResearch.WordTrace]
  refine ⟨61774204545032504263511345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41182803030021669509007563 61774204545032504263511345)
  ·
    refine ⟨46330653408774378197633509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61774204545032504263511345 46330653408774378197633509)
    ·
      refine ⟨8686997514145195912056283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46330653408774378197633509 8686997514145195912056283)
      ·
        refine ⟨13030496271217793868084425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8686997514145195912056283 13030496271217793868084425)
        ·
          refine ⟨9772872203413345401063319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13030496271217793868084425 9772872203413345401063319)
          ·
            refine ⟨14659308305120018101594979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9772872203413345401063319 14659308305120018101594979)
            ·
              refine ⟨21988962457680027152392469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14659308305120018101594979 21988962457680027152392469)
              ·
                refine ⟨1030732615203751272768397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21988962457680027152392469 1030732615203751272768397)
                ·
                  refine ⟨386524730701406727288149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030732615203751272768397 386524730701406727288149)
                  ·
                    rfl

theorem cell21_1693697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 3].length) (baseStart_1693697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693697 prefixEnd_1693697 := by exact prefixLift 1693697
  have htrace : WordTrace (prefixWord ++ tailWord_1693697) baseStart_1693697 baseEnd_1693697 := by
    simpa [prefixWord, tailWord_1693697, baseEnd_1693697] using wordTrace_append hprefix tailTrace_1693697
  have hstable : (prefixWord ++ tailWord_1693697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693697).length < 2 ^ (prefixWord ++ tailWord_1693697).sum := by decide
  have hdescent : baseEnd_1693697 < baseStart_1693697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693742 : List Nat := [4, 1, 3, 1, 1, 4, 7]
def baseStart_1693742 : Nat := 118140960795 + 1693742 * 2 ^ 59
def prefixEnd_1693742 : Nat := 4983230072969 + 3 ^ 40 * 1693742 * 2
def baseEnd_1693742 : Nat := 42948333368277405448673

theorem tailTrace_1693742 : CollatzResearch.WordTrace tailWord_1693742 prefixEnd_1693742 42948333368277405448673 := by
  unfold tailWord_1693742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7721980728733684618612435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41183897219912984632599653 7721980728733684618612435)
  ·
    refine ⟨11582971093100526927918653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7721980728733684618612435 11582971093100526927918653)
    ·
      refine ⟨4343614159912697597969495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11582971093100526927918653 4343614159912697597969495)
      ·
        refine ⟨6515421239869046396954243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4343614159912697597969495 6515421239869046396954243)
        ·
          refine ⟨9773131859803569595431365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6515421239869046396954243 9773131859803569595431365)
          ·
            refine ⟨1832462223713169299143381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9773131859803569595431365 1832462223713169299143381)
            ·
              refine ⟨42948333368277405448673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1832462223713169299143381 42948333368277405448673)
              ·
                rfl

theorem cell21_1693742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 7].length) (baseStart_1693742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693742 prefixEnd_1693742 := by exact prefixLift 1693742
  have htrace : WordTrace (prefixWord ++ tailWord_1693742) baseStart_1693742 baseEnd_1693742 := by
    simpa [prefixWord, tailWord_1693742, baseEnd_1693742] using wordTrace_append hprefix tailTrace_1693742
  have hstable : (prefixWord ++ tailWord_1693742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693742).length < 2 ^ (prefixWord ++ tailWord_1693742).sum := by decide
  have hdescent : baseEnd_1693742 < baseStart_1693742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693748 : List Nat := [2, 5, 1, 2, 2, 1, 3, 2, 3]
def baseStart_1693748 : Nat := 118140960795 + 1693748 * 2 ^ 59
def prefixEnd_1693748 : Nat := 4983230072969 + 3 ^ 40 * 1693748 * 2
def baseEnd_1693748 : Nat := 386536369596241971938045

theorem tailTrace_1693748 : CollatzResearch.WordTrace tailWord_1693748 prefixEnd_1693748 386536369596241971938045 := by
  unfold tailWord_1693748
  simp only [CollatzResearch.WordTrace]
  refine ⟨30888032333923869986808949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41184043111898493315745265 30888032333923869986808949)
  ·
    refine ⟨2895753031305362811263339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30888032333923869986808949 2895753031305362811263339)
    ·
      refine ⟨4343629546958044216895009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2895753031305362811263339 4343629546958044216895009)
      ·
        refine ⟨3257722160218533162671257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4343629546958044216895009 3257722160218533162671257)
        ·
          refine ⟨2443291620163899872003443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3257722160218533162671257 2443291620163899872003443)
          ·
            refine ⟨3664937430245849808005165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443291620163899872003443 3664937430245849808005165)
            ·
              refine ⟨1374351536342193678001937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3664937430245849808005165 1374351536342193678001937)
              ·
                refine ⟨1030763652256645258501453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1374351536342193678001937 1030763652256645258501453)
                ·
                  refine ⟨386536369596241971938045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030763652256645258501453 386536369596241971938045)
                  ·
                    rfl

theorem cell21_1693748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_1693748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693748 prefixEnd_1693748 := by exact prefixLift 1693748
  have htrace : WordTrace (prefixWord ++ tailWord_1693748) baseStart_1693748 baseEnd_1693748 := by
    simpa [prefixWord, tailWord_1693748, baseEnd_1693748] using wordTrace_append hprefix tailTrace_1693748
  have hstable : (prefixWord ++ tailWord_1693748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693748).length < 2 ^ (prefixWord ++ tailWord_1693748).sum := by decide
  have hdescent : baseEnd_1693748 < baseStart_1693748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693832 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 7]
def baseStart_1693832 : Nat := 118140960795 + 1693832 * 2 ^ 59
def prefixEnd_1693832 : Nat := 4983230072969 + 3 ^ 40 * 1693832 * 2
def baseEnd_1693832 : Nat := 386555539540676492537873

theorem tailTrace_1693832 : CollatzResearch.WordTrace tailWord_1693832 prefixEnd_1693832 386555539540676492537873 := by
  unfold tailWord_1693832
  simp only [CollatzResearch.WordTrace]
  refine ⟨30889564199771711159837875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41186085599695614879783833 30889564199771711159837875)
  ·
    refine ⟨46334346299657566739756813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30889564199771711159837875 46334346299657566739756813)
    ·
      refine ⟨17375379862371587527408805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46334346299657566739756813 17375379862371587527408805)
      ·
        refine ⟨3257883724194672661389151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17375379862371587527408805 3257883724194672661389151)
        ·
          refine ⟨4886825586292008992083727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3257883724194672661389151 4886825586292008992083727)
          ·
            refine ⟨7330238379438013488125591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4886825586292008992083727 7330238379438013488125591)
            ·
              refine ⟨10995357569157020232188387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7330238379438013488125591 10995357569157020232188387)
              ·
                refine ⟨16493036353735530348282581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10995357569157020232188387 16493036353735530348282581)
                ·
                  refine ⟨386555539540676492537873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16493036353735530348282581 386555539540676492537873)
                  ·
                    rfl

theorem cell21_1693832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_1693832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693832 prefixEnd_1693832 := by exact prefixLift 1693832
  have htrace : WordTrace (prefixWord ++ tailWord_1693832) baseStart_1693832 baseEnd_1693832 := by
    simpa [prefixWord, tailWord_1693832, baseEnd_1693832] using wordTrace_append hprefix tailTrace_1693832
  have hstable : (prefixWord ++ tailWord_1693832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693832).length < 2 ^ (prefixWord ++ tailWord_1693832).sum := by decide
  have hdescent : baseEnd_1693832 < baseStart_1693832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693866 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_1693866 : Nat := 118140960795 + 1693866 * 2 ^ 59
def prefixEnd_1693866 : Nat := 4983230072969 + 3 ^ 40 * 1693866 * 2
def baseEnd_1693866 : Nat := 386563298803899988971137

theorem tailTrace_1693866 : CollatzResearch.WordTrace tailWord_1693866 prefixEnd_1693866 386563298803899988971137 := by
  unfold tailWord_1693866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15445092120355061531603363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41186912320946830750942301 15445092120355061531603363)
  ·
    refine ⟨23167638180532592297405045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15445092120355061531603363 23167638180532592297405045)
    ·
      refine ⟨2171966079424930527881723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23167638180532592297405045 2171966079424930527881723)
      ·
        refine ⟨3257949119137395791822585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2171966079424930527881723 3257949119137395791822585)
        ·
          refine ⟨2443461839353046843866939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3257949119137395791822585 2443461839353046843866939)
          ·
            refine ⟨3665192759029570265800409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443461839353046843866939 3665192759029570265800409)
            ·
              refine ⟨2748894569272177699350307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3665192759029570265800409 2748894569272177699350307)
              ·
                refine ⟨4123341853908266549025461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748894569272177699350307 4123341853908266549025461)
                ·
                  refine ⟨386563298803899988971137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4123341853908266549025461 386563298803899988971137)
                  ·
                    rfl

theorem cell21_1693866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_1693866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693866 prefixEnd_1693866 := by exact prefixLift 1693866
  have htrace : WordTrace (prefixWord ++ tailWord_1693866) baseStart_1693866 baseEnd_1693866 := by
    simpa [prefixWord, tailWord_1693866, baseEnd_1693866] using wordTrace_append hprefix tailTrace_1693866
  have hstable : (prefixWord ++ tailWord_1693866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693866).length < 2 ^ (prefixWord ++ tailWord_1693866).sum := by decide
  have hdescent : baseEnd_1693866 < baseStart_1693866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693900 : List Nat := [2, 2, 1, 6, 2, 1, 1, 3, 3]
def baseStart_1693900 : Nat := 118140960795 + 1693900 * 2 ^ 59
def prefixEnd_1693900 : Nat := 4983230072969 + 3 ^ 40 * 1693900 * 2
def baseEnd_1693900 : Nat := 386571058067123485404401

theorem tailTrace_1693900 : CollatzResearch.WordTrace tailWord_1693900 prefixEnd_1693900 386571058067123485404401 := by
  unfold tailWord_1693900
  simp only [CollatzResearch.WordTrace]
  refine ⟨30890804281648534966575577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41187739042198046622100769 30890804281648534966575577)
  ·
    refine ⟨23168103211236401224931683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30890804281648534966575577 23168103211236401224931683)
    ·
      refine ⟨34752154816854601837397525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23168103211236401224931683 34752154816854601837397525)
      ·
        refine ⟨1629007257040059461128009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34752154816854601837397525 1629007257040059461128009)
        ·
          refine ⟨1221755442780044595846007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1629007257040059461128009 1221755442780044595846007)
          ·
            refine ⟨1832633164170066893769011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221755442780044595846007 1832633164170066893769011)
            ·
              refine ⟨2748949746255100340653517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832633164170066893769011 2748949746255100340653517)
              ·
                refine ⟨1030856154845662627745069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2748949746255100340653517 1030856154845662627745069)
                ·
                  refine ⟨386571058067123485404401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030856154845662627745069 386571058067123485404401)
                  ·
                    rfl

theorem cell21_1693900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_1693900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693900 prefixEnd_1693900 := by exact prefixLift 1693900
  have htrace : WordTrace (prefixWord ++ tailWord_1693900) baseStart_1693900 baseEnd_1693900 := by
    simpa [prefixWord, tailWord_1693900, baseEnd_1693900] using wordTrace_append hprefix tailTrace_1693900
  have hstable : (prefixWord ++ tailWord_1693900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693900).length < 2 ^ (prefixWord ++ tailWord_1693900).sum := by decide
  have hdescent : baseEnd_1693900 < baseStart_1693900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693925 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 5]
def baseStart_1693925 : Nat := 118140960795 + 1693925 * 2 ^ 59
def prefixEnd_1693925 : Nat := 4983230072969 + 3 ^ 40 * 1693925 * 2
def baseEnd_1693925 : Nat := 386576763407728997487683

theorem tailTrace_1693925 : CollatzResearch.WordTrace tailWord_1693925 prefixEnd_1693925 386576763407728997487683 := by
  unfold tailWord_1693925
  simp only [CollatzResearch.WordTrace]
  refine ⟨61782520388206499202811229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41188346925470999468540819 61782520388206499202811229)
  ·
    refine ⟨23168445145577437201054211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61782520388206499202811229 23168445145577437201054211)
    ·
      refine ⟨34752667718366155801581317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23168445145577437201054211 34752667718366155801581317)
      ·
        refine ⟨6516125197193654212796497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34752667718366155801581317 6516125197193654212796497)
        ·
          refine ⟨4887093897895240659597373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6516125197193654212796497 4887093897895240659597373)
          ·
            refine ⟨1832660211710715247349015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4887093897895240659597373 1832660211710715247349015)
            ·
              refine ⟨2748990317566072871023523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832660211710715247349015 2748990317566072871023523)
              ·
                refine ⟨4123485476349109306535285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748990317566072871023523 4123485476349109306535285)
                ·
                  refine ⟨386576763407728997487683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4123485476349109306535285 386576763407728997487683)
                  ·
                    rfl

theorem cell21_1693925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_1693925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1693925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1693925 prefixEnd_1693925 := by exact prefixLift 1693925
  have htrace : WordTrace (prefixWord ++ tailWord_1693925) baseStart_1693925 baseEnd_1693925 := by
    simpa [prefixWord, tailWord_1693925, baseEnd_1693925] using wordTrace_append hprefix tailTrace_1693925
  have hstable : (prefixWord ++ tailWord_1693925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693925).length < 2 ^ (prefixWord ++ tailWord_1693925).sum := by decide
  have hdescent : baseEnd_1693925 < baseStart_1693925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694077 : List Nat := [1, 4, 1, 1, 2, 3, 3, 3, 3]
def baseStart_1694077 : Nat := 118140960795 + 1694077 * 2 ^ 59
def prefixEnd_1694077 : Nat := 4983230072969 + 3 ^ 40 * 1694077 * 2
def baseEnd_1694077 : Nat := 386611451878610510954039

theorem tailTrace_1694077 : CollatzResearch.WordTrace tailWord_1694077 prefixEnd_1694077 386611451878610510954039 := by
  unfold tailWord_1694077
  simp only [CollatzResearch.WordTrace]
  refine ⟨61788064283655829162344485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41192042855770552774896323 61788064283655829162344485)
  ·
    refine ⟨11585262053185467967939591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61788064283655829162344485 11585262053185467967939591)
    ·
      refine ⟨17377893079778201951909387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11585262053185467967939591 17377893079778201951909387)
      ·
        refine ⟨26066839619667302927864081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17377893079778201951909387 26066839619667302927864081)
        ·
          refine ⟨19550129714750477195898061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26066839619667302927864081 19550129714750477195898061)
          ·
            refine ⟨7331298643031428948461773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19550129714750477195898061 7331298643031428948461773)
            ·
              refine ⟨2749236991136785855673165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7331298643031428948461773 2749236991136785855673165)
              ·
                refine ⟨1030963871676294695877437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2749236991136785855673165 1030963871676294695877437)
                ·
                  refine ⟨386611451878610510954039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030963871676294695877437 386611451878610510954039)
                  ·
                    rfl

theorem cell21_1694077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_1694077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694077 prefixEnd_1694077 := by exact prefixLift 1694077
  have htrace : WordTrace (prefixWord ++ tailWord_1694077) baseStart_1694077 baseEnd_1694077 := by
    simpa [prefixWord, tailWord_1694077, baseEnd_1694077] using wordTrace_append hprefix tailTrace_1694077
  have hstable : (prefixWord ++ tailWord_1694077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694077).length < 2 ^ (prefixWord ++ tailWord_1694077).sum := by decide
  have hdescent : baseEnd_1694077 < baseStart_1694077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694136 : List Nat := [2, 1, 2, 1, 2, 2, 1, 7, 3]
def baseStart_1694136 : Nat := 118140960795 + 1694136 * 2 ^ 59
def prefixEnd_1694136 : Nat := 4983230072969 + 3 ^ 40 * 1694136 * 2
def baseEnd_1694136 : Nat := 386624916482439519470585

theorem tailTrace_1694136 : CollatzResearch.WordTrace tailWord_1694136 prefixEnd_1694136 386624916482439519470585 := by
  unfold tailWord_1694136
  simp only [CollatzResearch.WordTrace]
  refine ⟨30895108095221041119371131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41193477460294721492494841 30895108095221041119371131)
  ·
    refine ⟨46342662142831561679056697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30895108095221041119371131 46342662142831561679056697)
    ·
      refine ⟨34756996607123671259292523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46342662142831561679056697 34756996607123671259292523)
      ·
        refine ⟨52135494910685506888938785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34756996607123671259292523 52135494910685506888938785)
        ·
          refine ⟨39101621183014130166704089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52135494910685506888938785 39101621183014130166704089)
          ·
            refine ⟨29326215887260597625028067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39101621183014130166704089 29326215887260597625028067)
            ·
              refine ⟨43989323830890896437542101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29326215887260597625028067 43989323830890896437542101)
              ·
                refine ⟨1030999777286505385254893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43989323830890896437542101 1030999777286505385254893)
                ·
                  refine ⟨386624916482439519470585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030999777286505385254893 386624916482439519470585)
                  ·
                    rfl

theorem cell21_1694136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 3].length) (baseStart_1694136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694136 prefixEnd_1694136 := by exact prefixLift 1694136
  have htrace : WordTrace (prefixWord ++ tailWord_1694136) baseStart_1694136 baseEnd_1694136 := by
    simpa [prefixWord, tailWord_1694136, baseEnd_1694136] using wordTrace_append hprefix tailTrace_1694136
  have hstable : (prefixWord ++ tailWord_1694136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694136).length < 2 ^ (prefixWord ++ tailWord_1694136).sum := by decide
  have hdescent : baseEnd_1694136 < baseStart_1694136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694145 : List Nat := [1, 2, 7, 1, 1, 2, 2, 2, 3]
def baseStart_1694145 : Nat := 118140960795 + 1694145 * 2 ^ 59
def prefixEnd_1694145 : Nat := 4983230072969 + 3 ^ 40 * 1694145 * 2
def baseEnd_1694145 : Nat := 386626970405057503820567

theorem tailTrace_1694145 : CollatzResearch.WordTrace tailWord_1694145 prefixEnd_1694145 386626970405057503820567 := by
  unfold tailWord_1694145
  simp only [CollatzResearch.WordTrace]
  refine ⟨61790544447409476775819889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41193696298272984517213259 61790544447409476775819889)
  ·
    refine ⟨46342908335557107581864917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61790544447409476775819889 46342908335557107581864917)
    ·
      refine ⟨1086161914114619708949959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 46342908335557107581864917 1086161914114619708949959)
      ·
        refine ⟨1629242871171929563424939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086161914114619708949959 1629242871171929563424939)
        ·
          refine ⟨2443864306757894345137409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629242871171929563424939 2443864306757894345137409)
          ·
            refine ⟨1832898230068420758853057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2443864306757894345137409 1832898230068420758853057)
            ·
              refine ⟨1374673672551315569139793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832898230068420758853057 1374673672551315569139793)
              ·
                refine ⟨1031005254413486676854845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1374673672551315569139793 1031005254413486676854845)
                ·
                  refine ⟨386626970405057503820567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031005254413486676854845 386626970405057503820567)
                  ·
                    rfl

theorem cell21_1694145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 3].length) (baseStart_1694145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694145 prefixEnd_1694145 := by exact prefixLift 1694145
  have htrace : WordTrace (prefixWord ++ tailWord_1694145) baseStart_1694145 baseEnd_1694145 := by
    simpa [prefixWord, tailWord_1694145, baseEnd_1694145] using wordTrace_append hprefix tailTrace_1694145
  have hstable : (prefixWord ++ tailWord_1694145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694145).length < 2 ^ (prefixWord ++ tailWord_1694145).sum := by decide
  have hdescent : baseEnd_1694145 < baseStart_1694145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694153 : List Nat := [1, 2, 1, 1, 2, 1, 8, 2, 3]
def baseStart_1694153 : Nat := 118140960795 + 1694153 * 2 ^ 59
def prefixEnd_1694153 : Nat := 4983230072969 + 3 ^ 40 * 1694153 * 2
def baseEnd_1694153 : Nat := 386628796114051267687217

theorem tailTrace_1694153 : CollatzResearch.WordTrace tailWord_1694153 prefixEnd_1694153 386628796114051267687217 := by
  unfold tailWord_1694153
  simp only [CollatzResearch.WordTrace]
  refine ⟨61790836231380494142111113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41193890820920329428074075 61790836231380494142111113)
  ·
    refine ⟨46343127173535370606583335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61790836231380494142111113 46343127173535370606583335)
    ·
      refine ⟨69514690760303055909875003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46343127173535370606583335 69514690760303055909875003)
      ·
        refine ⟨104272036140454583864812505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69514690760303055909875003 104272036140454583864812505)
        ·
          refine ⟨78204027105340937898609379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104272036140454583864812505 78204027105340937898609379)
          ·
            refine ⟨117306040658011406847914069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78204027105340937898609379 117306040658011406847914069)
            ·
              refine ⟨1374680163961071173998993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 117306040658011406847914069 1374680163961071173998993)
              ·
                refine ⟨1031010122970803380499245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1374680163961071173998993 1031010122970803380499245)
                ·
                  refine ⟨386628796114051267687217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031010122970803380499245 386628796114051267687217)
                  ·
                    rfl

theorem cell21_1694153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 3].length) (baseStart_1694153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694153 prefixEnd_1694153 := by exact prefixLift 1694153
  have htrace : WordTrace (prefixWord ++ tailWord_1694153) baseStart_1694153 baseEnd_1694153 := by
    simpa [prefixWord, tailWord_1694153, baseEnd_1694153] using wordTrace_append hprefix tailTrace_1694153
  have hstable : (prefixWord ++ tailWord_1694153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694153).length < 2 ^ (prefixWord ++ tailWord_1694153).sum := by decide
  have hdescent : baseEnd_1694153 < baseStart_1694153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694212 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 5]
def baseStart_1694212 : Nat := 118140960795 + 1694212 * 2 ^ 59
def prefixEnd_1694212 : Nat := 4983230072969 + 3 ^ 40 * 1694212 * 2
def baseEnd_1694212 : Nat := 386642260717880276203763

theorem tailTrace_1694212 : CollatzResearch.WordTrace tailWord_1694212 prefixEnd_1694212 386642260717880276203763 := by
  unfold tailWord_1694212
  simp only [CollatzResearch.WordTrace]
  refine ⟨30896494069083373609254445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41195325425444498145672593 30896494069083373609254445)
  ·
    refine ⟨11586185275906265103470417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30896494069083373609254445 11586185275906265103470417)
    ·
      refine ⟨8689638956929698827602813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11586185275906265103470417 8689638956929698827602813)
      ·
        refine ⟨3258614608848637060351055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8689638956929698827602813 3258614608848637060351055)
        ·
          refine ⟨4887921913272955590526583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3258614608848637060351055 4887921913272955590526583)
          ·
            refine ⟨7331882869909433385789875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887921913272955590526583 7331882869909433385789875)
            ·
              refine ⟨10997824304864150078684813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7331882869909433385789875 10997824304864150078684813)
              ·
                refine ⟨4124184114324056279506805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10997824304864150078684813 4124184114324056279506805)
                ·
                  refine ⟨386642260717880276203763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4124184114324056279506805 386642260717880276203763)
                  ·
                    rfl

theorem cell21_1694212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_1694212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694212 prefixEnd_1694212 := by exact prefixLift 1694212
  have htrace : WordTrace (prefixWord ++ tailWord_1694212) baseStart_1694212 baseEnd_1694212 := by
    simpa [prefixWord, tailWord_1694212, baseEnd_1694212] using wordTrace_append hprefix tailTrace_1694212
  have hstable : (prefixWord ++ tailWord_1694212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694212).length < 2 ^ (prefixWord ++ tailWord_1694212).sum := by decide
  have hdescent : baseEnd_1694212 < baseStart_1694212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694361 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 6]
def baseStart_1694361 : Nat := 118140960795 + 1694361 * 2 ^ 59
def prefixEnd_1694361 : Nat := 4983230072969 + 3 ^ 40 * 1694361 * 2
def baseEnd_1694361 : Nat := 386676264547889128220125

theorem tailTrace_1694361 : CollatzResearch.WordTrace tailWord_1694361 prefixEnd_1694361 386676264547889128220125 := by
  unfold tailWord_1694361
  simp only [CollatzResearch.WordTrace]
  refine ⟨61798422614626945665682937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41198948409751297110455291 61798422614626945665682937)
  ·
    refine ⟨46348816960970209249262203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61798422614626945665682937 46348816960970209249262203)
    ·
      refine ⟨69523225441455313873893305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46348816960970209249262203 69523225441455313873893305)
      ·
        refine ⟨52142419081091485405419979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69523225441455313873893305 52142419081091485405419979)
        ·
          refine ⟨78213628621637228108129969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52142419081091485405419979 78213628621637228108129969)
          ·
            refine ⟨58660221466227921081097477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78213628621637228108129969 58660221466227921081097477)
            ·
              refine ⟨10998791524917735202705777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58660221466227921081097477 10998791524917735202705777)
              ·
                refine ⟨8249093643688301402029333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10998791524917735202705777 8249093643688301402029333)
                ·
                  refine ⟨386676264547889128220125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8249093643688301402029333 386676264547889128220125)
                  ·
                    rfl

theorem cell21_1694361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_1694361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694361 prefixEnd_1694361 := by exact prefixLift 1694361
  have htrace : WordTrace (prefixWord ++ tailWord_1694361) baseStart_1694361 baseEnd_1694361 := by
    simpa [prefixWord, tailWord_1694361, baseEnd_1694361] using wordTrace_append hprefix tailTrace_1694361
  have hstable : (prefixWord ++ tailWord_1694361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694361).length < 2 ^ (prefixWord ++ tailWord_1694361).sum := by decide
  have hdescent : baseEnd_1694361 < baseStart_1694361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694381 : List Nat := [1, 5, 2, 1, 1, 2, 2, 4, 3]
def baseStart_1694381 : Nat := 118140960795 + 1694381 * 2 ^ 59
def prefixEnd_1694381 : Nat := 4983230072969 + 3 ^ 40 * 1694381 * 2
def baseEnd_1694381 : Nat := 386680828820373537886751

theorem tailTrace_1694381 : CollatzResearch.WordTrace tailWord_1694381 prefixEnd_1694381 386680828820373537886751 := by
  unfold tailWord_1694381
  simp only [CollatzResearch.WordTrace]
  refine ⟨61799152074554489081410997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41199434716369659387607331 61799152074554489081410997)
  ·
    refine ⟨5793670506989483351382281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61799152074554489081410997 5793670506989483351382281)
    ·
      refine ⟨4345252880242112513536711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5793670506989483351382281 4345252880242112513536711)
      ·
        refine ⟨6517879320363168770305067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4345252880242112513536711 6517879320363168770305067)
        ·
          refine ⟨9776818980544753155457601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6517879320363168770305067 9776818980544753155457601)
          ·
            refine ⟨7332614235408564866593201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9776818980544753155457601 7332614235408564866593201)
            ·
              refine ⟨5499460676556423649944901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7332614235408564866593201 5499460676556423649944901)
              ·
                refine ⟨1031148876854329434364669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5499460676556423649944901 1031148876854329434364669)
                ·
                  refine ⟨386680828820373537886751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031148876854329434364669 386680828820373537886751)
                  ·
                    rfl

theorem cell21_1694381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_1694381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694381 prefixEnd_1694381 := by exact prefixLift 1694381
  have htrace : WordTrace (prefixWord ++ tailWord_1694381) baseStart_1694381 baseEnd_1694381 := by
    simpa [prefixWord, tailWord_1694381, baseEnd_1694381] using wordTrace_append hprefix tailTrace_1694381
  have hstable : (prefixWord ++ tailWord_1694381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694381).length < 2 ^ (prefixWord ++ tailWord_1694381).sum := by decide
  have hdescent : baseEnd_1694381 < baseStart_1694381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694468 : List Nat := [2, 3, 2, 2, 1, 1, 1, 9]
def baseStart_1694468 : Nat := 118140960795 + 1694468 * 2 ^ 59
def prefixEnd_1694468 : Nat := 4983230072969 + 3 ^ 40 * 1694468 * 2
def baseEnd_1694468 : Nat := 128900227801893573312191

theorem tailTrace_1694468 : CollatzResearch.WordTrace tailWord_1694468 prefixEnd_1694468 128900227801893573312191 := by
  unfold tailWord_1694468
  simp only [CollatzResearch.WordTrace]
  refine ⟨30901162612619651469914029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41201550150159535293218705 30901162612619651469914029)
  ·
    refine ⟨11587935979732369301217761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30901162612619651469914029 11587935979732369301217761)
    ·
      refine ⟨8690951984799276975913321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11587935979732369301217761 8690951984799276975913321)
      ·
        refine ⟨6518213988599457731934991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8690951984799276975913321 6518213988599457731934991)
        ·
          refine ⟨9777320982899186597902487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6518213988599457731934991 9777320982899186597902487)
          ·
            refine ⟨14665981474348779896853731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9777320982899186597902487 14665981474348779896853731)
            ·
              refine ⟨21998972211523169845280597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14665981474348779896853731 21998972211523169845280597)
              ·
                refine ⟨128900227801893573312191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21998972211523169845280597 128900227801893573312191)
                ·
                  rfl

theorem cell21_1694468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_1694468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694468 prefixEnd_1694468 := by exact prefixLift 1694468
  have htrace : WordTrace (prefixWord ++ tailWord_1694468) baseStart_1694468 baseEnd_1694468 := by
    simpa [prefixWord, tailWord_1694468, baseEnd_1694468] using wordTrace_append hprefix tailTrace_1694468
  have hstable : (prefixWord ++ tailWord_1694468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694468).length < 2 ^ (prefixWord ++ tailWord_1694468).sum := by decide
  have hdescent : baseEnd_1694468 < baseStart_1694468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694589 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 6]
def baseStart_1694589 : Nat := 118140960795 + 1694589 * 2 ^ 59
def prefixEnd_1694589 : Nat := 4983230072969 + 3 ^ 40 * 1694589 * 2
def baseEnd_1694589 : Nat := 386728297254211398419659

theorem tailTrace_1694589 : CollatzResearch.WordTrace tailWord_1694589 prefixEnd_1694589 386728297254211398419659 := by
  unfold tailWord_1694589
  simp only [CollatzResearch.WordTrace]
  refine ⟨61806738457800940604982821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41204492305200627069988547 61806738457800940604982821)
  ·
    refine ⟨11588763460837676363434279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61806738457800940604982821 11588763460837676363434279)
    ·
      refine ⟨17383145191256514545151419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11588763460837676363434279 17383145191256514545151419)
      ·
        refine ⟨26074717786884771817727129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17383145191256514545151419 26074717786884771817727129)
        ·
          refine ⟨19556038340163578863295347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26074717786884771817727129 19556038340163578863295347)
          ·
            refine ⟨29334057510245368294943021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19556038340163578863295347 29334057510245368294943021)
            ·
              refine ⟨11000271566342013110603633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29334057510245368294943021 11000271566342013110603633)
              ·
                refine ⟨8250203674756509832952725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11000271566342013110603633 8250203674756509832952725)
                ·
                  refine ⟨386728297254211398419659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8250203674756509832952725 386728297254211398419659)
                  ·
                    rfl

theorem cell21_1694589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_1694589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694589 prefixEnd_1694589 := by exact prefixLift 1694589
  have htrace : WordTrace (prefixWord ++ tailWord_1694589) baseStart_1694589 baseEnd_1694589 := by
    simpa [prefixWord, tailWord_1694589, baseEnd_1694589] using wordTrace_append hprefix tailTrace_1694589
  have hstable : (prefixWord ++ tailWord_1694589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694589).length < 2 ^ (prefixWord ++ tailWord_1694589).sum := by decide
  have hdescent : baseEnd_1694589 < baseStart_1694589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694603 : List Nat := [1, 1, 1, 1, 4, 2, 11]
def baseStart_1694603 : Nat := 118140960795 + 1694603 * 2 ^ 59
def prefixEnd_1694603 : Nat := 4983230072969 + 3 ^ 40 * 1694603 * 2
def baseEnd_1694603 : Nat := 42970165804994498354033

theorem tailTrace_1694603 : CollatzResearch.WordTrace tailWord_1694603 prefixEnd_1694603 42970165804994498354033 := by
  unfold tailWord_1694603
  simp only [CollatzResearch.WordTrace]
  refine ⟨61807249079750220995992463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41204832719833480663994975 61807249079750220995992463)
  ·
    refine ⟨92710873619625331493988695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61807249079750220995992463 92710873619625331493988695)
    ·
      refine ⟨139066310429437997240983043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92710873619625331493988695 139066310429437997240983043)
      ·
        refine ⟨208599465644156995861474565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139066310429437997240983043 208599465644156995861474565)
        ·
          refine ⟨39112399808279436724026481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208599465644156995861474565 39112399808279436724026481)
          ·
            refine ⟨29334299856209577543019861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39112399808279436724026481 29334299856209577543019861)
            ·
              refine ⟨42970165804994498354033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29334299856209577543019861 42970165804994498354033)
              ·
                rfl

theorem cell21_1694603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 11].length) (baseStart_1694603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694603 prefixEnd_1694603 := by exact prefixLift 1694603
  have htrace : WordTrace (prefixWord ++ tailWord_1694603) baseStart_1694603 baseEnd_1694603 := by
    simpa [prefixWord, tailWord_1694603, baseEnd_1694603] using wordTrace_append hprefix tailTrace_1694603
  have hstable : (prefixWord ++ tailWord_1694603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694603).length < 2 ^ (prefixWord ++ tailWord_1694603).sum := by decide
  have hdescent : baseEnd_1694603 < baseStart_1694603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
