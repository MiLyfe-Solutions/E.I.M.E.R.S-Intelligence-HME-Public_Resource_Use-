import V185TrunkScan23Chunk0813

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4815493 : List Nat := [1, 3, 1, 1, 4, 3, 1, 3, 2, 1, 3]
def baseStart_4815493 : Nat := 118140960795 + 4815493 * 2 ^ 59
def prefixEnd_4815493 : Nat := 4983230072969 + 3 ^ 40 * 4815493 * 2
def baseEnd_4815493 : Nat := 2472662497361433095191457

theorem tailTrace_4815493 : CollatzResearch.WordTrace tailWord_4815493 prefixEnd_4815493 2472662497361433095191457 := by
  unfold tailWord_4815493
  simp only [CollatzResearch.WordTrace]
  refine ⟨175635458743298756573251133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117090305828865837715500755 175635458743298756573251133)
  ·
    refine ⟨65863297028737033714969175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175635458743298756573251133 65863297028737033714969175)
    ·
      refine ⟨98794945543105550572453763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65863297028737033714969175 98794945543105550572453763)
      ·
        refine ⟨148192418314658325858680645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98794945543105550572453763 148192418314658325858680645)
        ·
          refine ⟨27786078433998436098502621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148192418314658325858680645 27786078433998436098502621)
          ·
            refine ⟨10419779412749413536938483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27786078433998436098502621 10419779412749413536938483)
            ·
              refine ⟨15629669119124120305407725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10419779412749413536938483 15629669119124120305407725)
              ·
                refine ⟨5861125919671545114527897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15629669119124120305407725 5861125919671545114527897)
                ·
                  refine ⟨4395844439753658835895923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5861125919671545114527897 4395844439753658835895923)
                  ·
                    refine ⟨6593766659630488253843885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4395844439753658835895923 6593766659630488253843885)
                    ·
                      refine ⟨2472662497361433095191457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6593766659630488253843885 2472662497361433095191457)
                      ·
                        rfl

theorem cell23_4815493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_4815493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815493 prefixEnd_4815493 := by exact prefixLift 4815493
  have htrace : WordTrace (prefixWord ++ tailWord_4815493) baseStart_4815493 baseEnd_4815493 := by
    simpa [prefixWord, tailWord_4815493, baseEnd_4815493] using wordTrace_append hprefix tailTrace_4815493
  have hstable : (prefixWord ++ tailWord_4815493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815493).length < 2 ^ (prefixWord ++ tailWord_4815493).sum := by decide
  have hdescent : baseEnd_4815493 < baseStart_4815493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815527 : List Nat := [1, 1, 6, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_4815527 : Nat := 118140960795 + 4815527 * 2 ^ 59
def prefixEnd_4815527 : Nat := 4983230072969 + 3 ^ 40 * 4815527 * 2
def baseEnd_4815527 : Nat := 2472679955703685962166301

theorem tailTrace_4815527 : CollatzResearch.WordTrace tailWord_4815527 prefixEnd_4815527 2472679955703685962166301 := by
  unfold tailWord_4815527
  simp only [CollatzResearch.WordTrace]
  refine ⟨175636698825175580379988835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117091132550117053586659223 175636698825175580379988835)
  ·
    refine ⟨263455048237763370569983253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175636698825175580379988835 263455048237763370569983253)
    ·
      refine ⟨12349455386145157995467965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 263455048237763370569983253 12349455386145157995467965)
      ·
        refine ⟨4631045769804434248300487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12349455386145157995467965 4631045769804434248300487)
        ·
          refine ⟨6946568654706651372450731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4631045769804434248300487 6946568654706651372450731)
          ·
            refine ⟨10419852982059977058676097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6946568654706651372450731 10419852982059977058676097)
            ·
              refine ⟨7814889736544982794007073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10419852982059977058676097 7814889736544982794007073)
              ·
                refine ⟨5861167302408737095505305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7814889736544982794007073 5861167302408737095505305)
                ·
                  refine ⟨4395875476806552821628979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5861167302408737095505305 4395875476806552821628979)
                  ·
                    refine ⟨6593813215209829232443469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4395875476806552821628979 6593813215209829232443469)
                    ·
                      refine ⟨2472679955703685962166301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6593813215209829232443469 2472679955703685962166301)
                      ·
                        rfl

theorem cell23_4815527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_4815527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815527 prefixEnd_4815527 := by exact prefixLift 4815527
  have htrace : WordTrace (prefixWord ++ tailWord_4815527) baseStart_4815527 baseEnd_4815527 := by
    simpa [prefixWord, tailWord_4815527, baseEnd_4815527] using wordTrace_append hprefix tailTrace_4815527
  have hstable : (prefixWord ++ tailWord_4815527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815527).length < 2 ^ (prefixWord ++ tailWord_4815527).sum := by decide
  have hdescent : baseEnd_4815527 < baseStart_4815527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815550 : List Nat := [4, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_4815550 : Nat := 118140960795 + 4815550 * 2 ^ 59
def prefixEnd_4815550 : Nat := 4983230072969 + 3 ^ 40 * 4815550 * 2
def baseEnd_4815550 : Nat := 2472691765758739372178695

theorem tailTrace_4815550 : CollatzResearch.WordTrace tailWord_4815550 prefixEnd_4815550 2472691765758739372178695 := by
  unfold tailWord_4815550
  simp only [CollatzResearch.WordTrace]
  refine ⟨21954692213011531913509513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117091691802728170205384069 21954692213011531913509513)
  ·
    refine ⟨16466019159758648935132135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21954692213011531913509513 16466019159758648935132135)
    ·
      refine ⟨24699028739637973402698203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16466019159758648935132135 24699028739637973402698203)
      ·
        refine ⟨37048543109456960104047305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24699028739637973402698203 37048543109456960104047305)
        ·
          refine ⟨27786407332092720078035479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37048543109456960104047305 27786407332092720078035479)
          ·
            refine ⟨41679610998139080117053219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27786407332092720078035479 41679610998139080117053219)
            ·
              refine ⟨62519416497208620175579829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41679610998139080117053219 62519416497208620175579829)
              ·
                refine ⟨5861195296613308141460609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62519416497208620175579829 5861195296613308141460609)
                ·
                  refine ⟨4395896472459981106095457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5861195296613308141460609 4395896472459981106095457)
                  ·
                    refine ⟨3296922354344985829571593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4395896472459981106095457 3296922354344985829571593)
                    ·
                      refine ⟨2472691765758739372178695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3296922354344985829571593 2472691765758739372178695)
                      ·
                        rfl

theorem cell23_4815550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_4815550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815550 prefixEnd_4815550 := by exact prefixLift 4815550
  have htrace : WordTrace (prefixWord ++ tailWord_4815550) baseStart_4815550 baseEnd_4815550 := by
    simpa [prefixWord, tailWord_4815550, baseEnd_4815550] using wordTrace_append hprefix tailTrace_4815550
  have hstable : (prefixWord ++ tailWord_4815550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815550).length < 2 ^ (prefixWord ++ tailWord_4815550).sum := by decide
  have hdescent : baseEnd_4815550 < baseStart_4815550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815556 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 7]
def baseStart_4815556 : Nat := 118140960795 + 4815556 * 2 ^ 59
def prefixEnd_4815556 : Nat := 4983230072969 + 3 ^ 40 * 4815556 * 2
def baseEnd_4815556 : Nat := 274743871849185149855963

theorem tailTrace_4815556 : CollatzResearch.WordTrace tailWord_4815556 prefixEnd_4815556 274743871849185149855963 := by
  unfold tailWord_4815556
  simp only [CollatzResearch.WordTrace]
  refine ⟨87818878271035259166397261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117091837694713678888529681 87818878271035259166397261)
  ·
    refine ⟨32932079351638222187398973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87818878271035259166397261 32932079351638222187398973)
    ·
      refine ⟨12349529756864333320274615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32932079351638222187398973 12349529756864333320274615)
      ·
        refine ⟨18524294635296499980411923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12349529756864333320274615 18524294635296499980411923)
        ·
          refine ⟨27786441952944749970617885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18524294635296499980411923 27786441952944749970617885)
          ·
            refine ⟨10419915732354281238981707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27786441952944749970617885 10419915732354281238981707)
            ·
              refine ⟨15629873598531421858472561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10419915732354281238981707 15629873598531421858472561)
              ·
                refine ⟨11722405198898566393854421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15629873598531421858472561 11722405198898566393854421)
                ·
                  refine ⟨274743871849185149855963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11722405198898566393854421 274743871849185149855963)
                  ·
                    rfl

theorem cell23_4815556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_4815556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815556 prefixEnd_4815556 := by exact prefixLift 4815556
  have htrace : WordTrace (prefixWord ++ tailWord_4815556) baseStart_4815556 baseEnd_4815556 := by
    simpa [prefixWord, tailWord_4815556, baseEnd_4815556] using wordTrace_append hprefix tailTrace_4815556
  have hstable : (prefixWord ++ tailWord_4815556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815556).length < 2 ^ (prefixWord ++ tailWord_4815556).sum := by decide
  have hdescent : baseEnd_4815556 < baseStart_4815556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815569 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 1, 7]
def baseStart_4815569 : Nat := 118140960795 + 4815569 * 2 ^ 59
def prefixEnd_4815569 : Nat := 4983230072969 + 3 ^ 40 * 4815569 * 2
def baseEnd_4815569 : Nat := 824233840630391599280369

theorem tailTrace_4815569 : CollatzResearch.WordTrace tailWord_4815569 prefixEnd_4815569 824233840630391599280369 := by
  unfold tailWord_4815569
  simp only [CollatzResearch.WordTrace]
  refine ⟨175638230691023421553017761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117092153794015614368678507 175638230691023421553017761)
  ·
    refine ⟨131728673018267566164763321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175638230691023421553017761 131728673018267566164763321)
    ·
      refine ⟨98796504763700674623572491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131728673018267566164763321 98796504763700674623572491)
      ·
        refine ⟨148194757145551011935358737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98796504763700674623572491 148194757145551011935358737)
        ·
          refine ⟨111146067859163258951519053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148194757145551011935358737 111146067859163258951519053)
          ·
            refine ⟨41679775447186222106819645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111146067859163258951519053 41679775447186222106819645)
            ·
              refine ⟨15629915792694833290057367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41679775447186222106819645 15629915792694833290057367)
              ·
                refine ⟨23444873689042249935086051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15629915792694833290057367 23444873689042249935086051)
                ·
                  refine ⟨35167310533563374902629077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23444873689042249935086051 35167310533563374902629077)
                  ·
                    refine ⟨824233840630391599280369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35167310533563374902629077 824233840630391599280369)
                    ·
                      rfl

theorem cell23_4815569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_4815569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815569 prefixEnd_4815569 := by exact prefixLift 4815569
  have htrace : WordTrace (prefixWord ++ tailWord_4815569) baseStart_4815569 baseEnd_4815569 := by
    simpa [prefixWord, tailWord_4815569, baseEnd_4815569] using wordTrace_append hprefix tailTrace_4815569
  have hstable : (prefixWord ++ tailWord_4815569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815569).length < 2 ^ (prefixWord ++ tailWord_4815569).sum := by decide
  have hdescent : baseEnd_4815569 < baseStart_4815569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815606 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_4815606 : Nat := 118140960795 + 4815606 * 2 ^ 59
def prefixEnd_4815606 : Nat := 4983230072969 + 3 ^ 40 * 4815606 * 2
def baseEnd_4815606 : Nat := 2472720520675391153078437

theorem tailTrace_4815606 : CollatzResearch.WordTrace tailWord_4815606 prefixEnd_4815606 2472720520675391153078437 := by
  unfold tailWord_4815606
  simp only [CollatzResearch.WordTrace]
  refine ⟨10977473761993086054507167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117093053461259584581409781 10977473761993086054507167)
  ·
    refine ⟨16466210642989629081760751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10977473761993086054507167 16466210642989629081760751)
    ·
      refine ⟨24699315964484443622641127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16466210642989629081760751 24699315964484443622641127)
      ·
        refine ⟨37048973946726665433961691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24699315964484443622641127 37048973946726665433961691)
        ·
          refine ⟨55573460920089998150942537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37048973946726665433961691 55573460920089998150942537)
          ·
            refine ⟨41680095690067498613206903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55573460920089998150942537 41680095690067498613206903)
            ·
              refine ⟨62520143535101247919810355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41680095690067498613206903 62520143535101247919810355)
              ·
                refine ⟨93780215302651871879715533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62520143535101247919810355 93780215302651871879715533)
                ·
                  refine ⟨35167580738494451954893325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93780215302651871879715533 35167580738494451954893325)
                  ·
                    refine ⟨13187842776935419483084997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35167580738494451954893325 13187842776935419483084997)
                    ·
                      refine ⟨2472720520675391153078437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13187842776935419483084997 2472720520675391153078437)
                      ·
                        rfl

theorem cell23_4815606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_4815606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815606 prefixEnd_4815606 := by exact prefixLift 4815606
  have htrace : WordTrace (prefixWord ++ tailWord_4815606) baseStart_4815606 baseEnd_4815606 := by
    simpa [prefixWord, tailWord_4815606, baseEnd_4815606] using wordTrace_append hprefix tailTrace_4815606
  have hstable : (prefixWord ++ tailWord_4815606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815606).length < 2 ^ (prefixWord ++ tailWord_4815606).sum := by decide
  have hdescent : baseEnd_4815606 < baseStart_4815606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815619 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 4]
def baseStart_4815619 : Nat := 118140960795 + 4815619 * 2 ^ 59
def prefixEnd_4815619 : Nat := 4983230072969 + 3 ^ 40 * 4815619 * 2
def baseEnd_4815619 : Nat := 2472727195923899602215877

theorem tailTrace_4815619 : CollatzResearch.WordTrace tailWord_4815619 prefixEnd_4815619 2472727195923899602215877 := by
  unfold tailWord_4815619
  simp only [CollatzResearch.WordTrace]
  refine ⟨175640054340842280092337911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117093369560561520061558607 175640054340842280092337911)
  ·
    refine ⟨263460081511263420138506867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175640054340842280092337911 263460081511263420138506867)
    ·
      refine ⟨395190122266895130207760301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263460081511263420138506867 395190122266895130207760301)
      ·
        refine ⟨148196295850085673827910113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 395190122266895130207760301 148196295850085673827910113)
        ·
          refine ⟨111147221887564255370932585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148196295850085673827910113 111147221887564255370932585)
          ·
            refine ⟨83360416415673191528199439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111147221887564255370932585 83360416415673191528199439)
            ·
              refine ⟨125040624623509787292299159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83360416415673191528199439 125040624623509787292299159)
              ·
                refine ⟨187560936935264680938448739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125040624623509787292299159 187560936935264680938448739)
                ·
                  refine ⟨281341405402897021407673109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187560936935264680938448739 281341405402897021407673109)
                  ·
                    refine ⟨13187878378260797878484677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 281341405402897021407673109 13187878378260797878484677)
                    ·
                      refine ⟨2472727195923899602215877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13187878378260797878484677 2472727195923899602215877)
                      ·
                        rfl

theorem cell23_4815619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_4815619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815619 prefixEnd_4815619 := by exact prefixLift 4815619
  have htrace : WordTrace (prefixWord ++ tailWord_4815619) baseStart_4815619 baseEnd_4815619 := by
    simpa [prefixWord, tailWord_4815619, baseEnd_4815619] using wordTrace_append hprefix tailTrace_4815619
  have hstable : (prefixWord ++ tailWord_4815619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815619).length < 2 ^ (prefixWord ++ tailWord_4815619).sum := by decide
  have hdescent : baseEnd_4815619 < baseStart_4815619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815626 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_4815626 : Nat := 118140960795 + 4815626 * 2 ^ 59
def prefixEnd_4815626 : Nat := 4983230072969 + 3 ^ 40 * 4815626 * 2
def baseEnd_4815626 : Nat := 2472730790288481074828345

theorem tailTrace_4815626 : CollatzResearch.WordTrace tailWord_4815626 prefixEnd_4815626 2472730790288481074828345 := by
  unfold tailWord_4815626
  simp only [CollatzResearch.WordTrace]
  refine ⟨43910077412954230071960683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117093539767877946858561821 43910077412954230071960683)
  ·
    refine ⟨65865116119431345107941025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43910077412954230071960683 65865116119431345107941025)
    ·
      refine ⟨49398837089573508830955769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65865116119431345107941025 49398837089573508830955769)
      ·
        refine ⟨37049127817180131623216827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49398837089573508830955769 37049127817180131623216827)
        ·
          refine ⟨55573691725770197434825241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37049127817180131623216827 55573691725770197434825241)
          ·
            refine ⟨41680268794327648076118931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55573691725770197434825241 41680268794327648076118931)
            ·
              refine ⟨62520403191491472114178397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41680268794327648076118931 62520403191491472114178397)
              ·
                refine ⟨23445151196809302042816899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62520403191491472114178397 23445151196809302042816899)
                ·
                  refine ⟨35167726795213953064225349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23445151196809302042816899 35167726795213953064225349)
                  ·
                    refine ⟨6593948774102616199542253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35167726795213953064225349 6593948774102616199542253)
                    ·
                      refine ⟨2472730790288481074828345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6593948774102616199542253 2472730790288481074828345)
                      ·
                        rfl

theorem cell23_4815626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_4815626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815626 prefixEnd_4815626 := by exact prefixLift 4815626
  have htrace : WordTrace (prefixWord ++ tailWord_4815626) baseStart_4815626 baseEnd_4815626 := by
    simpa [prefixWord, tailWord_4815626, baseEnd_4815626] using wordTrace_append hprefix tailTrace_4815626
  have hstable : (prefixWord ++ tailWord_4815626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815626).length < 2 ^ (prefixWord ++ tailWord_4815626).sum := by decide
  have hdescent : baseEnd_4815626 < baseStart_4815626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815650 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_4815650 : Nat := 118140960795 + 4815650 * 2 ^ 59
def prefixEnd_4815650 : Nat := 4983230072969 + 3 ^ 40 * 4815650 * 2
def baseEnd_4815650 : Nat := 824247704608062993642745

theorem tailTrace_4815650 : CollatzResearch.WordTrace tailWord_4815650 prefixEnd_4815650 824247704608062993642745 := by
  unfold tailWord_4815650
  simp only [CollatzResearch.WordTrace]
  refine ⟨43910296250932493096679101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117094123335819981591144269 43910296250932493096679101)
  ·
    refine ⟨16466361094099684911254663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43910296250932493096679101 16466361094099684911254663)
    ·
      refine ⟨24699541641149527366881995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16466361094099684911254663 24699541641149527366881995)
      ·
        refine ⟨37049312461724291050322993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24699541641149527366881995 37049312461724291050322993)
        ·
          refine ⟨27786984346293218287742245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37049312461724291050322993 27786984346293218287742245)
          ·
            refine ⟨5210059564929978428951671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27786984346293218287742245 5210059564929978428951671)
            ·
              refine ⟨7815089347394967643427507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5210059564929978428951671 7815089347394967643427507)
              ·
                refine ⟨11722634021092451465141261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7815089347394967643427507 11722634021092451465141261)
                ·
                  refine ⟨4395987757909669299427973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11722634021092451465141261 4395987757909669299427973)
                  ·
                    refine ⟨824247704608062993642745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4395987757909669299427973 824247704608062993642745)
                    ·
                      rfl

theorem cell23_4815650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_4815650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815650 prefixEnd_4815650 := by exact prefixLift 4815650
  have htrace : WordTrace (prefixWord ++ tailWord_4815650) baseStart_4815650 baseEnd_4815650 := by
    simpa [prefixWord, tailWord_4815650, baseEnd_4815650] using wordTrace_append hprefix tailTrace_4815650
  have hstable : (prefixWord ++ tailWord_4815650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815650).length < 2 ^ (prefixWord ++ tailWord_4815650).sum := by decide
  have hdescent : baseEnd_4815650 < baseStart_4815650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815723 : List Nat := [1, 1, 1, 1, 2, 2, 6, 3, 2, 4]
def baseStart_4815723 : Nat := 118140960795 + 4815723 * 2 ^ 59
def prefixEnd_4815723 : Nat := 4983230072969 + 3 ^ 40 * 4815723 * 2
def baseEnd_4815723 : Nat := 824260199303989065105133

theorem tailTrace_4815723 : CollatzResearch.WordTrace tailWord_4815723 prefixEnd_4815723 824260199303989065105133 := by
  unfold tailWord_4815723
  simp only [CollatzResearch.WordTrace]
  refine ⟨175643847532465505854123823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117095898354977003902749215 175643847532465505854123823)
  ·
    refine ⟨263465771298698258781185735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175643847532465505854123823 263465771298698258781185735)
    ·
      refine ⟨395198656948047388171778603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263465771298698258781185735 395198656948047388171778603)
      ·
        refine ⟨592797985422071082257667905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395198656948047388171778603 592797985422071082257667905)
        ·
          refine ⟨444598489066553311693250929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 592797985422071082257667905 444598489066553311693250929)
          ·
            refine ⟨333448866799914983769938197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444598489066553311693250929 333448866799914983769938197)
            ·
              refine ⟨15630415631246014864215853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 333448866799914983769938197 15630415631246014864215853)
              ·
                refine ⟨5861405861717255574080945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15630415631246014864215853 5861405861717255574080945)
                ·
                  refine ⟨4396054396287941680560709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5861405861717255574080945 4396054396287941680560709)
                  ·
                    refine ⟨824260199303989065105133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4396054396287941680560709 824260199303989065105133)
                    ·
                      rfl

theorem cell23_4815723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 4].length) (baseStart_4815723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815723 prefixEnd_4815723 := by exact prefixLift 4815723
  have htrace : WordTrace (prefixWord ++ tailWord_4815723) baseStart_4815723 baseEnd_4815723 := by
    simpa [prefixWord, tailWord_4815723, baseEnd_4815723] using wordTrace_append hprefix tailTrace_4815723
  have hstable : (prefixWord ++ tailWord_4815723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815723).length < 2 ^ (prefixWord ++ tailWord_4815723).sum := by decide
  have hdescent : baseEnd_4815723 < baseStart_4815723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815730 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 5, 2, 2]
def baseStart_4815730 : Nat := 118140960795 + 4815730 * 2 ^ 59
def prefixEnd_4815730 : Nat := 4983230072969 + 3 ^ 40 * 4815730 * 2
def baseEnd_4815730 : Nat := 2472784192276548667927867

theorem tailTrace_4815730 : CollatzResearch.WordTrace tailWord_4815730 prefixEnd_4815730 2472784192276548667927867 := by
  unfold tailWord_4815730
  simp only [CollatzResearch.WordTrace]
  refine ⟨43911025710860036512407161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117096068562293430699752429 43911025710860036512407161)
  ·
    refine ⟨32933269283145027384305371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43911025710860036512407161 32933269283145027384305371)
    ·
      refine ⟨49399903924717541076458057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32933269283145027384305371 49399903924717541076458057)
      ·
        refine ⟨37049927943538155807343543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49399903924717541076458057 37049927943538155807343543)
        ·
          refine ⟨55574891915307233711015315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37049927943538155807343543 55574891915307233711015315)
          ·
            refine ⟨83362337872960850566522973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55574891915307233711015315 83362337872960850566522973)
            ·
              refine ⟨31260876702360318962446115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83362337872960850566522973 31260876702360318962446115)
              ·
                refine ⟨46891315053540478443669173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31260876702360318962446115 46891315053540478443669173)
                ·
                  refine ⟨4396060786269419854093985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46891315053540478443669173 4396060786269419854093985)
                  ·
                    refine ⟨3297045589702064890570489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4396060786269419854093985 3297045589702064890570489)
                    ·
                      refine ⟨2472784192276548667927867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3297045589702064890570489 2472784192276548667927867)
                      ·
                        rfl

theorem cell23_4815730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_4815730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815730 prefixEnd_4815730 := by exact prefixLift 4815730
  have htrace : WordTrace (prefixWord ++ tailWord_4815730) baseStart_4815730 baseEnd_4815730 := by
    simpa [prefixWord, tailWord_4815730, baseEnd_4815730] using wordTrace_append hprefix tailTrace_4815730
  have hstable : (prefixWord ++ tailWord_4815730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815730).length < 2 ^ (prefixWord ++ tailWord_4815730).sum := by decide
  have hdescent : baseEnd_4815730 < baseStart_4815730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815734 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_4815734 : Nat := 118140960795 + 4815734 * 2 ^ 59
def prefixEnd_4815734 : Nat := 4983230072969 + 3 ^ 40 * 4815734 * 2
def baseEnd_4815734 : Nat := 2472786246199166652277849

theorem tailTrace_4815734 : CollatzResearch.WordTrace tailWord_4815734 prefixEnd_4815734 2472786246199166652277849 := by
  unfold tailWord_4815734
  simp only [CollatzResearch.WordTrace]
  refine ⟨10977765545964103420798391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117096165823617103155182837 10977765545964103420798391)
  ·
    refine ⟨16466648318946155131197587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10977765545964103420798391 16466648318946155131197587)
    ·
      refine ⟨24699972478419232696796381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16466648318946155131197587 24699972478419232696796381)
      ·
        refine ⟨9262489679407212261298643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24699972478419232696796381 9262489679407212261298643)
        ·
          refine ⟨13893734519110818391947965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9262489679407212261298643 13893734519110818391947965)
          ·
            refine ⟨5210150444666556896980487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13893734519110818391947965 5210150444666556896980487)
            ·
              refine ⟨7815225666999835345470731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5210150444666556896980487 7815225666999835345470731)
              ·
                refine ⟨11722838500499753018206097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7815225666999835345470731 11722838500499753018206097)
                ·
                  refine ⟨8792128875374814763654573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11722838500499753018206097 8792128875374814763654573)
                  ·
                    refine ⟨3297048328265555536370465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8792128875374814763654573 3297048328265555536370465)
                    ·
                      refine ⟨2472786246199166652277849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3297048328265555536370465 2472786246199166652277849)
                      ·
                        rfl

theorem cell23_4815734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_4815734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815734 prefixEnd_4815734 := by exact prefixLift 4815734
  have htrace : WordTrace (prefixWord ++ tailWord_4815734) baseStart_4815734 baseEnd_4815734 := by
    simpa [prefixWord, tailWord_4815734, baseEnd_4815734] using wordTrace_append hprefix tailTrace_4815734
  have hstable : (prefixWord ++ tailWord_4815734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815734).length < 2 ^ (prefixWord ++ tailWord_4815734).sum := by decide
  have hdescent : baseEnd_4815734 < baseStart_4815734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815764 : List Nat := [2, 4, 2, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_4815764 : Nat := 118140960795 + 4815764 * 2 ^ 59
def prefixEnd_4815764 : Nat := 4983230072969 + 3 ^ 40 * 4815764 * 2
def baseEnd_4815764 : Nat := 2472801650618801534902711

theorem tailTrace_4815764 : CollatzResearch.WordTrace tailWord_4815764 prefixEnd_4815764 2472801650618801534902711 := by
  unfold tailWord_4815764
  simp only [CollatzResearch.WordTrace]
  refine ⟨87822671462658484928183173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117096895283544646570910897 87822671462658484928183173)
  ·
    refine ⟨16466750899248465924034345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87822671462658484928183173 16466750899248465924034345)
    ·
      refine ⟨12350063174436349443025759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16466750899248465924034345 12350063174436349443025759)
      ·
        refine ⟨18525094761654524164538639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12350063174436349443025759 18525094761654524164538639)
        ·
          refine ⟨27787642142481786246807959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18525094761654524164538639 27787642142481786246807959)
          ·
            refine ⟨41681463213722679370211939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27787642142481786246807959 41681463213722679370211939)
            ·
              refine ⟨62522194820584019055317909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41681463213722679370211939 62522194820584019055317909)
              ·
                refine ⟨2930727882214875893218027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62522194820584019055317909 2930727882214875893218027)
                ·
                  refine ⟨4396091823322313839827041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930727882214875893218027 4396091823322313839827041)
                  ·
                    refine ⟨3297068867491735379870281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4396091823322313839827041 3297068867491735379870281)
                    ·
                      refine ⟨2472801650618801534902711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3297068867491735379870281 2472801650618801534902711)
                      ·
                        rfl

theorem cell23_4815764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_4815764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815764 prefixEnd_4815764 := by exact prefixLift 4815764
  have htrace : WordTrace (prefixWord ++ tailWord_4815764) baseStart_4815764 baseEnd_4815764 := by
    simpa [prefixWord, tailWord_4815764, baseEnd_4815764] using wordTrace_append hprefix tailTrace_4815764
  have hstable : (prefixWord ++ tailWord_4815764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815764).length < 2 ^ (prefixWord ++ tailWord_4815764).sum := by decide
  have hdescent : baseEnd_4815764 < baseStart_4815764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815880 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 2, 5, 2]
def baseStart_4815880 : Nat := 118140960795 + 4815880 * 2 ^ 59
def prefixEnd_4815880 : Nat := 4983230072969 + 3 ^ 40 * 4815880 * 2
def baseEnd_4815880 : Nat := 2472861214374723081052177

theorem tailTrace_4815880 : CollatzResearch.WordTrace tailWord_4815880 prefixEnd_4815880 2472861214374723081052177 := by
  unfold tailWord_4815880
  simp only [CollatzResearch.WordTrace]
  refine ⟨87824786896448360833794547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117099715861931147778392729 87824786896448360833794547)
  ·
    refine ⟨131737180344672541250691821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87824786896448360833794547 131737180344672541250691821)
    ·
      refine ⟨49401442629252202969009433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131737180344672541250691821 49401442629252202969009433)
      ·
        refine ⟨37051081971939152226757075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49401442629252202969009433 37051081971939152226757075)
        ·
          refine ⟨55576622957908728340135613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37051081971939152226757075 55576622957908728340135613)
          ·
            refine ⟨20841233609215773127550855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55576622957908728340135613 20841233609215773127550855)
            ·
              refine ⟨31261850413823659691326283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20841233609215773127550855 31261850413823659691326283)
              ·
                refine ⟨46892775620735489536989425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31261850413823659691326283 46892775620735489536989425)
                ·
                  refine ⟨35169581715551617152742069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46892775620735489536989425 35169581715551617152742069)
                  ·
                    refine ⟨3297148285832964108069569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35169581715551617152742069 3297148285832964108069569)
                    ·
                      refine ⟨2472861214374723081052177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3297148285832964108069569 2472861214374723081052177)
                      ·
                        rfl

theorem cell23_4815880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_4815880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815880 prefixEnd_4815880 := by exact prefixLift 4815880
  have htrace : WordTrace (prefixWord ++ tailWord_4815880) baseStart_4815880 baseEnd_4815880 := by
    simpa [prefixWord, tailWord_4815880, baseEnd_4815880] using wordTrace_append hprefix tailTrace_4815880
  have hstable : (prefixWord ++ tailWord_4815880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815880).length < 2 ^ (prefixWord ++ tailWord_4815880).sum := by decide
  have hdescent : baseEnd_4815880 < baseStart_4815880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815883 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 5]
def baseStart_4815883 : Nat := 118140960795 + 4815883 * 2 ^ 59
def prefixEnd_4815883 : Nat := 4983230072969 + 3 ^ 40 * 4815883 * 2
def baseEnd_4815883 : Nat := 2472862754816686569314663

theorem tailTrace_4815883 : CollatzResearch.WordTrace tailWord_4815883 prefixEnd_4815883 2472862754816686569314663 := by
  unfold tailWord_4815883
  simp only [CollatzResearch.WordTrace]
  refine ⟨175649683211885853179948303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117099788807923902119965535 175649683211885853179948303)
  ·
    refine ⟨263474524817828779769922455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175649683211885853179948303 263474524817828779769922455)
    ·
      refine ⟨395211787226743169654883683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263474524817828779769922455 395211787226743169654883683)
      ·
        refine ⟨592817680840114754482325525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395211787226743169654883683 592817680840114754482325525)
        ·
          refine ⟨27788328789380379116359009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 592817680840114754482325525 27788328789380379116359009)
          ·
            refine ⟨20841246592035284337269257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27788328789380379116359009 20841246592035284337269257)
            ·
              refine ⟨15630934944026463252951943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20841246592035284337269257 15630934944026463252951943)
              ·
                refine ⟨23446402416039694879427915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15630934944026463252951943 23446402416039694879427915)
                ·
                  refine ⟨35169603624059542319141873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23446402416039694879427915 35169603624059542319141873)
                  ·
                    refine ⟨26377202718044656739356405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35169603624059542319141873 26377202718044656739356405)
                    ·
                      refine ⟨2472862754816686569314663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26377202718044656739356405 2472862754816686569314663)
                      ·
                        rfl

theorem cell23_4815883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 5].length) (baseStart_4815883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815883 prefixEnd_4815883 := by exact prefixLift 4815883
  have htrace : WordTrace (prefixWord ++ tailWord_4815883) baseStart_4815883 baseEnd_4815883 := by
    simpa [prefixWord, tailWord_4815883, baseEnd_4815883] using wordTrace_append hprefix tailTrace_4815883
  have hstable : (prefixWord ++ tailWord_4815883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815883).length < 2 ^ (prefixWord ++ tailWord_4815883).sum := by decide
  have hdescent : baseEnd_4815883 < baseStart_4815883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815930 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3]
def baseStart_4815930 : Nat := 118140960795 + 4815930 * 2 ^ 59
def prefixEnd_4815930 : Nat := 4983230072969 + 3 ^ 40 * 4815930 * 2
def baseEnd_4815930 : Nat := 2472886888407447885426947

theorem tailTrace_4815930 : CollatzResearch.WordTrace tailWord_4815930 prefixEnd_4815930 2472886888407447885426947 := by
  unfold tailWord_4815930
  simp only [CollatzResearch.WordTrace]
  refine ⟨43912849360678895051727311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117100931628477053471272829 43912849360678895051727311)
  ·
    refine ⟨65869274041018342577590967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43912849360678895051727311 65869274041018342577590967)
    ·
      refine ⟨98803911061527513866386451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65869274041018342577590967 98803911061527513866386451)
      ·
        refine ⟨148205866592291270799579677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98803911061527513866386451 148205866592291270799579677)
        ·
          refine ⟨55577199972109226549842379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148205866592291270799579677 55577199972109226549842379)
          ·
            refine ⟨83365799958163839824763569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55577199972109226549842379 83365799958163839824763569)
            ·
              refine ⟨62524349968622879868572677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83365799958163839824763569 62524349968622879868572677)
              ·
                refine ⟨11723315619116789975357377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62524349968622879868572677 11723315619116789975357377)
                ·
                  refine ⟨8792486714337592481518033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11723315619116789975357377 8792486714337592481518033)
                  ·
                    refine ⟨6594365035753194361138525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8792486714337592481518033 6594365035753194361138525)
                    ·
                      refine ⟨2472886888407447885426947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6594365035753194361138525 2472886888407447885426947)
                      ·
                        rfl

theorem cell23_4815930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_4815930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815930 prefixEnd_4815930 := by exact prefixLift 4815930
  have htrace : WordTrace (prefixWord ++ tailWord_4815930) baseStart_4815930 baseEnd_4815930 := by
    simpa [prefixWord, tailWord_4815930, baseEnd_4815930] using wordTrace_append hprefix tailTrace_4815930
  have hstable : (prefixWord ++ tailWord_4815930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815930).length < 2 ^ (prefixWord ++ tailWord_4815930).sum := by decide
  have hdescent : baseEnd_4815930 < baseStart_4815930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815980 : List Nat := [2, 2, 1, 1, 3, 2, 1, 5, 1, 5]
def baseStart_4815980 : Nat := 118140960795 + 4815980 * 2 ^ 59
def prefixEnd_4815980 : Nat := 4983230072969 + 3 ^ 40 * 4815980 * 2
def baseEnd_4815980 : Nat := 824304187480057563267239

theorem tailTrace_4815980 : CollatzResearch.WordTrace tailWord_4815980 prefixEnd_4815980 824304187480057563267239 := by
  unfold tailWord_4815980
  simp only [CollatzResearch.WordTrace]
  refine ⟨87826610546267219373114697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117102147395022959164152929 87826610546267219373114697)
  ·
    refine ⟨65869957909700414529836023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87826610546267219373114697 65869957909700414529836023)
    ·
      refine ⟨98804936864550621794754035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65869957909700414529836023 98804936864550621794754035)
      ·
        refine ⟨148207405296825932692131053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98804936864550621794754035 148207405296825932692131053)
        ·
          refine ⟨55577776986309724759549145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148207405296825932692131053 55577776986309724759549145)
          ·
            refine ⟨41683332739732293569661859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55577776986309724759549145 41683332739732293569661859)
            ·
              refine ⟨62524999109598440354492789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41683332739732293569661859 62524999109598440354492789)
              ·
                refine ⟨5861718666524853783233699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62524999109598440354492789 5861718666524853783233699)
                ·
                  refine ⟨8792577999787280674850549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5861718666524853783233699 8792577999787280674850549)
                  ·
                    refine ⟨824304187480057563267239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8792577999787280674850549 824304187480057563267239)
                    ·
                      rfl

theorem cell23_4815980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_4815980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815980 prefixEnd_4815980 := by exact prefixLift 4815980
  have htrace : WordTrace (prefixWord ++ tailWord_4815980) baseStart_4815980 baseEnd_4815980 := by
    simpa [prefixWord, tailWord_4815980, baseEnd_4815980] using wordTrace_append hprefix tailTrace_4815980
  have hstable : (prefixWord ++ tailWord_4815980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815980).length < 2 ^ (prefixWord ++ tailWord_4815980).sum := by decide
  have hdescent : baseEnd_4815980 < baseStart_4815980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816010 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 1, 6]
def baseStart_4816010 : Nat := 118140960795 + 4816010 * 2 ^ 59
def prefixEnd_4816010 : Nat := 4983230072969 + 3 ^ 40 * 4816010 * 2
def baseEnd_4816010 : Nat := 824309322286602524142193

theorem tailTrace_4816010 : CollatzResearch.WordTrace tailWord_4816010 prefixEnd_4816010 824309322286602524142193 := by
  unfold tailWord_4816010
  simp only [CollatzResearch.WordTrace]
  refine ⟨43913578820606438467455371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117102876854950502579880989 43913578820606438467455371)
  ·
    refine ⟨65870368230909657701183057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43913578820606438467455371 65870368230909657701183057)
    ·
      refine ⟨49402776173182243275887293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65870368230909657701183057 49402776173182243275887293)
      ·
        refine ⟨18526041064943341228457735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49402776173182243275887293 18526041064943341228457735)
        ·
          refine ⟨27789061597415011842686603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18526041064943341228457735 27789061597415011842686603)
          ·
            refine ⟨41683592396122517764029905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27789061597415011842686603 41683592396122517764029905)
            ·
              refine ⟨31262694297091888323022429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41683592396122517764029905 31262694297091888323022429)
              ·
                refine ⟨11723510361409458121133411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31262694297091888323022429 11723510361409458121133411)
                ·
                  refine ⟨17585265542114187181700117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11723510361409458121133411 17585265542114187181700117)
                  ·
                    refine ⟨824309322286602524142193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17585265542114187181700117 824309322286602524142193)
                    ·
                      rfl

theorem cell23_4816010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_4816010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816010 prefixEnd_4816010 := by exact prefixLift 4816010
  have htrace : WordTrace (prefixWord ++ tailWord_4816010) baseStart_4816010 baseEnd_4816010 := by
    simpa [prefixWord, tailWord_4816010, baseEnd_4816010] using wordTrace_append hprefix tailTrace_4816010
  have hstable : (prefixWord ++ tailWord_4816010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816010).length < 2 ^ (prefixWord ++ tailWord_4816010).sum := by decide
  have hdescent : baseEnd_4816010 < baseStart_4816010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816014 : List Nat := [4, 1, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_4816014 : Nat := 118140960795 + 4816014 * 2 ^ 59
def prefixEnd_4816014 : Nat := 4983230072969 + 3 ^ 40 * 4816014 * 2
def baseEnd_4816014 : Nat := 824310006927475185592187

theorem tailTrace_4816014 : CollatzResearch.WordTrace tailWord_4816014 prefixEnd_4816014 824310006927475185592187 := by
  unfold tailWord_4816014
  simp only [CollatzResearch.WordTrace]
  refine ⟨21956807646801407819120887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117102974116274175035311397 21956807646801407819120887)
  ·
    refine ⟨32935211470202111728681331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21956807646801407819120887 32935211470202111728681331)
    ·
      refine ⟨49402817205303167593021997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32935211470202111728681331 49402817205303167593021997)
      ·
        refine ⟨18526056451988687847383249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49402817205303167593021997 18526056451988687847383249)
        ·
          refine ⟨13894542338991515885537437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18526056451988687847383249 13894542338991515885537437)
          ·
            refine ⟨5210453377121818457076539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13894542338991515885537437 5210453377121818457076539)
            ·
              refine ⟨7815680065682727685614809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5210453377121818457076539 7815680065682727685614809)
              ·
                refine ⟨5861760049262045764211107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7815680065682727685614809 5861760049262045764211107)
                ·
                  refine ⟨8792640073893068646316661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5861760049262045764211107 8792640073893068646316661)
                  ·
                    refine ⟨824310006927475185592187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8792640073893068646316661 824310006927475185592187)
                    ·
                      rfl

theorem cell23_4816014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_4816014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816014 prefixEnd_4816014 := by exact prefixLift 4816014
  have htrace : WordTrace (prefixWord ++ tailWord_4816014) baseStart_4816014 baseEnd_4816014 := by
    simpa [prefixWord, tailWord_4816014, baseEnd_4816014] using wordTrace_append hprefix tailTrace_4816014
  have hstable : (prefixWord ++ tailWord_4816014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816014).length < 2 ^ (prefixWord ++ tailWord_4816014).sum := by decide
  have hdescent : baseEnd_4816014 < baseStart_4816014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816037 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 5]
def baseStart_4816037 : Nat := 118140960795 + 4816037 * 2 ^ 59
def prefixEnd_4816037 : Nat := 4983230072969 + 3 ^ 40 * 4816037 * 2
def baseEnd_4816037 : Nat := 2472941830837478966788955

theorem tailTrace_4816037 : CollatzResearch.WordTrace tailWord_4816037 prefixEnd_4816037 2472941830837478966788955 := by
  unfold tailWord_4816037
  simp only [CollatzResearch.WordTrace]
  refine ⟨175655300053327937481054365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117103533368885291654036243 175655300053327937481054365)
  ·
    refine ⟨65870737519997976555395387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175655300053327937481054365 65870737519997976555395387)
    ·
      refine ⟨98806106279996964833093081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65870737519997976555395387 98806106279996964833093081)
      ·
        refine ⟨74104579709997723624819811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98806106279996964833093081 74104579709997723624819811)
        ·
          refine ⟨111156869564996585437229717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74104579709997723624819811 111156869564996585437229717)
          ·
            refine ⟨5210478260859214942370143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111156869564996585437229717 5210478260859214942370143)
            ·
              refine ⟨7815717391288822413555215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5210478260859214942370143 7815717391288822413555215)
              ·
                refine ⟨11723576086933233620332823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7815717391288822413555215 11723576086933233620332823)
                ·
                  refine ⟨17585364130399850430499235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11723576086933233620332823 17585364130399850430499235)
                  ·
                    refine ⟨26378046195599775645748853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17585364130399850430499235 26378046195599775645748853)
                    ·
                      refine ⟨2472941830837478966788955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26378046195599775645748853 2472941830837478966788955)
                      ·
                        rfl

theorem cell23_4816037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_4816037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816037 prefixEnd_4816037 := by exact prefixLift 4816037
  have htrace : WordTrace (prefixWord ++ tailWord_4816037) baseStart_4816037 baseEnd_4816037 := by
    simpa [prefixWord, tailWord_4816037, baseEnd_4816037] using wordTrace_append hprefix tailTrace_4816037
  have hstable : (prefixWord ++ tailWord_4816037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816037).length < 2 ^ (prefixWord ++ tailWord_4816037).sum := by decide
  have hdescent : baseEnd_4816037 < baseStart_4816037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816045 : List Nat := [1, 5, 2, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_4816045 : Nat := 118140960795 + 4816045 * 2 ^ 59
def prefixEnd_4816045 : Nat := 4983230072969 + 3 ^ 40 * 4816045 * 2
def baseEnd_4816045 : Nat := 2472945938682714935488919

theorem tailTrace_4816045 : CollatzResearch.WordTrace tailWord_4816045 prefixEnd_4816045 2472945938682714935488919 := by
  unfold tailWord_4816045
  simp only [CollatzResearch.WordTrace]
  refine ⟨175655591837298954847345589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117103727891532636564897059 175655591837298954847345589)
  ·
    refine ⟨16467711734746777016938649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175655591837298954847345589 16467711734746777016938649)
    ·
      refine ⟨12350783801060082762703987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16467711734746777016938649 12350783801060082762703987)
      ·
        refine ⟨18526175701590124144055981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12350783801060082762703987 18526175701590124144055981)
        ·
          refine ⟨6947315888096296554020993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18526175701590124144055981 6947315888096296554020993)
          ·
            refine ⟨5210486916072222415515745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6947315888096296554020993 5210486916072222415515745)
            ·
              refine ⟨3907865187054166811636809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5210486916072222415515745 3907865187054166811636809)
              ·
                refine ⟨2930898890290625108727607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3907865187054166811636809 2930898890290625108727607)
                ·
                  refine ⟨4396348335435937663091411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930898890290625108727607 4396348335435937663091411)
                  ·
                    refine ⟨6594522503153906494637117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4396348335435937663091411 6594522503153906494637117)
                    ·
                      refine ⟨2472945938682714935488919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6594522503153906494637117 2472945938682714935488919)
                      ·
                        rfl

theorem cell23_4816045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_4816045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816045 prefixEnd_4816045 := by exact prefixLift 4816045
  have htrace : WordTrace (prefixWord ++ tailWord_4816045) baseStart_4816045 baseEnd_4816045 := by
    simpa [prefixWord, tailWord_4816045, baseEnd_4816045] using wordTrace_append hprefix tailTrace_4816045
  have hstable : (prefixWord ++ tailWord_4816045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816045).length < 2 ^ (prefixWord ++ tailWord_4816045).sum := by decide
  have hdescent : baseEnd_4816045 < baseStart_4816045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816088 : List Nat := [2, 1, 2, 2, 6, 1, 2, 1, 1, 2, 3]
def baseStart_4816088 : Nat := 118140960795 + 4816088 * 2 ^ 59
def prefixEnd_4816088 : Nat := 4983230072969 + 3 ^ 40 * 4816088 * 2
def baseEnd_4816088 : Nat := 2472968018350858267251221

theorem tailTrace_4816088 : CollatzResearch.WordTrace tailWord_4816088 prefixEnd_4816088 2472968018350858267251221 := by
  unfold tailWord_4816088
  simp only [CollatzResearch.WordTrace]
  refine ⟨87828580088071586595580459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117104773450762115460773945 87828580088071586595580459)
  ·
    refine ⟨131742870132107379893370689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87828580088071586595580459 131742870132107379893370689)
    ·
      refine ⟨98807152599080534920028017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131742870132107379893370689 98807152599080534920028017)
      ·
        refine ⟨74105364449310401190021013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98807152599080534920028017 74105364449310401190021013)
        ·
          refine ⟨3473688958561425055782235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74105364449310401190021013 3473688958561425055782235)
          ·
            refine ⟨5210533437842137583673353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3473688958561425055782235 5210533437842137583673353)
            ·
              refine ⟨3907900078381603187755015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5210533437842137583673353 3907900078381603187755015)
              ·
                refine ⟨5861850117572404781632523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3907900078381603187755015 5861850117572404781632523)
                ·
                  refine ⟨8792775176358607172448785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5861850117572404781632523 8792775176358607172448785)
                  ·
                    refine ⟨6594581382268955379336589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8792775176358607172448785 6594581382268955379336589)
                    ·
                      refine ⟨2472968018350858267251221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6594581382268955379336589 2472968018350858267251221)
                      ·
                        rfl

theorem cell23_4816088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_4816088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816088 prefixEnd_4816088 := by exact prefixLift 4816088
  have htrace : WordTrace (prefixWord ++ tailWord_4816088) baseStart_4816088 baseEnd_4816088 := by
    simpa [prefixWord, tailWord_4816088, baseEnd_4816088] using wordTrace_append hprefix tailTrace_4816088
  have hstable : (prefixWord ++ tailWord_4816088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816088).length < 2 ^ (prefixWord ++ tailWord_4816088).sum := by decide
  have hdescent : baseEnd_4816088 < baseStart_4816088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816100 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_4816100 : Nat := 118140960795 + 4816100 * 2 ^ 59
def prefixEnd_4816100 : Nat := 4983230072969 + 3 ^ 40 * 4816100 * 2
def baseEnd_4816100 : Nat := 824324726706237406767055

theorem tailTrace_4816100 : CollatzResearch.WordTrace tailWord_4816100 prefixEnd_4816100 824324726706237406767055 := by
  unfold tailWord_4816100
  simp only [CollatzResearch.WordTrace]
  refine ⟨87828798926049849620298877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117105065234733132827065169 87828798926049849620298877)
  ·
    refine ⟨32935799597268693607612079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87828798926049849620298877 32935799597268693607612079)
    ·
      refine ⟨49403699395903040411418119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32935799597268693607612079 49403699395903040411418119)
      ·
        refine ⟨74105549093854560617127179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49403699395903040411418119 74105549093854560617127179)
        ·
          refine ⟨111158323640781840925690769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74105549093854560617127179 111158323640781840925690769)
          ·
            refine ⟨83368742730586380694268077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111158323640781840925690769 83368742730586380694268077)
            ·
              refine ⟨31263278523969892760350529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83368742730586380694268077 31263278523969892760350529)
              ·
                refine ⟨23447458892977419570262897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31263278523969892760350529 23447458892977419570262897)
                ·
                  refine ⟨17585594169733064677697173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23447458892977419570262897 17585594169733064677697173)
                  ·
                    refine ⟨824324726706237406767055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17585594169733064677697173 824324726706237406767055)
                    ·
                      rfl

theorem cell23_4816100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_4816100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816100 prefixEnd_4816100 := by exact prefixLift 4816100
  have htrace : WordTrace (prefixWord ++ tailWord_4816100) baseStart_4816100 baseEnd_4816100 := by
    simpa [prefixWord, tailWord_4816100, baseEnd_4816100] using wordTrace_append hprefix tailTrace_4816100
  have hstable : (prefixWord ++ tailWord_4816100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816100).length < 2 ^ (prefixWord ++ tailWord_4816100).sum := by decide
  have hdescent : baseEnd_4816100 < baseStart_4816100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816231 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_4816231 : Nat := 118140960795 + 4816231 * 2 ^ 59
def prefixEnd_4816231 : Nat := 4983230072969 + 3 ^ 40 * 4816231 * 2
def baseEnd_4816231 : Nat := 2473041446084451207763063

theorem tailTrace_4816231 : CollatzResearch.WordTrace tailWord_4816231 prefixEnd_4816231 2473041446084451207763063 := by
  unfold tailWord_4816231
  simp only [CollatzResearch.WordTrace]
  refine ⟨175662375814625108613616547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117108250543083405742411031 175662375814625108613616547)
  ·
    refine ⟨263493563721937662920424821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175662375814625108613616547 263493563721937662920424821)
    ·
      refine ⟨24702521598931655898789827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 263493563721937662920424821 24702521598931655898789827)
      ·
        refine ⟨37053782398397483848184741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24702521598931655898789827 37053782398397483848184741)
        ·
          refine ⟨6947584199699528221534639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37053782398397483848184741 6947584199699528221534639)
          ·
            refine ⟨10421376299549292332301959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6947584199699528221534639 10421376299549292332301959)
            ·
              refine ⟨15632064449323938498452939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10421376299549292332301959 15632064449323938498452939)
              ·
                refine ⟨23448096673985907747679409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15632064449323938498452939 23448096673985907747679409)
                ·
                  refine ⟨17586072505489430810759557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23448096673985907747679409 17586072505489430810759557)
                  ·
                    refine ⟨3297388594779268277017417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17586072505489430810759557 3297388594779268277017417)
                    ·
                      refine ⟨2473041446084451207763063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3297388594779268277017417 2473041446084451207763063)
                      ·
                        rfl

theorem cell23_4816231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_4816231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816231 prefixEnd_4816231 := by exact prefixLift 4816231
  have htrace : WordTrace (prefixWord ++ tailWord_4816231) baseStart_4816231 baseEnd_4816231 := by
    simpa [prefixWord, tailWord_4816231, baseEnd_4816231] using wordTrace_append hprefix tailTrace_4816231
  have hstable : (prefixWord ++ tailWord_4816231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816231).length < 2 ^ (prefixWord ++ tailWord_4816231).sum := by decide
  have hdescent : baseEnd_4816231 < baseStart_4816231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816281 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 3, 1, 3]
def baseStart_4816281 : Nat := 118140960795 + 4816281 * 2 ^ 59
def prefixEnd_4816281 : Nat := 4983230072969 + 3 ^ 40 * 4816281 * 2
def baseEnd_4816281 : Nat := 2473067120117176012137833

theorem tailTrace_4816281 : CollatzResearch.WordTrace tailWord_4816281 prefixEnd_4816281 2473067120117176012137833 := by
  unfold tailWord_4816281
  simp only [CollatzResearch.WordTrace]
  refine ⟨175664199464443967152936697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117109466309629311435291131 175664199464443967152936697)
  ·
    refine ⟨131748149598332975364702523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175664199464443967152936697 131748149598332975364702523)
    ·
      refine ⟨197622224397499463047053785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131748149598332975364702523 197622224397499463047053785)
      ·
        refine ⟨148216668298124597285290339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197622224397499463047053785 148216668298124597285290339)
        ·
          refine ⟨222325002447186895927935509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148216668298124597285290339 222325002447186895927935509)
          ·
            refine ⟨10421484489711885746621977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 222325002447186895927935509 10421484489711885746621977)
            ·
              refine ⟨7816113367283914309966483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10421484489711885746621977 7816113367283914309966483)
              ·
                refine ⟨11724170050925871464949725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7816113367283914309966483 11724170050925871464949725)
                ·
                  refine ⟨4396563769097201799356147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11724170050925871464949725 4396563769097201799356147)
                  ·
                    refine ⟨6594845653645802699034221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4396563769097201799356147 6594845653645802699034221)
                    ·
                      refine ⟨2473067120117176012137833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6594845653645802699034221 2473067120117176012137833)
                      ·
                        rfl

theorem cell23_4816281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_4816281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816281 prefixEnd_4816281 := by exact prefixLift 4816281
  have htrace : WordTrace (prefixWord ++ tailWord_4816281) baseStart_4816281 baseEnd_4816281 := by
    simpa [prefixWord, tailWord_4816281, baseEnd_4816281] using wordTrace_append hprefix tailTrace_4816281
  have hstable : (prefixWord ++ tailWord_4816281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816281).length < 2 ^ (prefixWord ++ tailWord_4816281).sum := by decide
  have hdescent : baseEnd_4816281 < baseStart_4816281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816301 : List Nat := [1, 5, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_4816301 : Nat := 118140960795 + 4816301 * 2 ^ 59
def prefixEnd_4816301 : Nat := 4983230072969 + 3 ^ 40 * 4816301 * 2
def baseEnd_4816301 : Nat := 824359129910088644629247

theorem tailTrace_4816301 : CollatzResearch.WordTrace tailWord_4816301 prefixEnd_4816301 824359129910088644629247 := by
  unfold tailWord_4816301
  simp only [CollatzResearch.WordTrace]
  refine ⟨175664928924371510568664757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117109952616247673712443171 175664928924371510568664757)
  ·
    refine ⟨16468587086659829115812321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175664928924371510568664757 16468587086659829115812321)
    ·
      refine ⟨12351440314994871836859241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16468587086659829115812321 12351440314994871836859241)
      ·
        refine ⟨9263580236246153877644431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12351440314994871836859241 9263580236246153877644431)
        ·
          refine ⟨13895370354369230816466647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9263580236246153877644431 13895370354369230816466647)
          ·
            refine ⟨20843055531553846224699971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13895370354369230816466647 20843055531553846224699971)
            ·
              refine ⟨31264583297330769337049957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20843055531553846224699971 31264583297330769337049957)
              ·
                refine ⟨5862109368249519250696867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31264583297330769337049957 5862109368249519250696867)
                ·
                  refine ⟨8793164052374278876045301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5862109368249519250696867 8793164052374278876045301)
                  ·
                    refine ⟨824359129910088644629247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8793164052374278876045301 824359129910088644629247)
                    ·
                      rfl

theorem cell23_4816301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_4816301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816301 prefixEnd_4816301 := by exact prefixLift 4816301
  have htrace : WordTrace (prefixWord ++ tailWord_4816301) baseStart_4816301 baseEnd_4816301 := by
    simpa [prefixWord, tailWord_4816301, baseEnd_4816301] using wordTrace_append hprefix tailTrace_4816301
  have hstable : (prefixWord ++ tailWord_4816301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816301).length < 2 ^ (prefixWord ++ tailWord_4816301).sum := by decide
  have hdescent : baseEnd_4816301 < baseStart_4816301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816307 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 3]
def baseStart_4816307 : Nat := 118140960795 + 4816307 * 2 ^ 59
def prefixEnd_4816307 : Nat := 4983230072969 + 3 ^ 40 * 4816307 * 2
def baseEnd_4816307 : Nat := 2473080470614192910412713

theorem tailTrace_4816307 : CollatzResearch.WordTrace tailWord_4816307 prefixEnd_4816307 2473080470614192910412713 := by
  unfold tailWord_4816307
  simp only [CollatzResearch.WordTrace]
  refine ⟨175665147762349773593383175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117110098508233182395588783 175665147762349773593383175)
  ·
    refine ⟨263497721643524660390074763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175665147762349773593383175 263497721643524660390074763)
    ·
      refine ⟨395246582465286990585112145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263497721643524660390074763 395246582465286990585112145)
      ·
        refine ⟨296434936848965242938834109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395246582465286990585112145 296434936848965242938834109)
        ·
          refine ⟨111163101318361966102062791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296434936848965242938834109 111163101318361966102062791)
          ·
            refine ⟨166744651977542949153094187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111163101318361966102062791 166744651977542949153094187)
            ·
              refine ⟨250116977966314423729641281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166744651977542949153094187 250116977966314423729641281)
              ·
                refine ⟨187587733474735817797230961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250116977966314423729641281 187587733474735817797230961)
                ·
                  refine ⟨140690800106051863347923221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187587733474735817797230961 140690800106051863347923221)
                  ·
                    refine ⟨6594881254971181094433901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 140690800106051863347923221 6594881254971181094433901)
                    ·
                      refine ⟨2473080470614192910412713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6594881254971181094433901 2473080470614192910412713)
                      ·
                        rfl

theorem cell23_4816307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 3].length) (baseStart_4816307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816307 prefixEnd_4816307 := by exact prefixLift 4816307
  have htrace : WordTrace (prefixWord ++ tailWord_4816307) baseStart_4816307 baseEnd_4816307 := by
    simpa [prefixWord, tailWord_4816307, baseEnd_4816307] using wordTrace_append hprefix tailTrace_4816307
  have hstable : (prefixWord ++ tailWord_4816307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816307).length < 2 ^ (prefixWord ++ tailWord_4816307).sum := by decide
  have hdescent : baseEnd_4816307 < baseStart_4816307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816367 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 5]
def baseStart_4816367 : Nat := 118140960795 + 4816367 * 2 ^ 59
def prefixEnd_4816367 : Nat := 4983230072969 + 3 ^ 40 * 4816367 * 2
def baseEnd_4816367 : Nat := 2473111279453462675662437

theorem tailTrace_4816367 : CollatzResearch.WordTrace tailWord_4816367 prefixEnd_4816367 2473111279453462675662437 := by
  unfold tailWord_4816367
  simp only [CollatzResearch.WordTrace]
  refine ⟨175667336142132403840567355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117111557428088269227044903 175667336142132403840567355)
  ·
    refine ⟨263501004213198605760851033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175667336142132403840567355 263501004213198605760851033)
    ·
      refine ⟨197625753159898954320638275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263501004213198605760851033 197625753159898954320638275)
      ·
        refine ⟨296438629739848431480957413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197625753159898954320638275 296438629739848431480957413)
        ·
          refine ⟨55582243076221580902679515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296438629739848431480957413 55582243076221580902679515)
          ·
            refine ⟨83373364614332371354019273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55582243076221580902679515 83373364614332371354019273)
            ·
              refine ⟨62530023460749278515514455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83373364614332371354019273 62530023460749278515514455)
              ·
                refine ⟨93795035191123917773271683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62530023460749278515514455 93795035191123917773271683)
                ·
                  refine ⟨140692552786685876659907525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93795035191123917773271683 140692552786685876659907525)
                  ·
                    refine ⟨26379853647503601873732661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140692552786685876659907525 26379853647503601873732661)
                    ·
                      refine ⟨2473111279453462675662437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26379853647503601873732661 2473111279453462675662437)
                      ·
                        rfl

theorem cell23_4816367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_4816367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816367 prefixEnd_4816367 := by exact prefixLift 4816367
  have htrace : WordTrace (prefixWord ++ tailWord_4816367) baseStart_4816367 baseEnd_4816367 := by
    simpa [prefixWord, tailWord_4816367, baseEnd_4816367] using wordTrace_append hprefix tailTrace_4816367
  have hstable : (prefixWord ++ tailWord_4816367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816367).length < 2 ^ (prefixWord ++ tailWord_4816367).sum := by decide
  have hdescent : baseEnd_4816367 < baseStart_4816367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816394 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_4816394 : Nat := 118140960795 + 4816394 * 2 ^ 59
def prefixEnd_4816394 : Nat := 4983230072969 + 3 ^ 40 * 4816394 * 2
def baseEnd_4816394 : Nat := 2473125143431134070024813

theorem tailTrace_4816394 : CollatzResearch.WordTrace tailWord_4816394 prefixEnd_4816394 2473125143431134070024813 := by
  unfold tailWord_4816394
  simp only [CollatzResearch.WordTrace]
  refine ⟨43917080228258646862950059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117112213942023058301200157 43917080228258646862950059)
  ·
    refine ⟨65875620342387970294425089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43917080228258646862950059 65875620342387970294425089)
    ·
      refine ⟨49406715256790977720818817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65875620342387970294425089 49406715256790977720818817)
      ·
        refine ⟨37055036442593233290614113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49406715256790977720818817 37055036442593233290614113)
        ·
          refine ⟨27791277331944924967960585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37055036442593233290614113 27791277331944924967960585)
          ·
            refine ⟨20843457998958693725970439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27791277331944924967960585 20843457998958693725970439)
            ·
              refine ⟨31265186998438040588955659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20843457998958693725970439 31265186998438040588955659)
              ·
                refine ⟨46897780497657060883433489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31265186998438040588955659 46897780497657060883433489)
                ·
                  refine ⟨35173335373242795662575117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46897780497657060883433489 35173335373242795662575117)
                  ·
                    refine ⟨13190000764966048373465669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35173335373242795662575117 13190000764966048373465669)
                    ·
                      refine ⟨2473125143431134070024813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13190000764966048373465669 2473125143431134070024813)
                      ·
                        rfl

theorem cell23_4816394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_4816394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816394 prefixEnd_4816394 := by exact prefixLift 4816394
  have htrace : WordTrace (prefixWord ++ tailWord_4816394) baseStart_4816394 baseEnd_4816394 := by
    simpa [prefixWord, tailWord_4816394, baseEnd_4816394] using wordTrace_append hprefix tailTrace_4816394
  have hstable : (prefixWord ++ tailWord_4816394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816394).length < 2 ^ (prefixWord ++ tailWord_4816394).sum := by decide
  have hdescent : baseEnd_4816394 < baseStart_4816394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816427 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 7]
def baseStart_4816427 : Nat := 118140960795 + 4816427 * 2 ^ 59
def prefixEnd_4816427 : Nat := 4983230072969 + 3 ^ 40 * 4816427 * 2
def baseEnd_4816427 : Nat := 2473142088292732440912161

theorem tailTrace_4816427 : CollatzResearch.WordTrace tailWord_4816427 prefixEnd_4816427 2473142088292732440912161 := by
  unfold tailWord_4816427
  simp only [CollatzResearch.WordTrace]
  refine ⟨175669524521915034087751535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117113016347943356058501023 175669524521915034087751535)
  ·
    refine ⟨263504286782872551131627303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175669524521915034087751535 263504286782872551131627303)
    ·
      refine ⟨395256430174308826697440955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263504286782872551131627303 395256430174308826697440955)
      ·
        refine ⟨592884645261463240046161433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395256430174308826697440955 592884645261463240046161433)
        ·
          refine ⟨444663483946097430034621075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 592884645261463240046161433 444663483946097430034621075)
          ·
            refine ⟨666995225919146145051931613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444663483946097430034621075 666995225919146145051931613)
            ·
              refine ⟨250123209719679804394474355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 666995225919146145051931613 250123209719679804394474355)
              ·
                refine ⟨375184814579519706591711533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250123209719679804394474355 375184814579519706591711533)
                ·
                  refine ⟨140694305467319889971891825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375184814579519706591711533 140694305467319889971891825)
                  ·
                    refine ⟨105520729100489917478918869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 140694305467319889971891825 105520729100489917478918869)
                    ·
                      refine ⟨2473142088292732440912161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105520729100489917478918869 2473142088292732440912161)
                      ·
                        rfl

theorem cell23_4816427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_4816427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816427 prefixEnd_4816427 := by exact prefixLift 4816427
  have htrace : WordTrace (prefixWord ++ tailWord_4816427) baseStart_4816427 baseEnd_4816427 := by
    simpa [prefixWord, tailWord_4816427, baseEnd_4816427] using wordTrace_append hprefix tailTrace_4816427
  have hstable : (prefixWord ++ tailWord_4816427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816427).length < 2 ^ (prefixWord ++ tailWord_4816427).sum := by decide
  have hdescent : baseEnd_4816427 < baseStart_4816427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816445 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 4, 2, 2]
def baseStart_4816445 : Nat := 118140960795 + 4816445 * 2 ^ 59
def prefixEnd_4816445 : Nat := 4983230072969 + 3 ^ 40 * 4816445 * 2
def baseEnd_4816445 : Nat := 2473151330944513370487079

theorem tailTrace_4816445 : CollatzResearch.WordTrace tailWord_4816445 prefixEnd_4816445 2473151330944513370487079 := by
  unfold tailWord_4816445
  simp only [CollatzResearch.WordTrace]
  refine ⟨175670181035849823161906789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117113454023899882107937859 175670181035849823161906789)
  ·
    refine ⟨32938158944221841842857523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175670181035849823161906789 32938158944221841842857523)
    ·
      refine ⟨49407238416332762764286285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32938158944221841842857523 49407238416332762764286285)
      ·
        refine ⟨18527714406124786036607357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49407238416332762764286285 18527714406124786036607357)
        ·
          refine ⟨6947892902296794763727759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18527714406124786036607357 6947892902296794763727759)
          ·
            refine ⟨10421839353445192145591639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6947892902296794763727759 10421839353445192145591639)
            ·
              refine ⟨15632759030167788218387459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10421839353445192145591639 15632759030167788218387459)
              ·
                refine ⟨23449138545251682327581189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15632759030167788218387459 23449138545251682327581189)
                ·
                  refine ⟨4396713477234690436421473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23449138545251682327581189 4396713477234690436421473)
                  ·
                    refine ⟨3297535107926017827316105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4396713477234690436421473 3297535107926017827316105)
                    ·
                      refine ⟨2473151330944513370487079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3297535107926017827316105 2473151330944513370487079)
                      ·
                        rfl

theorem cell23_4816445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_4816445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816445 prefixEnd_4816445 := by exact prefixLift 4816445
  have htrace : WordTrace (prefixWord ++ tailWord_4816445) baseStart_4816445 baseEnd_4816445 := by
    simpa [prefixWord, tailWord_4816445, baseEnd_4816445] using wordTrace_append hprefix tailTrace_4816445
  have hstable : (prefixWord ++ tailWord_4816445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816445).length < 2 ^ (prefixWord ++ tailWord_4816445).sum := by decide
  have hdescent : baseEnd_4816445 < baseStart_4816445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816601 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 1, 6]
def baseStart_4816601 : Nat := 118140960795 + 4816601 * 2 ^ 59
def prefixEnd_4816601 : Nat := 4983230072969 + 3 ^ 40 * 4816601 * 2
def baseEnd_4816601 : Nat := 824410477975538253378787

theorem tailTrace_4816601 : CollatzResearch.WordTrace tailWord_4816601 prefixEnd_4816601 824410477975538253378787 := by
  unfold tailWord_4816601
  simp only [CollatzResearch.WordTrace]
  refine ⟨175675870823284661804585657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117117247215523107869723771 175675870823284661804585657)
  ·
    refine ⟨131756903117463496353439243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175675870823284661804585657 131756903117463496353439243)
    ·
      refine ⟨197635354676195244530158865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131756903117463496353439243 197635354676195244530158865)
      ·
        refine ⟨148226516007146433397619149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197635354676195244530158865 148226516007146433397619149)
        ·
          refine ⟨55584943502679912524107181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148226516007146433397619149 55584943502679912524107181)
          ·
            refine ⟨20844353813504967196540193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55584943502679912524107181 20844353813504967196540193)
            ·
              refine ⟨15633265360128725397405145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20844353813504967196540193 15633265360128725397405145)
              ·
                refine ⟨11724949020096544048053859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15633265360128725397405145 11724949020096544048053859)
                ·
                  refine ⟨17587423530144816072080789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11724949020096544048053859 17587423530144816072080789)
                  ·
                    refine ⟨824410477975538253378787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17587423530144816072080789 824410477975538253378787)
                    ·
                      rfl

theorem cell23_4816601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 6].length) (baseStart_4816601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816601 prefixEnd_4816601 := by exact prefixLift 4816601
  have htrace : WordTrace (prefixWord ++ tailWord_4816601) baseStart_4816601 baseEnd_4816601 := by
    simpa [prefixWord, tailWord_4816601, baseEnd_4816601] using wordTrace_append hprefix tailTrace_4816601
  have hstable : (prefixWord ++ tailWord_4816601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816601).length < 2 ^ (prefixWord ++ tailWord_4816601).sum := by decide
  have hdescent : baseEnd_4816601 < baseStart_4816601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816602 : List Nat := [3, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3]
def baseStart_4816602 : Nat := 118140960795 + 4816602 * 2 ^ 59
def prefixEnd_4816602 : Nat := 4983230072969 + 3 ^ 40 * 4816602 * 2
def baseEnd_4816602 : Nat := 2473231947407269256223857

theorem tailTrace_4816602 : CollatzResearch.WordTrace tailWord_4816602 prefixEnd_4816602 2473231947407269256223857 := by
  unfold tailWord_4816602
  simp only [CollatzResearch.WordTrace]
  refine ⟨43918976824070259743843015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117117271530854025983581373 43918976824070259743843015)
  ·
    refine ⟨65878465236105389615764523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43918976824070259743843015 65878465236105389615764523)
    ·
      refine ⟨98817697854158084423646785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65878465236105389615764523 98817697854158084423646785)
      ·
        refine ⟨74113273390618563317735089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98817697854158084423646785 74113273390618563317735089)
        ·
          refine ⟨55584955042963922488301317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74113273390618563317735089 55584955042963922488301317)
          ·
            refine ⟨10422179070555735466556497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55584955042963922488301317 10422179070555735466556497)
            ·
              refine ⟨7816634302916801599917373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10422179070555735466556497 7816634302916801599917373)
              ·
                refine ⟨2931237863593800599969015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7816634302916801599917373 2931237863593800599969015)
                ·
                  refine ⟨4396856795390700899953523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2931237863593800599969015 4396856795390700899953523)
                  ·
                    refine ⟨6595285193086051349930285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4396856795390700899953523 6595285193086051349930285)
                    ·
                      refine ⟨2473231947407269256223857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6595285193086051349930285 2473231947407269256223857)
                      ·
                        rfl

theorem cell23_4816602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_4816602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816602 prefixEnd_4816602 := by exact prefixLift 4816602
  have htrace : WordTrace (prefixWord ++ tailWord_4816602) baseStart_4816602 baseEnd_4816602 := by
    simpa [prefixWord, tailWord_4816602, baseEnd_4816602] using wordTrace_append hprefix tailTrace_4816602
  have hstable : (prefixWord ++ tailWord_4816602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816602).length < 2 ^ (prefixWord ++ tailWord_4816602).sum := by decide
  have hdescent : baseEnd_4816602 < baseStart_4816602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816625 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 3, 2, 2]
def baseStart_4816625 : Nat := 118140960795 + 4816625 * 2 ^ 59
def prefixEnd_4816625 : Nat := 4983230072969 + 3 ^ 40 * 4816625 * 2
def baseEnd_4816625 : Nat := 2473243757462322666236251

theorem tailTrace_4816625 : CollatzResearch.WordTrace tailWord_4816625 prefixEnd_4816625 2473243757462322666236251 := by
  unfold tailWord_4816625
  simp only [CollatzResearch.WordTrace]
  refine ⟨175676746175197713903459329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117117830783465142602306219 175676746175197713903459329)
  ·
    refine ⟨131757559631398285427594497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175676746175197713903459329 131757559631398285427594497)
    ·
      refine ⟨98818169723548714070695873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131757559631398285427594497 98818169723548714070695873)
      ·
        refine ⟨74113627292661535553021905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98818169723548714070695873 74113627292661535553021905)
        ·
          refine ⟨55585220469496151664766429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74113627292661535553021905 55585220469496151664766429)
          ·
            refine ⟨20844457676061056874287411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55585220469496151664766429 20844457676061056874287411)
            ·
              refine ⟨31266686514091585311431117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20844457676061056874287411 31266686514091585311431117)
              ·
                refine ⟨11725007442784344491786669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31266686514091585311431117 11725007442784344491786669)
                ·
                  refine ⟨4396877791044129184420001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11725007442784344491786669 4396877791044129184420001)
                  ·
                    refine ⟨3297658343283096888315001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4396877791044129184420001 3297658343283096888315001)
                    ·
                      refine ⟨2473243757462322666236251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3297658343283096888315001 2473243757462322666236251)
                      ·
                        rfl

theorem cell23_4816625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_4816625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816625 prefixEnd_4816625 := by exact prefixLift 4816625
  have htrace : WordTrace (prefixWord ++ tailWord_4816625) baseStart_4816625 baseEnd_4816625 := by
    simpa [prefixWord, tailWord_4816625, baseEnd_4816625] using wordTrace_append hprefix tailTrace_4816625
  have hstable : (prefixWord ++ tailWord_4816625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816625).length < 2 ^ (prefixWord ++ tailWord_4816625).sum := by decide
  have hdescent : baseEnd_4816625 < baseStart_4816625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816642 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_4816642 : Nat := 118140960795 + 4816642 * 2 ^ 59
def prefixEnd_4816642 : Nat := 4983230072969 + 3 ^ 40 * 4816642 * 2
def baseEnd_4816642 : Nat := 2473252486633449099723673

theorem tailTrace_4816642 : CollatzResearch.WordTrace tailWord_4816642 prefixEnd_4816642 2473252486633449099723673 := by
  unfold tailWord_4816642
  simp only [CollatzResearch.WordTrace]
  refine ⟨43919341554034031451707045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117118244144090750537885453 43919341554034031451707045)
  ·
    refine ⟨8234876541381380897195071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43919341554034031451707045 8234876541381380897195071)
    ·
      refine ⟨12352314812072071345792607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8234876541381380897195071 12352314812072071345792607)
      ·
        refine ⟨18528472218108107018688911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12352314812072071345792607 18528472218108107018688911)
        ·
          refine ⟨27792708327162160528033367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18528472218108107018688911 27792708327162160528033367)
          ·
            refine ⟨41689062490743240792050051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27792708327162160528033367 41689062490743240792050051)
            ·
              refine ⟨62533593736114861188075077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41689062490743240792050051 62533593736114861188075077)
              ·
                refine ⟨11725048825521536472764077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62533593736114861188075077 11725048825521536472764077)
                ·
                  refine ⟨4396893309570576177286529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11725048825521536472764077 4396893309570576177286529)
                  ·
                    refine ⟨3297669982177932132964897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4396893309570576177286529 3297669982177932132964897)
                    ·
                      refine ⟨2473252486633449099723673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3297669982177932132964897 2473252486633449099723673)
                      ·
                        rfl

theorem cell23_4816642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_4816642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816642 prefixEnd_4816642 := by exact prefixLift 4816642
  have htrace : WordTrace (prefixWord ++ tailWord_4816642) baseStart_4816642 baseEnd_4816642 := by
    simpa [prefixWord, tailWord_4816642, baseEnd_4816642] using wordTrace_append hprefix tailTrace_4816642
  have hstable : (prefixWord ++ tailWord_4816642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816642).length < 2 ^ (prefixWord ++ tailWord_4816642).sum := by decide
  have hdescent : baseEnd_4816642 < baseStart_4816642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816671 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 5]
def baseStart_4816671 : Nat := 118140960795 + 4816671 * 2 ^ 59
def prefixEnd_4816671 : Nat := 4983230072969 + 3 ^ 40 * 4816671 * 2
def baseEnd_4816671 : Nat := 2473267377572429486261039

theorem tailTrace_4816671 : CollatzResearch.WordTrace tailWord_4816671 prefixEnd_4816671 2473267377572429486261039 := by
  unfold tailWord_4816671
  simp only [CollatzResearch.WordTrace]
  refine ⟨175678423933031063759633867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117118949288687375839755911 175678423933031063759633867)
  ·
    refine ⟨263517635899546595639450801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175678423933031063759633867 263517635899546595639450801)
    ·
      refine ⟨197638226924659946729588101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263517635899546595639450801 197638226924659946729588101)
      ·
        refine ⟨37057167548373740011797769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197638226924659946729588101 37057167548373740011797769)
        ·
          refine ⟨27792875661280305008848327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37057167548373740011797769 27792875661280305008848327)
          ·
            refine ⟨41689313491920457513272491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27792875661280305008848327 41689313491920457513272491)
            ·
              refine ⟨62533970237880686269908737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41689313491920457513272491 62533970237880686269908737)
              ·
                refine ⟨46900477678410514702431553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62533970237880686269908737 46900477678410514702431553)
                ·
                  refine ⟨35175358258807886026823665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46900477678410514702431553 35175358258807886026823665)
                  ·
                    refine ⟨26381518694105914520117749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35175358258807886026823665 26381518694105914520117749)
                    ·
                      refine ⟨2473267377572429486261039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26381518694105914520117749 2473267377572429486261039)
                      ·
                        rfl

theorem cell23_4816671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_4816671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816671 prefixEnd_4816671 := by exact prefixLift 4816671
  have htrace : WordTrace (prefixWord ++ tailWord_4816671) baseStart_4816671 baseEnd_4816671 := by
    simpa [prefixWord, tailWord_4816671, baseEnd_4816671] using wordTrace_append hprefix tailTrace_4816671
  have hstable : (prefixWord ++ tailWord_4816671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816671).length < 2 ^ (prefixWord ++ tailWord_4816671).sum := by decide
  have hdescent : baseEnd_4816671 < baseStart_4816671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816676 : List Nat := [2, 3, 1, 3, 2, 2, 3, 2, 1, 2, 2]
def baseStart_4816676 : Nat := 118140960795 + 4816676 * 2 ^ 59
def prefixEnd_4816676 : Nat := 4983230072969 + 3 ^ 40 * 4816676 * 2
def baseEnd_4816676 : Nat := 2473269944975701966698517

theorem tailTrace_4816676 : CollatzResearch.WordTrace tailWord_4816676 prefixEnd_4816676 2473269944975701966698517 := by
  unfold tailWord_4816676
  simp only [CollatzResearch.WordTrace]
  refine ⟨87839303149006474806782941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117119070865341966409043921 87839303149006474806782941)
  ·
    refine ⟨32939738680877428052543603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87839303149006474806782941 32939738680877428052543603)
    ·
      refine ⟨49409608021316142078815405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32939738680877428052543603 49409608021316142078815405)
      ·
        refine ⟨18528603007993553279555777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49409608021316142078815405 18528603007993553279555777)
        ·
          refine ⟨13896452255995164959666833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18528603007993553279555777 13896452255995164959666833)
          ·
            refine ⟨10422339191996373719750125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13896452255995164959666833 10422339191996373719750125)
            ·
              refine ⟨3908377196998640144906297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10422339191996373719750125 3908377196998640144906297)
              ·
                refine ⟨2931282897748980108679723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3908377196998640144906297 2931282897748980108679723)
                ·
                  refine ⟨4396924346623470163019585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2931282897748980108679723 4396924346623470163019585)
                  ·
                    refine ⟨3297693259967602622264689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4396924346623470163019585 3297693259967602622264689)
                    ·
                      refine ⟨2473269944975701966698517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3297693259967602622264689 2473269944975701966698517)
                      ·
                        rfl

theorem cell23_4816676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_4816676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816676 prefixEnd_4816676 := by exact prefixLift 4816676
  have htrace : WordTrace (prefixWord ++ tailWord_4816676) baseStart_4816676 baseEnd_4816676 := by
    simpa [prefixWord, tailWord_4816676, baseEnd_4816676] using wordTrace_append hprefix tailTrace_4816676
  have hstable : (prefixWord ++ tailWord_4816676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816676).length < 2 ^ (prefixWord ++ tailWord_4816676).sum := by decide
  have hdescent : baseEnd_4816676 < baseStart_4816676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816686 : List Nat := [4, 1, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_4816686 : Nat := 118140960795 + 4816686 * 2 ^ 59
def prefixEnd_4816686 : Nat := 4983230072969 + 3 ^ 40 * 4816686 * 2
def baseEnd_4816686 : Nat := 824425026594082309191157

theorem tailTrace_4816686 : CollatzResearch.WordTrace tailWord_4816686 prefixEnd_4816686 824425026594082309191157 := by
  unfold tailWord_4816686
  simp only [CollatzResearch.WordTrace]
  refine ⟨21959871378497090165178739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117119314018651147547619941 21959871378497090165178739)
  ·
    refine ⟨32939807067745635247768109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21959871378497090165178739 32939807067745635247768109)
    ·
      refine ⟨12352427650404613217913041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32939807067745635247768109 12352427650404613217913041)
      ·
        refine ⟨9264320737803459913434781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12352427650404613217913041 9264320737803459913434781)
        ·
          refine ⟨3474120276676297467538043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9264320737803459913434781 3474120276676297467538043)
          ·
            refine ⟨5211180415014446201307065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3474120276676297467538043 5211180415014446201307065)
            ·
              refine ⟨3908385311260834650980299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5211180415014446201307065 3908385311260834650980299)
              ·
                refine ⟨5862577966891251976470449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3908385311260834650980299 5862577966891251976470449)
                ·
                  refine ⟨4396933475168438982352837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5862577966891251976470449 4396933475168438982352837)
                  ·
                    refine ⟨824425026594082309191157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4396933475168438982352837 824425026594082309191157)
                    ·
                      rfl

theorem cell23_4816686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_4816686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816686 prefixEnd_4816686 := by exact prefixLift 4816686
  have htrace : WordTrace (prefixWord ++ tailWord_4816686) baseStart_4816686 baseEnd_4816686 := by
    simpa [prefixWord, tailWord_4816686, baseEnd_4816686] using wordTrace_append hprefix tailTrace_4816686
  have hstable : (prefixWord ++ tailWord_4816686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816686).length < 2 ^ (prefixWord ++ tailWord_4816686).sum := by decide
  have hdescent : baseEnd_4816686 < baseStart_4816686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816702 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_4816702 : Nat := 118140960795 + 4816702 * 2 ^ 59
def prefixEnd_4816702 : Nat := 4983230072969 + 3 ^ 40 * 4816702 * 2
def baseEnd_4816702 : Nat := 2473283295472718864973397

theorem tailTrace_4816702 : CollatzResearch.WordTrace tailWord_4816702 prefixEnd_4816702 2473283295472718864973397 := by
  unfold tailWord_4816702
  simp only [CollatzResearch.WordTrace]
  refine ⟨21959944324489844506751545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117119703063945837369341573 21959944324489844506751545)
  ·
    refine ⟨16469958243367383380063659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21959944324489844506751545 16469958243367383380063659)
    ·
      refine ⟨24704937365051075070095489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16469958243367383380063659 24704937365051075070095489)
      ·
        refine ⟨18528703023788306302571617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24704937365051075070095489 18528703023788306302571617)
        ·
          refine ⟨13896527267841229726928713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18528703023788306302571617 13896527267841229726928713)
          ·
            refine ⟨10422395450880922295196535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13896527267841229726928713 10422395450880922295196535)
            ·
              refine ⟨15633593176321383442794803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10422395450880922295196535 15633593176321383442794803)
              ·
                refine ⟨23450389764482075164192205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15633593176321383442794803 23450389764482075164192205)
                ·
                  refine ⟨8793896161680778186572077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23450389764482075164192205 8793896161680778186572077)
                  ·
                    refine ⟨3297711060630291819964529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8793896161680778186572077 3297711060630291819964529)
                    ·
                      refine ⟨2473283295472718864973397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3297711060630291819964529 2473283295472718864973397)
                      ·
                        rfl

theorem cell23_4816702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_4816702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816702 prefixEnd_4816702 := by exact prefixLift 4816702
  have htrace : WordTrace (prefixWord ++ tailWord_4816702) baseStart_4816702 baseEnd_4816702 := by
    simpa [prefixWord, tailWord_4816702, baseEnd_4816702] using wordTrace_append hprefix tailTrace_4816702
  have hstable : (prefixWord ++ tailWord_4816702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816702).length < 2 ^ (prefixWord ++ tailWord_4816702).sum := by decide
  have hdescent : baseEnd_4816702 < baseStart_4816702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816741 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_4816741 : Nat := 118140960795 + 4816741 * 2 ^ 59
def prefixEnd_4816741 : Nat := 4983230072969 + 3 ^ 40 * 4816741 * 2
def baseEnd_4816741 : Nat := 2473303321218244212385717

theorem tailTrace_4816741 : CollatzResearch.WordTrace tailWord_4816741 prefixEnd_4816741 2473303321218244212385717 := by
  unfold tailWord_4816741
  simp only [CollatzResearch.WordTrace]
  refine ⟨175680977042777465714682077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117120651361851643809788051 175680977042777465714682077)
  ·
    refine ⟨65880366391041549643005779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175680977042777465714682077 65880366391041549643005779)
    ·
      refine ⟨98820549586562324464508669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65880366391041549643005779 98820549586562324464508669)
      ·
        refine ⟨37057706094960871674190751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98820549586562324464508669 37057706094960871674190751)
        ·
          refine ⟨55586559142441307511286127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37057706094960871674190751 55586559142441307511286127)
          ·
            refine ⟨83379838713661961266929191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55586559142441307511286127 83379838713661961266929191)
            ·
              refine ⟨125069758070492941900393787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83379838713661961266929191 125069758070492941900393787)
              ·
                refine ⟨187604637105739412850590681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125069758070492941900393787 187604637105739412850590681)
                ·
                  refine ⟨140703477829304559637943011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187604637105739412850590681 140703477829304559637943011)
                  ·
                    refine ⟨211055216743956839456914517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140703477829304559637943011 211055216743956839456914517)
                    ·
                      refine ⟨2473303321218244212385717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 211055216743956839456914517 2473303321218244212385717)
                      ·
                        rfl

theorem cell23_4816741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_4816741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816741 prefixEnd_4816741 := by exact prefixLift 4816741
  have htrace : WordTrace (prefixWord ++ tailWord_4816741) baseStart_4816741 baseEnd_4816741 := by
    simpa [prefixWord, tailWord_4816741, baseEnd_4816741] using wordTrace_append hprefix tailTrace_4816741
  have hstable : (prefixWord ++ tailWord_4816741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816741).length < 2 ^ (prefixWord ++ tailWord_4816741).sum := by decide
  have hdescent : baseEnd_4816741 < baseStart_4816741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816748 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 3]
def baseStart_4816748 : Nat := 118140960795 + 4816748 * 2 ^ 59
def prefixEnd_4816748 : Nat := 4983230072969 + 3 ^ 40 * 4816748 * 2
def baseEnd_4816748 : Nat := 2473306915582825684998185

theorem tailTrace_4816748 : CollatzResearch.WordTrace tailWord_4816748 prefixEnd_4816748 2473306915582825684998185 := by
  unfold tailWord_4816748
  simp only [CollatzResearch.WordTrace]
  refine ⟨87840616176876052955093449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117120821569168070606791265 87840616176876052955093449)
  ·
    refine ⟨65880462132657039716320087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87840616176876052955093449 65880462132657039716320087)
    ·
      refine ⟨98820693198985559574480131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65880462132657039716320087 98820693198985559574480131)
      ·
        refine ⟨148231039798478339361720197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98820693198985559574480131 148231039798478339361720197)
        ·
          refine ⟨27793319962214688630322537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148231039798478339361720197 27793319962214688630322537)
          ·
            refine ⟨20844989971661016472741903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27793319962214688630322537 20844989971661016472741903)
            ·
              refine ⟨31267484957491524709112855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20844989971661016472741903 31267484957491524709112855)
              ·
                refine ⟨46901227436237287063669283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31267484957491524709112855 46901227436237287063669283)
                ·
                  refine ⟨70351841154355930595503925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46901227436237287063669283 70351841154355930595503925)
                  ·
                    refine ⟨6595485108220868493328493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70351841154355930595503925 6595485108220868493328493)
                    ·
                      refine ⟨2473306915582825684998185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6595485108220868493328493 2473306915582825684998185)
                      ·
                        rfl

theorem cell23_4816748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_4816748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816748 prefixEnd_4816748 := by exact prefixLift 4816748
  have htrace : WordTrace (prefixWord ++ tailWord_4816748) baseStart_4816748 baseEnd_4816748 := by
    simpa [prefixWord, tailWord_4816748, baseEnd_4816748] using wordTrace_append hprefix tailTrace_4816748
  have hstable : (prefixWord ++ tailWord_4816748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816748).length < 2 ^ (prefixWord ++ tailWord_4816748).sum := by decide
  have hdescent : baseEnd_4816748 < baseStart_4816748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816811 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 12]
def baseStart_4816811 : Nat := 118140960795 + 4816811 * 2 ^ 59
def prefixEnd_4816811 : Nat := 4983230072969 + 3 ^ 40 * 4816811 * 2
def baseEnd_4816811 : Nat := 274815473873784326501155

theorem tailTrace_4816811 : CollatzResearch.WordTrace tailWord_4816811 prefixEnd_4816811 274815473873784326501155 := by
  unfold tailWord_4816811
  simp only [CollatzResearch.WordTrace]
  refine ⟨175683530152523867669730287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117122353435015911779820191 175683530152523867669730287)
  ·
    refine ⟨263525295228785801504595431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175683530152523867669730287 263525295228785801504595431)
    ·
      refine ⟨395287942843178702256893147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263525295228785801504595431 395287942843178702256893147)
      ·
        refine ⟨592931914264768053385339721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395287942843178702256893147 592931914264768053385339721)
        ·
          refine ⟨444698935698576040039004791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 592931914264768053385339721 444698935698576040039004791)
          ·
            refine ⟨667048403547864060058507187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444698935698576040039004791 667048403547864060058507187)
            ·
              refine ⟨1000572605321796090087760781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667048403547864060058507187 1000572605321796090087760781)
              ·
                refine ⟨375214726995673533782910293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1000572605321796090087760781 375214726995673533782910293)
                ·
                  refine ⟨274815473873784326501155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 375214726995673533782910293 274815473873784326501155)
                  ·
                    rfl

theorem cell23_4816811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 12].length) (baseStart_4816811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816811 prefixEnd_4816811 := by exact prefixLift 4816811
  have htrace : WordTrace (prefixWord ++ tailWord_4816811) baseStart_4816811 baseEnd_4816811 := by
    simpa [prefixWord, tailWord_4816811, baseEnd_4816811] using wordTrace_append hprefix tailTrace_4816811
  have hstable : (prefixWord ++ tailWord_4816811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816811).length < 2 ^ (prefixWord ++ tailWord_4816811).sum := by decide
  have hdescent : baseEnd_4816811 < baseStart_4816811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816825 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 2, 2, 3]
def baseStart_4816825 : Nat := 118140960795 + 4816825 * 2 ^ 59
def prefixEnd_4816825 : Nat := 4983230072969 + 3 ^ 40 * 4816825 * 2
def baseEnd_4816825 : Nat := 2473346453593221883735331

theorem tailTrace_4816825 : CollatzResearch.WordTrace tailWord_4816825 prefixEnd_4816825 2473346453593221883735331 := by
  unfold tailWord_4816825
  simp only [CollatzResearch.WordTrace]
  refine ⟨175684040774473148060739929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117122693849648765373826619 175684040774473148060739929)
  ·
    refine ⟨131763030580854861045554947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175684040774473148060739929 131763030580854861045554947)
    ·
      refine ⟨197644545871282291568332421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131763030580854861045554947 197644545871282291568332421)
      ·
        refine ⟨37058352350865429669062329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197644545871282291568332421 37058352350865429669062329)
        ·
          refine ⟨27793764263149072251796747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37058352350865429669062329 27793764263149072251796747)
          ·
            refine ⟨41690646394723608377695121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27793764263149072251796747 41690646394723608377695121)
            ·
              refine ⟨31267984796042706283271341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41690646394723608377695121 31267984796042706283271341)
              ·
                refine ⟨11725494298516014856226753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31267984796042706283271341 11725494298516014856226753)
                ·
                  refine ⟨8794120723887011142170065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11725494298516014856226753 8794120723887011142170065)
                  ·
                    refine ⟨6595590542915258356627549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8794120723887011142170065 6595590542915258356627549)
                    ·
                      refine ⟨2473346453593221883735331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6595590542915258356627549 2473346453593221883735331)
                      ·
                        rfl

theorem cell23_4816825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_4816825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816825 prefixEnd_4816825 := by exact prefixLift 4816825
  have htrace : WordTrace (prefixWord ++ tailWord_4816825) baseStart_4816825 baseEnd_4816825 := by
    simpa [prefixWord, tailWord_4816825, baseEnd_4816825] using wordTrace_append hprefix tailTrace_4816825
  have hstable : (prefixWord ++ tailWord_4816825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816825).length < 2 ^ (prefixWord ++ tailWord_4816825).sum := by decide
  have hdescent : baseEnd_4816825 < baseStart_4816825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816865 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 3, 5, 2]
def baseStart_4816865 : Nat := 118140960795 + 4816865 * 2 ^ 59
def prefixEnd_4816865 : Nat := 4983230072969 + 3 ^ 40 * 4816865 * 2
def baseEnd_4816865 : Nat := 2473366992819401727235147

theorem tailTrace_4816865 : CollatzResearch.WordTrace tailWord_4816865 prefixEnd_4816865 2473366992819401727235147 := by
  unfold tailWord_4816865
  simp only [CollatzResearch.WordTrace]
  refine ⟨175685499694328234892196049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117123666462885489928130699 175685499694328234892196049)
  ·
    refine ⟨131764124770746176169147037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175685499694328234892196049 131764124770746176169147037)
    ·
      refine ⟨49411546789029816063430139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131764124770746176169147037 49411546789029816063430139)
      ·
        refine ⟨74117320183544724095145209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49411546789029816063430139 74117320183544724095145209)
        ·
          refine ⟨55587990137658543071358907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74117320183544724095145209 55587990137658543071358907)
          ·
            refine ⟨83381985206487814607038361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55587990137658543071358907 83381985206487814607038361)
            ·
              refine ⟨62536488904865860955278771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83381985206487814607038361 62536488904865860955278771)
              ·
                refine ⟨93804733357298791432918157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62536488904865860955278771 93804733357298791432918157)
                ·
                  refine ⟨35176775008987046787344309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93804733357298791432918157 35176775008987046787344309)
                  ·
                    refine ⟨3297822657092535636313529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35176775008987046787344309 3297822657092535636313529)
                    ·
                      refine ⟨2473366992819401727235147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3297822657092535636313529 2473366992819401727235147)
                      ·
                        rfl

theorem cell23_4816865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_4816865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816865 prefixEnd_4816865 := by exact prefixLift 4816865
  have htrace : WordTrace (prefixWord ++ tailWord_4816865) baseStart_4816865 baseEnd_4816865 := by
    simpa [prefixWord, tailWord_4816865, baseEnd_4816865] using wordTrace_append hprefix tailTrace_4816865
  have hstable : (prefixWord ++ tailWord_4816865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816865).length < 2 ^ (prefixWord ++ tailWord_4816865).sum := by decide
  have hdescent : baseEnd_4816865 < baseStart_4816865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816888 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 3, 6]
def baseStart_4816888 : Nat := 118140960795 + 4816888 * 2 ^ 59
def prefixEnd_4816888 : Nat := 4983230072969 + 3 ^ 40 * 4816888 * 2
def baseEnd_4816888 : Nat := 824459600958151712415847

theorem tailTrace_4816888 : CollatzResearch.WordTrace tailWord_4816888 prefixEnd_4816888 824459600958151712415847 := by
  unfold tailWord_4816888
  simp only [CollatzResearch.WordTrace]
  refine ⟨87843169286622454910141659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117124225715496606546855545 87843169286622454910141659)
  ·
    refine ⟨131764753929933682365212489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87843169286622454910141659 131764753929933682365212489)
    ·
      refine ⟨98823565447450261773909367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131764753929933682365212489 98823565447450261773909367)
      ·
        refine ⟨148235348171175392660864051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98823565447450261773909367 148235348171175392660864051)
        ·
          refine ⟨222353022256763088991296077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148235348171175392660864051 222353022256763088991296077)
          ·
            refine ⟨83382383346286158371736029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222353022256763088991296077 83382383346286158371736029)
            ·
              refine ⟨31268393754857309389401011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83382383346286158371736029 31268393754857309389401011)
              ·
                refine ⟨46902590632285964084101517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31268393754857309389401011 46902590632285964084101517)
                ·
                  refine ⟨17588471487107236531538069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46902590632285964084101517 17588471487107236531538069)
                  ·
                    refine ⟨824459600958151712415847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17588471487107236531538069 824459600958151712415847)
                    ·
                      rfl

theorem cell23_4816888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_4816888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816888 prefixEnd_4816888 := by exact prefixLift 4816888
  have htrace : WordTrace (prefixWord ++ tailWord_4816888) baseStart_4816888 baseEnd_4816888 := by
    simpa [prefixWord, tailWord_4816888, baseEnd_4816888] using wordTrace_append hprefix tailTrace_4816888
  have hstable : (prefixWord ++ tailWord_4816888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816888).length < 2 ^ (prefixWord ++ tailWord_4816888).sum := by decide
  have hdescent : baseEnd_4816888 < baseStart_4816888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816892 : List Nat := [2, 2, 2, 1, 2, 2, 5, 1, 1, 5]
def baseStart_4816892 : Nat := 118140960795 + 4816892 * 2 ^ 59
def prefixEnd_4816892 : Nat := 4983230072969 + 3 ^ 40 * 4816892 * 2
def baseEnd_4816892 : Nat := 824460285599024373865841

theorem tailTrace_4816892 : CollatzResearch.WordTrace tailWord_4816892 prefixEnd_4816892 824460285599024373865841 := by
  unfold tailWord_4816892
  simp only [CollatzResearch.WordTrace]
  refine ⟨87843242232615209251714465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117124322976820279002285953 87843242232615209251714465)
  ·
    refine ⟨65882431674461406938785849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87843242232615209251714465 65882431674461406938785849)
    ·
      refine ⟨49411823755846055204089387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65882431674461406938785849 49411823755846055204089387)
      ·
        refine ⟨74117735633769082806134081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49411823755846055204089387 74117735633769082806134081)
        ·
          refine ⟨55588301725326812104600561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74117735633769082806134081 55588301725326812104600561)
          ·
            refine ⟨41691226293995109078450421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55588301725326812104600561 41691226293995109078450421)
            ·
              refine ⟨3908552465062041476104727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41691226293995109078450421 3908552465062041476104727)
              ·
                refine ⟨5862828697593062214157091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3908552465062041476104727 5862828697593062214157091)
                ·
                  refine ⟨8794243046389593321235637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5862828697593062214157091 8794243046389593321235637)
                  ·
                    refine ⟨824460285599024373865841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8794243046389593321235637 824460285599024373865841)
                    ·
                      rfl

theorem cell23_4816892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_4816892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816892 prefixEnd_4816892 := by exact prefixLift 4816892
  have htrace : WordTrace (prefixWord ++ tailWord_4816892) baseStart_4816892 baseEnd_4816892 := by
    simpa [prefixWord, tailWord_4816892, baseEnd_4816892] using wordTrace_append hprefix tailTrace_4816892
  have hstable : (prefixWord ++ tailWord_4816892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816892).length < 2 ^ (prefixWord ++ tailWord_4816892).sum := by decide
  have hdescent : baseEnd_4816892 < baseStart_4816892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816895 : List Nat := [1, 1, 2, 2, 1, 2, 1, 7, 1, 1, 4]
def baseStart_4816895 : Nat := 118140960795 + 4816895 * 2 ^ 59
def prefixEnd_4816895 : Nat := 4983230072969 + 3 ^ 40 * 4816895 * 2
def baseEnd_4816895 : Nat := 2473382397239036609860009

theorem tailTrace_4816895 : CollatzResearch.WordTrace tailWord_4816895 prefixEnd_4816895 2473382397239036609860009 := by
  unfold tailWord_4816895
  simp only [CollatzResearch.WordTrace]
  refine ⟨175686593884219550015788139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117124395922813033343858759 175686593884219550015788139)
  ·
    refine ⟨263529890826329325023682209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175686593884219550015788139 263529890826329325023682209)
    ·
      refine ⟨197647418119746993767761657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263529890826329325023682209 197647418119746993767761657)
      ·
        refine ⟨148235563589810245325821243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197647418119746993767761657 148235563589810245325821243)
        ·
          refine ⟨222353345384715367988731865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148235563589810245325821243 222353345384715367988731865)
          ·
            refine ⟨166765009038536525991548899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222353345384715367988731865 166765009038536525991548899)
            ·
              refine ⟨250147513557804788987323349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166765009038536525991548899 250147513557804788987323349)
              ·
                refine ⟨5862832349011049741890391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 250147513557804788987323349 5862832349011049741890391)
                ·
                  refine ⟨8794248523516574612835587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5862832349011049741890391 8794248523516574612835587)
                  ·
                    refine ⟨13191372785274861919253381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8794248523516574612835587 13191372785274861919253381)
                    ·
                      refine ⟨2473382397239036609860009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13191372785274861919253381 2473382397239036609860009)
                      ·
                        rfl

theorem cell23_4816895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_4816895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816895 prefixEnd_4816895 := by exact prefixLift 4816895
  have htrace : WordTrace (prefixWord ++ tailWord_4816895) baseStart_4816895 baseEnd_4816895 := by
    simpa [prefixWord, tailWord_4816895, baseEnd_4816895] using wordTrace_append hprefix tailTrace_4816895
  have hstable : (prefixWord ++ tailWord_4816895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816895).length < 2 ^ (prefixWord ++ tailWord_4816895).sum := by decide
  have hdescent : baseEnd_4816895 < baseStart_4816895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816900 : List Nat := [2, 3, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_4816900 : Nat := 118140960795 + 4816900 * 2 ^ 59
def prefixEnd_4816900 : Nat := 4983230072969 + 3 ^ 40 * 4816900 * 2
def baseEnd_4816900 : Nat := 824461654880769696765829

theorem tailTrace_4816900 : CollatzResearch.WordTrace tailWord_4816900 prefixEnd_4816900 824461654880769696765829 := by
  unfold tailWord_4816900
  simp only [CollatzResearch.WordTrace]
  refine ⟨87843388124600717934860077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117124517499467623913146769 87843388124600717934860077)
  ·
    refine ⟨32941270546725269225572529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87843388124600717934860077 32941270546725269225572529)
    ·
      refine ⟨24705952910043951919179397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32941270546725269225572529 24705952910043951919179397)
      ·
        refine ⟨4632366170633240984846137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24705952910043951919179397 4632366170633240984846137)
        ·
          refine ⟨3474274627974930738634603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4632366170633240984846137 3474274627974930738634603)
          ·
            refine ⟨5211411941962396107951905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3474274627974930738634603 5211411941962396107951905)
            ·
              refine ⟨3908558956471797080963929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5211411941962396107951905 3908558956471797080963929)
              ·
                refine ⟨2931419217353847810722947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3908558956471797080963929 2931419217353847810722947)
                ·
                  refine ⟨4397128826030771716084421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2931419217353847810722947 4397128826030771716084421)
                  ·
                    refine ⟨824461654880769696765829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4397128826030771716084421 824461654880769696765829)
                    ·
                      rfl

theorem cell23_4816900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_4816900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816900 prefixEnd_4816900 := by exact prefixLift 4816900
  have htrace : WordTrace (prefixWord ++ tailWord_4816900) baseStart_4816900 baseEnd_4816900 := by
    simpa [prefixWord, tailWord_4816900, baseEnd_4816900] using wordTrace_append hprefix tailTrace_4816900
  have hstable : (prefixWord ++ tailWord_4816900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816900).length < 2 ^ (prefixWord ++ tailWord_4816900).sum := by decide
  have hdescent : baseEnd_4816900 < baseStart_4816900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816906 : List Nat := [3, 1, 2, 2, 4, 1, 1, 4, 1, 1, 3]
def baseStart_4816906 : Nat := 118140960795 + 4816906 * 2 ^ 59
def prefixEnd_4816906 : Nat := 4983230072969 + 3 ^ 40 * 4816906 * 2
def baseEnd_4816906 : Nat := 2473388045526236066822459

theorem tailTrace_4816906 : CollatzResearch.WordTrace tailWord_4816906 prefixEnd_4816906 2473388045526236066822459 := by
  unfold tailWord_4816906
  simp only [CollatzResearch.WordTrace]
  refine ⟨43921748771794924723609643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117124663391453132596292381 43921748771794924723609643)
  ·
    refine ⟨65882623157692387085414465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43921748771794924723609643 65882623157692387085414465)
    ·
      refine ⟨49411967368269290314060849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65882623157692387085414465 49411967368269290314060849)
      ·
        refine ⟨37058975526201967735545637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49411967368269290314060849 37058975526201967735545637)
        ·
          refine ⟨6948557911162868950414807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37058975526201967735545637 6948557911162868950414807)
          ·
            refine ⟨10422836866744303425622211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6948557911162868950414807 10422836866744303425622211)
            ·
              refine ⟨15634255300116455138433317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10422836866744303425622211 15634255300116455138433317)
              ·
                refine ⟨2931422868771835338456247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15634255300116455138433317 2931422868771835338456247)
                ·
                  refine ⟨4397134303157753007684371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2931422868771835338456247 4397134303157753007684371)
                  ·
                    refine ⟨6595701454736629511526557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4397134303157753007684371 6595701454736629511526557)
                    ·
                      refine ⟨2473388045526236066822459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6595701454736629511526557 2473388045526236066822459)
                      ·
                        rfl

theorem cell23_4816906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_4816906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816906 prefixEnd_4816906 := by exact prefixLift 4816906
  have htrace : WordTrace (prefixWord ++ tailWord_4816906) baseStart_4816906 baseEnd_4816906 := by
    simpa [prefixWord, tailWord_4816906, baseEnd_4816906] using wordTrace_append hprefix tailTrace_4816906
  have hstable : (prefixWord ++ tailWord_4816906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816906).length < 2 ^ (prefixWord ++ tailWord_4816906).sum := by decide
  have hdescent : baseEnd_4816906 < baseStart_4816906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816915 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 3]
def baseStart_4816915 : Nat := 118140960795 + 4816915 * 2 ^ 59
def prefixEnd_4816915 : Nat := 4983230072969 + 3 ^ 40 * 4816915 * 2
def baseEnd_4816915 : Nat := 2473392666852126531609917

theorem tailTrace_4816915 : CollatzResearch.WordTrace tailWord_4816915 prefixEnd_4816915 2473392666852126531609917 := by
  unfold tailWord_4816915
  simp only [CollatzResearch.WordTrace]
  refine ⟨175687323344147093431516199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117124882229431395621010799 175687323344147093431516199)
  ·
    refine ⟨263530985016220640147274299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175687323344147093431516199 263530985016220640147274299)
    ·
      refine ⟨395296477524330960220911449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263530985016220640147274299 395296477524330960220911449)
      ·
        refine ⟨296472358143248220165683587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395296477524330960220911449 296472358143248220165683587)
        ·
          refine ⟨444708537214872330248525381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296472358143248220165683587 444708537214872330248525381)
          ·
            refine ⟨83382850727788561921598509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 444708537214872330248525381 83382850727788561921598509)
            ·
              refine ⟨31268569022920710720599441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83382850727788561921598509 31268569022920710720599441)
              ·
                refine ⟨23451426767190533040449581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31268569022920710720599441 23451426767190533040449581)
                ·
                  refine ⟨8794285037696449890168593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23451426767190533040449581 8794285037696449890168593)
                  ·
                    refine ⟨6595713778272337417626445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8794285037696449890168593 6595713778272337417626445)
                    ·
                      refine ⟨2473392666852126531609917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6595713778272337417626445 2473392666852126531609917)
                      ·
                        rfl

theorem cell23_4816915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 3].length) (baseStart_4816915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816915 prefixEnd_4816915 := by exact prefixLift 4816915
  have htrace : WordTrace (prefixWord ++ tailWord_4816915) baseStart_4816915 baseEnd_4816915 := by
    simpa [prefixWord, tailWord_4816915, baseEnd_4816915] using wordTrace_append hprefix tailTrace_4816915
  have hstable : (prefixWord ++ tailWord_4816915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816915).length < 2 ^ (prefixWord ++ tailWord_4816915).sum := by decide
  have hdescent : baseEnd_4816915 < baseStart_4816915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816922 : List Nat := [3, 1, 1, 3, 1, 3, 2, 3, 2, 4]
def baseStart_4816922 : Nat := 118140960795 + 4816922 * 2 ^ 59
def prefixEnd_4816922 : Nat := 4983230072969 + 3 ^ 40 * 4816922 * 2
def baseEnd_4816922 : Nat := 824465420405569334740795

theorem tailTrace_4816922 : CollatzResearch.WordTrace tailWord_4816922 prefixEnd_4816922 824465420405569334740795 := by
  unfold tailWord_4816922
  simp only [CollatzResearch.WordTrace]
  refine ⟨43921894663780433406755255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117125052436747822418014013 43921894663780433406755255)
  ·
    refine ⟨65882841995670650110132883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43921894663780433406755255 65882841995670650110132883)
    ·
      refine ⟨98824262993505975165199325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65882841995670650110132883 98824262993505975165199325)
      ·
        refine ⟨37059098622564740686949747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98824262993505975165199325 37059098622564740686949747)
        ·
          refine ⟨55588647933847111030424621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37059098622564740686949747 55588647933847111030424621)
          ·
            refine ⟨20845742975192666636409233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55588647933847111030424621 20845742975192666636409233)
            ·
              refine ⟨15634307231394499977306925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20845742975192666636409233 15634307231394499977306925)
              ·
                refine ⟨5862865211772937491490097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15634307231394499977306925 5862865211772937491490097)
                ·
                  refine ⟨4397148908829703118617573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5862865211772937491490097 4397148908829703118617573)
                  ·
                    refine ⟨824465420405569334740795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4397148908829703118617573 824465420405569334740795)
                    ·
                      rfl

theorem cell23_4816922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_4816922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816922 prefixEnd_4816922 := by exact prefixLift 4816922
  have htrace : WordTrace (prefixWord ++ tailWord_4816922) baseStart_4816922 baseEnd_4816922 := by
    simpa [prefixWord, tailWord_4816922, baseEnd_4816922] using wordTrace_append hprefix tailTrace_4816922
  have hstable : (prefixWord ++ tailWord_4816922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816922).length < 2 ^ (prefixWord ++ tailWord_4816922).sum := by decide
  have hdescent : baseEnd_4816922 < baseStart_4816922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816942 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_4816942 : Nat := 118140960795 + 4816942 * 2 ^ 59
def prefixEnd_4816942 : Nat := 4983230072969 + 3 ^ 40 * 4816942 * 2
def baseEnd_4816942 : Nat := 2473406530829797925972293

theorem tailTrace_4816942 : CollatzResearch.WordTrace tailWord_4816942 prefixEnd_4816942 2473406530829797925972293 := by
  unfold tailWord_4816942
  simp only [CollatzResearch.WordTrace]
  refine ⟨21961038514381159630343635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117125538743366184695166053 21961038514381159630343635)
  ·
    refine ⟨32941557771571739445515453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21961038514381159630343635 32941557771571739445515453)
    ·
      refine ⟨12353084164339402292068295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32941557771571739445515453 12353084164339402292068295)
      ·
        refine ⟨18529626246509103438102443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12353084164339402292068295 18529626246509103438102443)
        ·
          refine ⟨27794439369763655157153665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18529626246509103438102443 27794439369763655157153665)
          ·
            refine ⟨20845829527322741367865249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27794439369763655157153665 20845829527322741367865249)
            ·
              refine ⟨15634372145492056025898937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20845829527322741367865249 15634372145492056025898937)
              ·
                refine ⟨11725779109119042019424203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15634372145492056025898937 11725779109119042019424203)
                ·
                  refine ⟨17588668663678563029136305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11725779109119042019424203 17588668663678563029136305)
                  ·
                    refine ⟨13191501497758922271852229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17588668663678563029136305 13191501497758922271852229)
                    ·
                      refine ⟨2473406530829797925972293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13191501497758922271852229 2473406530829797925972293)
                      ·
                        rfl

theorem cell23_4816942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_4816942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816942 prefixEnd_4816942 := by exact prefixLift 4816942
  have htrace : WordTrace (prefixWord ++ tailWord_4816942) baseStart_4816942 baseEnd_4816942 := by
    simpa [prefixWord, tailWord_4816942, baseEnd_4816942] using wordTrace_append hprefix tailTrace_4816942
  have hstable : (prefixWord ++ tailWord_4816942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816942).length < 2 ^ (prefixWord ++ tailWord_4816942).sum := by decide
  have hdescent : baseEnd_4816942 < baseStart_4816942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816946 : List Nat := [3, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2]
def baseStart_4816946 : Nat := 118140960795 + 4816946 * 2 ^ 59
def prefixEnd_4816946 : Nat := 4983230072969 + 3 ^ 40 * 4816946 * 2
def baseEnd_4816946 : Nat := 2473408584752415910322275

theorem tailTrace_4816946 : CollatzResearch.WordTrace tailWord_4816946 prefixEnd_4816946 2473408584752415910322275 := by
  unfold tailWord_4816946
  simp only [CollatzResearch.WordTrace]
  refine ⟨43922113501758696431473673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117125636004689857150596461 43922113501758696431473673)
  ·
    refine ⟨32941585126319022323605255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43922113501758696431473673 32941585126319022323605255)
    ·
      refine ⟨49412377689478533485407883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32941585126319022323605255 49412377689478533485407883)
      ·
        refine ⟨74118566534217800228111825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49412377689478533485407883 74118566534217800228111825)
        ·
          refine ⟨55588924900663350171083869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74118566534217800228111825 55588924900663350171083869)
          ·
            refine ⟨20845846837748756314156451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55588924900663350171083869 20845846837748756314156451)
            ·
              refine ⟨31268770256623134471234677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20845846837748756314156451 31268770256623134471234677)
              ·
                refine ⟨2931447211558418856678251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31268770256623134471234677 2931447211558418856678251)
                ·
                  refine ⟨4397170817337628285017377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2931447211558418856678251 4397170817337628285017377)
                  ·
                    refine ⟨3297878113003221213763033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4397170817337628285017377 3297878113003221213763033)
                    ·
                      refine ⟨2473408584752415910322275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3297878113003221213763033 2473408584752415910322275)
                      ·
                        rfl

theorem cell23_4816946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_4816946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816946 prefixEnd_4816946 := by exact prefixLift 4816946
  have htrace : WordTrace (prefixWord ++ tailWord_4816946) baseStart_4816946 baseEnd_4816946 := by
    simpa [prefixWord, tailWord_4816946, baseEnd_4816946] using wordTrace_append hprefix tailTrace_4816946
  have hstable : (prefixWord ++ tailWord_4816946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816946).length < 2 ^ (prefixWord ++ tailWord_4816946).sum := by decide
  have hdescent : baseEnd_4816946 < baseStart_4816946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816949 : List Nat := [1, 3, 3, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_4816949 : Nat := 118140960795 + 4816949 * 2 ^ 59
def prefixEnd_4816949 : Nat := 4983230072969 + 3 ^ 40 * 4816949 * 2
def baseEnd_4816949 : Nat := 2473410125194379398584761

theorem tailTrace_4816949 : CollatzResearch.WordTrace tailWord_4816949 prefixEnd_4816949 2473410125194379398584761 := by
  unfold tailWord_4816949
  simp only [CollatzResearch.WordTrace]
  refine ⟨175688563426023917238253901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117125708950682611492169267 175688563426023917238253901)
  ·
    refine ⟨65883211284758968964345213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175688563426023917238253901 65883211284758968964345213)
    ·
      refine ⟨24706204231784613361629455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65883211284758968964345213 24706204231784613361629455)
      ·
        refine ⟨37059306347676920042444183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24706204231784613361629455 37059306347676920042444183)
        ·
          refine ⟨55588959521515380063666275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37059306347676920042444183 55588959521515380063666275)
          ·
            refine ⟨83383439282273070095499413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55588959521515380063666275 83383439282273070095499413)
            ·
              refine ⟨3908598716356550160726535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83383439282273070095499413 3908598716356550160726535)
              ·
                refine ⟨5862898074534825241089803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3908598716356550160726535 5862898074534825241089803)
                ·
                  refine ⟨8794347111802237861634705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5862898074534825241089803 8794347111802237861634705)
                  ·
                    refine ⟨6595760333851678396226029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8794347111802237861634705 6595760333851678396226029)
                    ·
                      refine ⟨2473410125194379398584761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6595760333851678396226029 2473410125194379398584761)
                      ·
                        rfl

theorem cell23_4816949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_4816949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816949 prefixEnd_4816949 := by exact prefixLift 4816949
  have htrace : WordTrace (prefixWord ++ tailWord_4816949) baseStart_4816949 baseEnd_4816949 := by
    simpa [prefixWord, tailWord_4816949, baseEnd_4816949] using wordTrace_append hprefix tailTrace_4816949
  have hstable : (prefixWord ++ tailWord_4816949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816949).length < 2 ^ (prefixWord ++ tailWord_4816949).sum := by decide
  have hdescent : baseEnd_4816949 < baseStart_4816949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4816972 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 5, 3, 2]
def baseStart_4816972 : Nat := 118140960795 + 4816972 * 2 ^ 59
def prefixEnd_4816972 : Nat := 4983230072969 + 3 ^ 40 * 4816972 * 2
def baseEnd_4816972 : Nat := 2473421935249432808597155

theorem tailTrace_4816972 : CollatzResearch.WordTrace tailWord_4816972 prefixEnd_4816972 2473421935249432808597155 := by
  unfold tailWord_4816972
  simp only [CollatzResearch.WordTrace]
  refine ⟨87844701152470296083170585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117126268203293728110894113 87844701152470296083170585)
  ·
    refine ⟨65883525864352722062377939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87844701152470296083170585 65883525864352722062377939)
    ·
      refine ⟨98825288796529083093566909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65883525864352722062377939 98825288796529083093566909)
      ·
        refine ⟨37059483298698406160087591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98825288796529083093566909 37059483298698406160087591)
        ·
          refine ⟨55589224948047609240131387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37059483298698406160087591 55589224948047609240131387)
          ·
            refine ⟨83383837422071413860197081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55589224948047609240131387 83383837422071413860197081)
            ·
              refine ⟨62537878066553560395147811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83383837422071413860197081 62537878066553560395147811)
              ·
                refine ⟨93806817099830340592721717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62537878066553560395147811 93806817099830340592721717)
                ·
                  refine ⟨8794389103109094430567661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93806817099830340592721717 8794389103109094430567661)
                  ·
                    refine ⟨3297895913665910411462873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8794389103109094430567661 3297895913665910411462873)
                    ·
                      refine ⟨2473421935249432808597155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3297895913665910411462873 2473421935249432808597155)
                      ·
                        rfl

theorem cell23_4816972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_4816972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4816972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4816972 prefixEnd_4816972 := by exact prefixLift 4816972
  have htrace : WordTrace (prefixWord ++ tailWord_4816972) baseStart_4816972 baseEnd_4816972 := by
    simpa [prefixWord, tailWord_4816972, baseEnd_4816972] using wordTrace_append hprefix tailTrace_4816972
  have hstable : (prefixWord ++ tailWord_4816972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4816972).length < 2 ^ (prefixWord ++ tailWord_4816972).sum := by decide
  have hdescent : baseEnd_4816972 < baseStart_4816972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4816972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817075 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 4]
def baseStart_4817075 : Nat := 118140960795 + 4817075 * 2 ^ 59
def prefixEnd_4817075 : Nat := 4983230072969 + 3 ^ 40 * 4817075 * 2
def baseEnd_4817075 : Nat := 2473474823756845905609181

theorem tailTrace_4817075 : CollatzResearch.WordTrace tailWord_4817075 prefixEnd_4817075 2473474823756845905609181 := by
  unfold tailWord_4817075
  simp only [CollatzResearch.WordTrace]
  refine ⟨175693159023567440757340679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117128772682378293838227119 175693159023567440757340679)
  ·
    refine ⟨263539738535351161136011019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175693159023567440757340679 263539738535351161136011019)
    ·
      refine ⟨395309607803026741704016529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263539738535351161136011019 395309607803026741704016529)
      ·
        refine ⟨296482205852270056278012397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395309607803026741704016529 296482205852270056278012397)
        ·
          refine ⟨111180827194601271104254649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296482205852270056278012397 111180827194601271104254649)
          ·
            refine ⟨83385620395950953328190987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111180827194601271104254649 83385620395950953328190987)
            ·
              refine ⟨125078430593926429992286481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83385620395950953328190987 125078430593926429992286481)
              ·
                refine ⟨93808822945444822494214861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125078430593926429992286481 93808822945444822494214861)
                ·
                  refine ⟨35178308604541808435330573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93808822945444822494214861 35178308604541808435330573)
                  ·
                    refine ⟨13191865726703178163248965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35178308604541808435330573 13191865726703178163248965)
                    ·
                      refine ⟨2473474823756845905609181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13191865726703178163248965 2473474823756845905609181)
                      ·
                        rfl

theorem cell23_4817075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_4817075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817075 prefixEnd_4817075 := by exact prefixLift 4817075
  have htrace : WordTrace (prefixWord ++ tailWord_4817075) baseStart_4817075 baseEnd_4817075 := by
    simpa [prefixWord, tailWord_4817075, baseEnd_4817075] using wordTrace_append hprefix tailTrace_4817075
  have hstable : (prefixWord ++ tailWord_4817075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817075).length < 2 ^ (prefixWord ++ tailWord_4817075).sum := by decide
  have hdescent : baseEnd_4817075 < baseStart_4817075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817085 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_4817085 : Nat := 118140960795 + 4817085 * 2 ^ 59
def prefixEnd_4817085 : Nat := 4983230072969 + 3 ^ 40 * 4817085 * 2
def baseEnd_4817085 : Nat := 824493319521130288828045

theorem tailTrace_4817085 : CollatzResearch.WordTrace tailWord_4817085 prefixEnd_4817085 824493319521130288828045 := by
  unfold tailWord_4817085
  simp only [CollatzResearch.WordTrace]
  refine ⟨175693523753531212465204709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117129015835687474976803139 175693523753531212465204709)
  ·
    refine ⟨32942535703787102337225883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175693523753531212465204709 32942535703787102337225883)
    ·
      refine ⟨49413803555680653505838825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32942535703787102337225883 49413803555680653505838825)
      ·
        refine ⟨37060352666760490129379119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49413803555680653505838825 37060352666760490129379119)
        ·
          refine ⟨55590529000140735194068679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37060352666760490129379119 55590529000140735194068679)
          ·
            refine ⟨83385793500211102791103019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55590529000140735194068679 83385793500211102791103019)
            ·
              refine ⟨125078690250316654186654529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83385793500211102791103019 125078690250316654186654529)
              ·
                refine ⟨93809017687737490639990897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125078690250316654186654529 93809017687737490639990897)
                ·
                  refine ⟨70356763265803117979993173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93809017687737490639990897 70356763265803117979993173)
                  ·
                    refine ⟨824493319521130288828045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70356763265803117979993173 824493319521130288828045)
                    ·
                      rfl

theorem cell23_4817085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_4817085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817085 prefixEnd_4817085 := by exact prefixLift 4817085
  have htrace : WordTrace (prefixWord ++ tailWord_4817085) baseStart_4817085 baseEnd_4817085 := by
    simpa [prefixWord, tailWord_4817085, baseEnd_4817085] using wordTrace_append hprefix tailTrace_4817085
  have hstable : (prefixWord ++ tailWord_4817085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817085).length < 2 ^ (prefixWord ++ tailWord_4817085).sum := by decide
  have hdescent : baseEnd_4817085 < baseStart_4817085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817109 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4817109 : Nat := 118140960795 + 4817109 * 2 ^ 59
def prefixEnd_4817109 : Nat := 4983230072969 + 3 ^ 40 * 4817109 * 2
def baseEnd_4817109 : Nat := 2473492282099098772584025

theorem tailTrace_4817109 : CollatzResearch.WordTrace tailWord_4817109 prefixEnd_4817109 2473492282099098772584025 := by
  unfold tailWord_4817109
  simp only [CollatzResearch.WordTrace]
  refine ⟨175694399105444264564078381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117129599403629509709385587 175694399105444264564078381)
  ·
    refine ⟨65885399664541599211529393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175694399105444264564078381 65885399664541599211529393)
    ·
      refine ⟨49414049748406199408647045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65885399664541599211529393 49414049748406199408647045)
      ·
        refine ⟨9265134327826162389121321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49414049748406199408647045 9265134327826162389121321)
        ·
          refine ⟨6948850745869621791840991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9265134327826162389121321 6948850745869621791840991)
          ·
            refine ⟨10423276118804432687761487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6948850745869621791840991 10423276118804432687761487)
            ·
              refine ⟨15634914178206649031642231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10423276118804432687761487 15634914178206649031642231)
              ·
                refine ⟨23452371267309973547463347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15634914178206649031642231 23452371267309973547463347)
                ·
                  refine ⟨35178556900964960321195021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23452371267309973547463347 35178556900964960321195021)
                  ·
                    refine ⟨13191958837861860120448133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35178556900964960321195021 13191958837861860120448133)
                    ·
                      refine ⟨2473492282099098772584025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13191958837861860120448133 2473492282099098772584025)
                      ·
                        rfl

theorem cell23_4817109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4817109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817109 prefixEnd_4817109 := by exact prefixLift 4817109
  have htrace : WordTrace (prefixWord ++ tailWord_4817109) baseStart_4817109 baseEnd_4817109 := by
    simpa [prefixWord, tailWord_4817109, baseEnd_4817109] using wordTrace_append hprefix tailTrace_4817109
  have hstable : (prefixWord ++ tailWord_4817109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817109).length < 2 ^ (prefixWord ++ tailWord_4817109).sum := by decide
  have hdescent : baseEnd_4817109 < baseStart_4817109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817145 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 2, 9]
def baseStart_4817145 : Nat := 118140960795 + 4817145 * 2 ^ 59
def prefixEnd_4817145 : Nat := 4983230072969 + 3 ^ 40 * 4817145 * 2
def baseEnd_4817145 : Nat := 824503589134220210577953

theorem tailTrace_4817145 : CollatzResearch.WordTrace tailWord_4817145 prefixEnd_4817145 824503589134220210577953 := by
  unfold tailWord_4817145
  simp only [CollatzResearch.WordTrace]
  refine ⟨175695712133313842712388889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117130474755542561808259259 175695712133313842712388889)
  ·
    refine ⟨131771784099985382034291667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175695712133313842712388889 131771784099985382034291667)
    ·
      refine ⟨197657676149978073051437501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131771784099985382034291667 197657676149978073051437501)
      ·
        refine ⟨74121628556241777394289063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197657676149978073051437501 74121628556241777394289063)
        ·
          refine ⟨111182442834362666091433595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74121628556241777394289063 111182442834362666091433595)
          ·
            refine ⟨166773664251543999137150393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111182442834362666091433595 166773664251543999137150393)
            ·
              refine ⟨125080248188657999352862795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166773664251543999137150393 125080248188657999352862795)
              ·
                refine ⟨187620372282986999029294193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125080248188657999352862795 187620372282986999029294193)
                ·
                  refine ⟨140715279212240249271970645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187620372282986999029294193 140715279212240249271970645)
                  ·
                    refine ⟨824503589134220210577953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 140715279212240249271970645 824503589134220210577953)
                    ·
                      rfl

theorem cell23_4817145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_4817145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817145 prefixEnd_4817145 := by exact prefixLift 4817145
  have htrace : WordTrace (prefixWord ++ tailWord_4817145) baseStart_4817145 baseEnd_4817145 := by
    simpa [prefixWord, tailWord_4817145, baseEnd_4817145] using wordTrace_append hprefix tailTrace_4817145
  have hstable : (prefixWord ++ tailWord_4817145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817145).length < 2 ^ (prefixWord ++ tailWord_4817145).sum := by decide
  have hdescent : baseEnd_4817145 < baseStart_4817145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817162 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 3, 5]
def baseStart_4817162 : Nat := 118140960795 + 4817162 * 2 ^ 59
def prefixEnd_4817162 : Nat := 4983230072969 + 3 ^ 40 * 4817162 * 2
def baseEnd_4817162 : Nat := 824506498857929021740427

theorem tailTrace_4817162 : CollatzResearch.WordTrace tailWord_4817162 prefixEnd_4817162 824506498857929021740427 := by
  unfold tailWord_4817162
  simp only [CollatzResearch.WordTrace]
  refine ⟨43924083043563063653939435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117130888116168169743838493 43924083043563063653939435)
  ·
    refine ⟨65886124565344595480909153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43924083043563063653939435 65886124565344595480909153)
    ·
      refine ⟨49414593424008446610681865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65886124565344595480909153 49414593424008446610681865)
      ·
        refine ⟨37060945068006334958011399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49414593424008446610681865 37060945068006334958011399)
        ·
          refine ⟨55591417602009502437017099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37060945068006334958011399 55591417602009502437017099)
          ·
            refine ⟨83387126403014253655525649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55591417602009502437017099 83387126403014253655525649)
            ·
              refine ⟨62540344802260690241644237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83387126403014253655525649 62540344802260690241644237)
              ·
                refine ⟨23452629300847758840616589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62540344802260690241644237 23452629300847758840616589)
                ·
                  refine ⟨8794735987817909565231221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23452629300847758840616589 8794735987817909565231221)
                  ·
                    refine ⟨824506498857929021740427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8794735987817909565231221 824506498857929021740427)
                    ·
                      rfl

theorem cell23_4817162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_4817162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817162 prefixEnd_4817162 := by exact prefixLift 4817162
  have htrace : WordTrace (prefixWord ++ tailWord_4817162) baseStart_4817162 baseEnd_4817162 := by
    simpa [prefixWord, tailWord_4817162, baseEnd_4817162] using wordTrace_append hprefix tailTrace_4817162
  have hstable : (prefixWord ++ tailWord_4817162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817162).length < 2 ^ (prefixWord ++ tailWord_4817162).sum := by decide
  have hdescent : baseEnd_4817162 < baseStart_4817162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817169 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 1, 5, 2]
def baseStart_4817169 : Nat := 118140960795 + 4817169 * 2 ^ 59
def prefixEnd_4817169 : Nat := 4983230072969 + 3 ^ 40 * 4817169 * 2
def baseEnd_4817169 : Nat := 2473523090938368537833749

theorem tailTrace_4817169 : CollatzResearch.WordTrace tailWord_4817169 prefixEnd_4817169 2473523090938368537833749 := by
  unfold tailWord_4817169
  simp only [CollatzResearch.WordTrace]
  refine ⟨175696587485226894811262561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117131058323484596540841707 175696587485226894811262561)
  ·
    refine ⟨131772440613920171108446921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175696587485226894811262561 131772440613920171108446921)
    ·
      refine ⟨98829330460440128331335191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131772440613920171108446921 98829330460440128331335191)
      ·
        refine ⟨148243995690660192497002787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98829330460440128331335191 148243995690660192497002787)
        ·
          refine ⟨222365993535990288745504181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148243995690660192497002787 222365993535990288745504181)
          ·
            refine ⟨20846811893999089569891017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 222365993535990288745504181 20846811893999089569891017)
            ·
              refine ⟨15635108920499317177418263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20846811893999089569891017 15635108920499317177418263)
              ·
                refine ⟨23452663380748975766127395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15635108920499317177418263 23452663380748975766127395)
                ·
                  refine ⟨35178995071123463649191093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23452663380748975766127395 35178995071123463649191093)
                  ·
                    refine ⟨3298030787917824717111665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35178995071123463649191093 3298030787917824717111665)
                    ·
                      refine ⟨2473523090938368537833749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298030787917824717111665 2473523090938368537833749)
                      ·
                        rfl

theorem cell23_4817169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 5, 2].length) (baseStart_4817169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817169 prefixEnd_4817169 := by exact prefixLift 4817169
  have htrace : WordTrace (prefixWord ++ tailWord_4817169) baseStart_4817169 baseEnd_4817169 := by
    simpa [prefixWord, tailWord_4817169, baseEnd_4817169] using wordTrace_append hprefix tailTrace_4817169
  have hstable : (prefixWord ++ tailWord_4817169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817169).length < 2 ^ (prefixWord ++ tailWord_4817169).sum := by decide
  have hdescent : baseEnd_4817169 < baseStart_4817169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817186 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_4817186 : Nat := 118140960795 + 4817186 * 2 ^ 59
def prefixEnd_4817186 : Nat := 4983230072969 + 3 ^ 40 * 4817186 * 2
def baseEnd_4817186 : Nat := 2473531820109494971321171

theorem tailTrace_4817186 : CollatzResearch.WordTrace tailWord_4817186 prefixEnd_4817186 2473531820109494971321171 := by
  unfold tailWord_4817186
  simp only [CollatzResearch.WordTrace]
  refine ⟨43924301881541326678657853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117131471684110204476420941 43924301881541326678657853)
  ·
    refine ⟨16471613205577997504496695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43924301881541326678657853 16471613205577997504496695)
    ·
      refine ⟨24707419808366996256745043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16471613205577997504496695 24707419808366996256745043)
      ·
        refine ⟨37061129712550494385117565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24707419808366996256745043 37061129712550494385117565)
        ·
          refine ⟨13897923642206435394419087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37061129712550494385117565 13897923642206435394419087)
          ·
            refine ⟨20846885463309653091628631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13897923642206435394419087 20846885463309653091628631)
            ·
              refine ⟨31270328194964479637442947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20846885463309653091628631 31270328194964479637442947)
              ·
                refine ⟨46905492292446719456164421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31270328194964479637442947 46905492292446719456164421)
                ·
                  refine ⟨8794779804833759898030829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46905492292446719456164421 8794779804833759898030829)
                  ·
                    refine ⟨3298042426812659961761561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8794779804833759898030829 3298042426812659961761561)
                    ·
                      refine ⟨2473531820109494971321171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298042426812659961761561 2473531820109494971321171)
                      ·
                        rfl

theorem cell23_4817186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_4817186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817186 prefixEnd_4817186 := by exact prefixLift 4817186
  have htrace : WordTrace (prefixWord ++ tailWord_4817186) baseStart_4817186 baseEnd_4817186 := by
    simpa [prefixWord, tailWord_4817186, baseEnd_4817186] using wordTrace_append hprefix tailTrace_4817186
  have hstable : (prefixWord ++ tailWord_4817186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817186).length < 2 ^ (prefixWord ++ tailWord_4817186).sum := by decide
  have hdescent : baseEnd_4817186 < baseStart_4817186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817212 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_4817212 : Nat := 118140960795 + 4817212 * 2 ^ 59
def prefixEnd_4817212 : Nat := 4983230072969 + 3 ^ 40 * 4817212 * 2
def baseEnd_4817212 : Nat := 2473545170606511869596051

theorem tailTrace_4817212 : CollatzResearch.WordTrace tailWord_4817212 prefixEnd_4817212 2473545170606511869596051 := by
  unfold tailWord_4817212
  simp only [CollatzResearch.WordTrace]
  refine ⟨87849077912035556577538945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117132103882714075436718593 87849077912035556577538945)
  ·
    refine ⟨65886808434026667433154209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87849077912035556577538945 65886808434026667433154209)
    ·
      refine ⟨49415106325520000574865657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65886808434026667433154209 49415106325520000574865657)
      ·
        refine ⟨37061329744140000431149243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49415106325520000574865657 37061329744140000431149243)
        ·
          refine ⟨55591994616210000646723865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37061329744140000431149243 55591994616210000646723865)
          ·
            refine ⟨41693995962157500485042899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55591994616210000646723865 41693995962157500485042899)
            ·
              refine ⟨62540993943236250727564349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41693995962157500485042899 62540993943236250727564349)
              ·
                refine ⟨23452872728713594022836631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62540993943236250727564349 23452872728713594022836631)
                ·
                  refine ⟨35179309093070391034254947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23452872728713594022836631 35179309093070391034254947)
                  ·
                    refine ⟨52768963639605586551382421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35179309093070391034254947 52768963639605586551382421)
                    ·
                      refine ⟨2473545170606511869596051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52768963639605586551382421 2473545170606511869596051)
                      ·
                        rfl

theorem cell23_4817212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_4817212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817212 prefixEnd_4817212 := by exact prefixLift 4817212
  have htrace : WordTrace (prefixWord ++ tailWord_4817212) baseStart_4817212 baseEnd_4817212 := by
    simpa [prefixWord, tailWord_4817212, baseEnd_4817212] using wordTrace_append hprefix tailTrace_4817212
  have hstable : (prefixWord ++ tailWord_4817212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817212).length < 2 ^ (prefixWord ++ tailWord_4817212).sum := by decide
  have hdescent : baseEnd_4817212 < baseStart_4817212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817220 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_4817220 : Nat := 118140960795 + 4817220 * 2 ^ 59
def prefixEnd_4817220 : Nat := 4983230072969 + 3 ^ 40 * 4817220 * 2
def baseEnd_4817220 : Nat := 2473549278451747838296015

theorem tailTrace_4817220 : CollatzResearch.WordTrace tailWord_4817220 prefixEnd_4817220 2473549278451747838296015 := by
  unfold tailWord_4817220
  simp only [CollatzResearch.WordTrace]
  refine ⟨87849223804021065260684557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117132298405361420347579409 87849223804021065260684557)
  ·
    refine ⟨32943458926507899472756709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87849223804021065260684557 32943458926507899472756709)
    ·
      refine ⟨6176898548720231151141883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32943458926507899472756709 6176898548720231151141883)
      ·
        refine ⟨9265347823080346726712825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6176898548720231151141883 9265347823080346726712825)
        ·
          refine ⟨6949010867310260045034619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9265347823080346726712825 6949010867310260045034619)
          ·
            refine ⟨10423516300965390067551929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6949010867310260045034619 10423516300965390067551929)
            ·
              refine ⟨7817637225724042550663947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10423516300965390067551929 7817637225724042550663947)
              ·
                refine ⟨11726455838586063825995921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7817637225724042550663947 11726455838586063825995921)
                ·
                  refine ⟨8794841878939547869496941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11726455838586063825995921 8794841878939547869496941)
                  ·
                    refine ⟨3298065704602330451061353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8794841878939547869496941 3298065704602330451061353)
                    ·
                      refine ⟨2473549278451747838296015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298065704602330451061353 2473549278451747838296015)
                      ·
                        rfl

theorem cell23_4817220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_4817220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817220 prefixEnd_4817220 := by exact prefixLift 4817220
  have htrace : WordTrace (prefixWord ++ tailWord_4817220) baseStart_4817220 baseEnd_4817220 := by
    simpa [prefixWord, tailWord_4817220, baseEnd_4817220] using wordTrace_append hprefix tailTrace_4817220
  have hstable : (prefixWord ++ tailWord_4817220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817220).length < 2 ^ (prefixWord ++ tailWord_4817220).sum := by decide
  have hdescent : baseEnd_4817220 < baseStart_4817220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817236 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_4817236 : Nat := 118140960795 + 4817236 * 2 ^ 59
def prefixEnd_4817236 : Nat := 4983230072969 + 3 ^ 40 * 4817236 * 2
def baseEnd_4817236 : Nat := 2473557494142219775695941

theorem tailTrace_4817236 : CollatzResearch.WordTrace tailWord_4817236 prefixEnd_4817236 2473557494142219775695941 := by
  unfold tailWord_4817236
  simp only [CollatzResearch.WordTrace]
  refine ⟨87849515587992082626975781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117132687450656110169301041 87849515587992082626975781)
  ·
    refine ⟨16471784172748515492557959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87849515587992082626975781 16471784172748515492557959)
    ·
      refine ⟨24707676259122773238836939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16471784172748515492557959 24707676259122773238836939)
      ·
        refine ⟨37061514388684159858255409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24707676259122773238836939 37061514388684159858255409)
        ·
          refine ⟨27796135791513119893691557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37061514388684159858255409 27796135791513119893691557)
          ·
            refine ⟨5211775460908709980067167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27796135791513119893691557 5211775460908709980067167)
            ·
              refine ⟨7817663191363064970100751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5211775460908709980067167 7817663191363064970100751)
              ·
                refine ⟨11726494787044597455151127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7817663191363064970100751 11726494787044597455151127)
                ·
                  refine ⟨17589742180566896182726691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11726494787044597455151127 17589742180566896182726691)
                  ·
                    refine ⟨26384613270850344274090037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17589742180566896182726691 26384613270850344274090037)
                    ·
                      refine ⟨2473557494142219775695941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26384613270850344274090037 2473557494142219775695941)
                      ·
                        rfl

theorem cell23_4817236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_4817236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817236 prefixEnd_4817236 := by exact prefixLift 4817236
  have htrace : WordTrace (prefixWord ++ tailWord_4817236) baseStart_4817236 baseEnd_4817236 := by
    simpa [prefixWord, tailWord_4817236, baseEnd_4817236] using wordTrace_append hprefix tailTrace_4817236
  have hstable : (prefixWord ++ tailWord_4817236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817236).length < 2 ^ (prefixWord ++ tailWord_4817236).sum := by decide
  have hdescent : baseEnd_4817236 < baseStart_4817236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817244 : List Nat := [2, 2, 4, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4817244 : Nat := 118140960795 + 4817244 * 2 ^ 59
def prefixEnd_4817244 : Nat := 4983230072969 + 3 ^ 40 * 4817244 * 2
def baseEnd_4817244 : Nat := 2473561601987455744395905

theorem tailTrace_4817244 : CollatzResearch.WordTrace tailWord_4817244 prefixEnd_4817244 2473561601987455744395905 := by
  unfold tailWord_4817244
  simp only [CollatzResearch.WordTrace]
  refine ⟨87849661479977591310121393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117132881973303455080161857 87849661479977591310121393)
  ·
    refine ⟨65887246109983193482591045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87849661479977591310121393 65887246109983193482591045)
    ·
      refine ⟨12353858645621848777985821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65887246109983193482591045 12353858645621848777985821)
      ·
        refine ⟨4632696992108193291744683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12353858645621848777985821 4632696992108193291744683)
        ·
          refine ⟨6949045488162289937617025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4632696992108193291744683 6949045488162289937617025)
          ·
            refine ⟨5211784116121717453212769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6949045488162289937617025 5211784116121717453212769)
            ·
              refine ⟨3908838087091288089909577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5211784116121717453212769 3908838087091288089909577)
              ·
                refine ⟨2931628565318466067432183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3908838087091288089909577 2931628565318466067432183)
                ·
                  refine ⟨4397442847977699101148275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2931628565318466067432183 4397442847977699101148275)
                  ·
                    refine ⟨6596164271966548651722413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4397442847977699101148275 6596164271966548651722413)
                    ·
                      refine ⟨2473561601987455744395905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6596164271966548651722413 2473561601987455744395905)
                      ·
                        rfl

theorem cell23_4817244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4817244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817244 prefixEnd_4817244 := by exact prefixLift 4817244
  have htrace : WordTrace (prefixWord ++ tailWord_4817244) baseStart_4817244 baseEnd_4817244 := by
    simpa [prefixWord, tailWord_4817244, baseEnd_4817244] using wordTrace_append hprefix tailTrace_4817244
  have hstable : (prefixWord ++ tailWord_4817244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817244).length < 2 ^ (prefixWord ++ tailWord_4817244).sum := by decide
  have hdescent : baseEnd_4817244 < baseStart_4817244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817252 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_4817252 : Nat := 118140960795 + 4817252 * 2 ^ 59
def prefixEnd_4817252 : Nat := 4983230072969 + 3 ^ 40 * 4817252 * 2
def baseEnd_4817252 : Nat := 824521903277563904365289

theorem tailTrace_4817252 : CollatzResearch.WordTrace tailWord_4817252 prefixEnd_4817252 824521903277563904365289 := by
  unfold tailWord_4817252
  simp only [CollatzResearch.WordTrace]
  refine ⟨87849807371963099993267005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117133076495950799991022673 87849807371963099993267005)
  ·
    refine ⟨32943677764486162497475127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87849807371963099993267005 32943677764486162497475127)
    ·
      refine ⟨49415516646729243746212691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32943677764486162497475127 49415516646729243746212691)
      ·
        refine ⟨74123274970093865619319037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49415516646729243746212691 74123274970093865619319037)
        ·
          refine ⟨27796228113785199607244639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74123274970093865619319037 27796228113785199607244639)
          ·
            refine ⟨41694342170677799410866959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27796228113785199607244639 41694342170677799410866959)
            ·
              refine ⟨62541513256016699116300439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41694342170677799410866959 62541513256016699116300439)
              ·
                refine ⟨93812269884025048674450659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62541513256016699116300439 93812269884025048674450659)
                ·
                  refine ⟨140718404826037573011675989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93812269884025048674450659 140718404826037573011675989)
                  ·
                    refine ⟨824521903277563904365289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 140718404826037573011675989 824521903277563904365289)
                    ·
                      rfl

theorem cell23_4817252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_4817252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817252 prefixEnd_4817252 := by exact prefixLift 4817252
  have htrace : WordTrace (prefixWord ++ tailWord_4817252) baseStart_4817252 baseEnd_4817252 := by
    simpa [prefixWord, tailWord_4817252, baseEnd_4817252] using wordTrace_append hprefix tailTrace_4817252
  have hstable : (prefixWord ++ tailWord_4817252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817252).length < 2 ^ (prefixWord ++ tailWord_4817252).sum := by decide
  have hdescent : baseEnd_4817252 < baseStart_4817252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817266 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_4817266 : Nat := 118140960795 + 4817266 * 2 ^ 59
def prefixEnd_4817266 : Nat := 4983230072969 + 3 ^ 40 * 4817266 * 2
def baseEnd_4817266 : Nat := 2473572898561854658320803

theorem tailTrace_4817266 : CollatzResearch.WordTrace tailWord_4817266 prefixEnd_4817266 2473572898561854658320803 := by
  unfold tailWord_4817266
  simp only [CollatzResearch.WordTrace]
  refine ⟨43925031341468870094385913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117133416910583653585029101 43925031341468870094385913)
  ·
    refine ⟨32943773506101652570789435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43925031341468870094385913 32943773506101652570789435)
    ·
      refine ⟨49415660259152478856184153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32943773506101652570789435 49415660259152478856184153)
      ·
        refine ⟨37061745194364359142138115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49415660259152478856184153 37061745194364359142138115)
        ·
          refine ⟨55592617791546538713207173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37061745194364359142138115 55592617791546538713207173)
          ·
            refine ⟨10423615835914976008726345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55592617791546538713207173 10423615835914976008726345)
            ·
              refine ⟨7817711876936232006544759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10423615835914976008726345 7817711876936232006544759)
              ·
                refine ⟨11726567815404348009817139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7817711876936232006544759 11726567815404348009817139)
                ·
                  refine ⟨17589851723106522014725709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11726567815404348009817139 17589851723106522014725709)
                  ·
                    refine ⟨6596194396164945755522141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17589851723106522014725709 6596194396164945755522141)
                    ·
                      refine ⟨2473572898561854658320803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6596194396164945755522141 2473572898561854658320803)
                      ·
                        rfl

theorem cell23_4817266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_4817266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817266 prefixEnd_4817266 := by exact prefixLift 4817266
  have htrace : WordTrace (prefixWord ++ tailWord_4817266) baseStart_4817266 baseEnd_4817266 := by
    simpa [prefixWord, tailWord_4817266, baseEnd_4817266] using wordTrace_append hprefix tailTrace_4817266
  have hstable : (prefixWord ++ tailWord_4817266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817266).length < 2 ^ (prefixWord ++ tailWord_4817266).sum := by decide
  have hdescent : baseEnd_4817266 < baseStart_4817266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817329 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 7]
def baseStart_4817329 : Nat := 118140960795 + 4817329 * 2 ^ 59
def prefixEnd_4817329 : Nat := 4983230072969 + 3 ^ 40 * 4817329 * 2
def baseEnd_4817329 : Nat := 274845027538120879092557

theorem tailTrace_4817329 : CollatzResearch.WordTrace tailWord_4817329 prefixEnd_4817329 274845027538120879092557 := by
  unfold tailWord_4817329
  simp only [CollatzResearch.WordTrace]
  refine ⟨175702423164647242137087041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117134948776431494758058027 175702423164647242137087041)
  ·
    refine ⟨131776817373485431602815281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175702423164647242137087041 131776817373485431602815281)
    ·
      refine ⟨98832613030114073702111461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131776817373485431602815281 98832613030114073702111461)
      ·
        refine ⟨18531114943146388819145899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98832613030114073702111461 18531114943146388819145899)
        ·
          refine ⟨27796672414719583228718849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18531114943146388819145899 27796672414719583228718849)
          ·
            refine ⟨20847504311039687421539137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27796672414719583228718849 20847504311039687421539137)
            ·
              refine ⟨15635628233279765566154353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20847504311039687421539137 15635628233279765566154353)
              ·
                refine ⟨11726721174959824174615765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15635628233279765566154353 11726721174959824174615765)
                ·
                  refine ⟨274845027538120879092557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11726721174959824174615765 274845027538120879092557)
                  ·
                    rfl

theorem cell23_4817329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 7].length) (baseStart_4817329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817329 prefixEnd_4817329 := by exact prefixLift 4817329
  have htrace : WordTrace (prefixWord ++ tailWord_4817329) baseStart_4817329 baseEnd_4817329 := by
    simpa [prefixWord, tailWord_4817329, baseEnd_4817329] using wordTrace_append hprefix tailTrace_4817329
  have hstable : (prefixWord ++ tailWord_4817329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817329).length < 2 ^ (prefixWord ++ tailWord_4817329).sum := by decide
  have hdescent : baseEnd_4817329 < baseStart_4817329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817369 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 5]
def baseStart_4817369 : Nat := 118140960795 + 4817369 * 2 ^ 59
def prefixEnd_4817369 : Nat := 4983230072969 + 3 ^ 40 * 4817369 * 2
def baseEnd_4817369 : Nat := 2473625787069267755332829

theorem tailTrace_4817369 : CollatzResearch.WordTrace tailWord_4817369 prefixEnd_4817369 2473625787069267755332829 := by
  unfold tailWord_4817369
  simp only [CollatzResearch.WordTrace]
  refine ⟨175703882084502328968543161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117135921389668219312362107 175703882084502328968543161)
  ·
    refine ⟨131777911563376746726407371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175703882084502328968543161 131777911563376746726407371)
    ·
      refine ⟨197666867345065120089611057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131777911563376746726407371 197666867345065120089611057)
      ·
        refine ⟨148250150508798840067208293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197666867345065120089611057 148250150508798840067208293)
        ·
          refine ⟨27796903220399782512601555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148250150508798840067208293 27796903220399782512601555)
          ·
            refine ⟨41695354830599673768902333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27796903220399782512601555 41695354830599673768902333)
            ·
              refine ⟨15635758061474877663338375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41695354830599673768902333 15635758061474877663338375)
              ·
                refine ⟨23453637092212316495007563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15635758061474877663338375 23453637092212316495007563)
                ·
                  refine ⟨35180455638318474742511345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23453637092212316495007563 35180455638318474742511345)
                  ·
                    refine ⟨26385341728738856056883509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35180455638318474742511345 26385341728738856056883509)
                    ·
                      refine ⟨2473625787069267755332829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26385341728738856056883509 2473625787069267755332829)
                      ·
                        rfl

theorem cell23_4817369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_4817369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817369 prefixEnd_4817369 := by exact prefixLift 4817369
  have htrace : WordTrace (prefixWord ++ tailWord_4817369) baseStart_4817369 baseEnd_4817369 := by
    simpa [prefixWord, tailWord_4817369, baseEnd_4817369] using wordTrace_append hprefix tailTrace_4817369
  have hstable : (prefixWord ++ tailWord_4817369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817369).length < 2 ^ (prefixWord ++ tailWord_4817369).sum := by decide
  have hdescent : baseEnd_4817369 < baseStart_4817369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817399 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 3]
def baseStart_4817399 : Nat := 118140960795 + 4817399 * 2 ^ 59
def prefixEnd_4817399 : Nat := 4983230072969 + 3 ^ 40 * 4817399 * 2
def baseEnd_4817399 : Nat := 2473641191488902637957691

theorem tailTrace_4817399 : CollatzResearch.WordTrace tailWord_4817399 prefixEnd_4817399 2473641191488902637957691 := by
  unfold tailWord_4817399
  simp only [CollatzResearch.WordTrace]
  refine ⟨175704976274393644092135251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117136650849595762728090167 175704976274393644092135251)
  ·
    refine ⟨263557464411590466138202877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175704976274393644092135251 263557464411590466138202877)
    ·
      refine ⟨98834049154346424801826079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263557464411590466138202877 98834049154346424801826079)
      ·
        refine ⟨148251073731519637202739119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98834049154346424801826079 148251073731519637202739119)
        ·
          refine ⟨222376610597279455804108679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148251073731519637202739119 222376610597279455804108679)
          ·
            refine ⟨333564915895919183706163019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222376610597279455804108679 333564915895919183706163019)
            ·
              refine ⟨500347373843878775559244529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333564915895919183706163019 500347373843878775559244529)
              ·
                refine ⟨375260530382909081669433397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500347373843878775559244529 375260530382909081669433397)
                ·
                  refine ⟨35180674723397726406509381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 375260530382909081669433397 35180674723397726406509381)
                  ·
                    refine ⟨6596376510637073701220509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35180674723397726406509381 6596376510637073701220509)
                    ·
                      refine ⟨2473641191488902637957691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6596376510637073701220509 2473641191488902637957691)
                      ·
                        rfl

theorem cell23_4817399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_4817399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817399 prefixEnd_4817399 := by exact prefixLift 4817399
  have htrace : WordTrace (prefixWord ++ tailWord_4817399) baseStart_4817399 baseEnd_4817399 := by
    simpa [prefixWord, tailWord_4817399, baseEnd_4817399] using wordTrace_append hprefix tailTrace_4817399
  have hstable : (prefixWord ++ tailWord_4817399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817399).length < 2 ^ (prefixWord ++ tailWord_4817399).sum := by decide
  have hdescent : baseEnd_4817399 < baseStart_4817399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817414 : List Nat := [6, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_4817414 : Nat := 118140960795 + 4817414 * 2 ^ 59
def prefixEnd_4817414 : Nat := 4983230072969 + 3 ^ 40 * 4817414 * 2
def baseEnd_4817414 : Nat := 274849877077635564363347

theorem tailTrace_4817414 : CollatzResearch.WordTrace tailWord_4817414 prefixEnd_4817414 274849877077635564363347 := by
  unfold tailWord_4817414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5490797605291853176685353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 117137015579559534435954197 5490797605291853176685353)
  ·
    refine ⟨4118098203968889882514015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5490797605291853176685353 4118098203968889882514015)
    ·
      refine ⟨6177147305953334823771023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4118098203968889882514015 6177147305953334823771023)
      ·
        refine ⟨9265720958930002235656535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6177147305953334823771023 9265720958930002235656535)
        ·
          refine ⟨13898581438395003353484803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9265720958930002235656535 13898581438395003353484803)
          ·
            refine ⟨20847872157592505030227205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13898581438395003353484803 20847872157592505030227205)
            ·
              refine ⟨3908976029548594693167601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20847872157592505030227205 3908976029548594693167601)
              ·
                refine ⟨2931732022161446019875701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3908976029548594693167601 2931732022161446019875701)
                ·
                  refine ⟨274849877077635564363347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2931732022161446019875701 274849877077635564363347)
                  ·
                    rfl

theorem cell23_4817414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_4817414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817414 prefixEnd_4817414 := by exact prefixLift 4817414
  have htrace : WordTrace (prefixWord ++ tailWord_4817414) baseStart_4817414 baseEnd_4817414 := by
    simpa [prefixWord, tailWord_4817414, baseEnd_4817414] using wordTrace_append hprefix tailTrace_4817414
  have hstable : (prefixWord ++ tailWord_4817414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817414).length < 2 ^ (prefixWord ++ tailWord_4817414).sum := by decide
  have hdescent : baseEnd_4817414 < baseStart_4817414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817436 : List Nat := [2, 2, 3, 1, 2, 2, 2, 3, 6]
def baseStart_4817436 : Nat := 118140960795 + 4817436 * 2 ^ 59
def prefixEnd_4817436 : Nat := 4983230072969 + 3 ^ 40 * 4817436 * 2
def baseEnd_4817436 : Nat := 274851132252568777021669

theorem tailTrace_4817436 : CollatzResearch.WordTrace tailWord_4817436 prefixEnd_4817436 274851132252568777021669 := by
  unfold tailWord_4817436
  simp only [CollatzResearch.WordTrace]
  refine ⟨87853162887629799705616081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117137550516839732940821441 87853162887629799705616081)
  ·
    refine ⟨65889872165722349779212061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87853162887629799705616081 65889872165722349779212061)
    ·
      refine ⟨24708702062145881167204523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65889872165722349779212061 24708702062145881167204523)
      ·
        refine ⟨37063053093218821750806785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24708702062145881167204523 37063053093218821750806785)
        ·
          refine ⟨27797289819914116313105089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37063053093218821750806785 27797289819914116313105089)
          ·
            refine ⟨20847967364935587234828817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27797289819914116313105089 20847967364935587234828817)
            ·
              refine ⟨15635975523701690426121613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20847967364935587234828817 15635975523701690426121613)
              ·
                refine ⟨5863490821388133909795605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15635975523701690426121613 5863490821388133909795605)
                ·
                  refine ⟨274851132252568777021669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5863490821388133909795605 274851132252568777021669)
                  ·
                    rfl

theorem cell23_4817436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_4817436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817436 prefixEnd_4817436 := by exact prefixLift 4817436
  have htrace : WordTrace (prefixWord ++ tailWord_4817436) baseStart_4817436 baseEnd_4817436 := by
    simpa [prefixWord, tailWord_4817436, baseEnd_4817436] using wordTrace_append hprefix tailTrace_4817436
  have hstable : (prefixWord ++ tailWord_4817436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817436).length < 2 ^ (prefixWord ++ tailWord_4817436).sum := by decide
  have hdescent : baseEnd_4817436 < baseStart_4817436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817447 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_4817447 : Nat := 118140960795 + 4817447 * 2 ^ 59
def prefixEnd_4817447 : Nat := 4983230072969 + 3 ^ 40 * 4817447 * 2
def baseEnd_4817447 : Nat := 2473665838560318450157471

theorem tailTrace_4817447 : CollatzResearch.WordTrace tailWord_4817447 prefixEnd_4817447 2473665838560318450157471 := by
  unfold tailWord_4817447
  simp only [CollatzResearch.WordTrace]
  refine ⟨175706726978219748289882595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117137817985479832193255063 175706726978219748289882595)
  ·
    refine ⟨263560090467329622434823893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175706726978219748289882595 263560090467329622434823893)
    ·
      refine ⟨6177189620328038025816185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 263560090467329622434823893 6177189620328038025816185)
      ·
        refine ⟨4632892215246028519362139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6177189620328038025816185 4632892215246028519362139)
        ·
          refine ⟨6949338322869042779043209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4632892215246028519362139 6949338322869042779043209)
          ·
            refine ⟨5212003742151782084282407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6949338322869042779043209 5212003742151782084282407)
            ·
              refine ⟨7818005613227673126423611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5212003742151782084282407 7818005613227673126423611)
              ·
                refine ⟨11727008419841509689635417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7818005613227673126423611 11727008419841509689635417)
                ·
                  refine ⟨8795256314881132267226563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11727008419841509689635417 8795256314881132267226563)
                  ·
                    refine ⟨13192884472321698400839845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8795256314881132267226563 13192884472321698400839845)
                    ·
                      refine ⟨2473665838560318450157471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13192884472321698400839845 2473665838560318450157471)
                      ·
                        rfl

theorem cell23_4817447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_4817447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817447 prefixEnd_4817447 := by exact prefixLift 4817447
  have htrace : WordTrace (prefixWord ++ tailWord_4817447) baseStart_4817447 baseEnd_4817447 := by
    simpa [prefixWord, tailWord_4817447, baseEnd_4817447] using wordTrace_append hprefix tailTrace_4817447
  have hstable : (prefixWord ++ tailWord_4817447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817447).length < 2 ^ (prefixWord ++ tailWord_4817447).sum := by decide
  have hdescent : baseEnd_4817447 < baseStart_4817447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817450 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_4817450 : Nat := 118140960795 + 4817450 * 2 ^ 59
def prefixEnd_4817450 : Nat := 4983230072969 + 3 ^ 40 * 4817450 * 2
def baseEnd_4817450 : Nat := 2473667379002281938419957

theorem tailTrace_4817450 : CollatzResearch.WordTrace tailWord_4817450 prefixEnd_4817450 2473667379002281938419957 := by
  unfold tailWord_4817450
  simp only [CollatzResearch.WordTrace]
  refine ⟨43926709099302219950560451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117137890931472586534827869 43926709099302219950560451)
  ·
    refine ⟨65890063648953329925840677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43926709099302219950560451 65890063648953329925840677)
    ·
      refine ⟨12354386934178749361095127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65890063648953329925840677 12354386934178749361095127)
      ·
        refine ⟨18531580401268124041642691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12354386934178749361095127 18531580401268124041642691)
        ·
          refine ⟨27797370601902186062464037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18531580401268124041642691 27797370601902186062464037)
          ·
            refine ⟨5212006987856659886712007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27797370601902186062464037 5212006987856659886712007)
            ·
              refine ⟨7818010481784989830068011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5212006987856659886712007 7818010481784989830068011)
              ·
                refine ⟨11727015722677484745102017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7818010481784989830068011 11727015722677484745102017)
                ·
                  refine ⟨8795261792008113558826513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11727015722677484745102017 8795261792008113558826513)
                  ·
                    refine ⟨6596446344006085169119885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8795261792008113558826513 6596446344006085169119885)
                    ·
                      refine ⟨2473667379002281938419957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6596446344006085169119885 2473667379002281938419957)
                      ·
                        rfl

theorem cell23_4817450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_4817450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817450 prefixEnd_4817450 := by exact prefixLift 4817450
  have htrace : WordTrace (prefixWord ++ tailWord_4817450) baseStart_4817450 baseEnd_4817450 := by
    simpa [prefixWord, tailWord_4817450, baseEnd_4817450] using wordTrace_append hprefix tailTrace_4817450
  have hstable : (prefixWord ++ tailWord_4817450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817450).length < 2 ^ (prefixWord ++ tailWord_4817450).sum := by decide
  have hdescent : baseEnd_4817450 < baseStart_4817450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817486 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_4817486 : Nat := 118140960795 + 4817486 * 2 ^ 59
def prefixEnd_4817486 : Nat := 4983230072969 + 3 ^ 40 * 4817486 * 2
def baseEnd_4817486 : Nat := 2473685864305843797569791

theorem tailTrace_4817486 : CollatzResearch.WordTrace tailWord_4817486 prefixEnd_4817486 2473685864305843797569791 := by
  unfold tailWord_4817486
  simp only [CollatzResearch.WordTrace]
  refine ⟨21963518678134807243819039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117138766283385638633701541 21963518678134807243819039)
  ·
    refine ⟨32945278017202210865728559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21963518678134807243819039 32945278017202210865728559)
    ·
      refine ⟨49417917025803316298592839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32945278017202210865728559 49417917025803316298592839)
      ·
        refine ⟨74126875538704974447889259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49417917025803316298592839 74126875538704974447889259)
        ·
          refine ⟨111190313308057461671833889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74126875538704974447889259 111190313308057461671833889)
          ·
            refine ⟨83392734981043096253875417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111190313308057461671833889 83392734981043096253875417)
            ·
              refine ⟨62544551235782322190406563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83392734981043096253875417 62544551235782322190406563)
              ·
                refine ⟨93816826853673483285609845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62544551235782322190406563 93816826853673483285609845)
                ·
                  refine ⟨8795327517531889058025923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93816826853673483285609845 8795327517531889058025923)
                  ·
                    refine ⟨13192991276297833587038885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8795327517531889058025923 13192991276297833587038885)
                    ·
                      refine ⟨2473685864305843797569791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13192991276297833587038885 2473685864305843797569791)
                      ·
                        rfl

theorem cell23_4817486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_4817486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817486 prefixEnd_4817486 := by exact prefixLift 4817486
  have htrace : WordTrace (prefixWord ++ tailWord_4817486) baseStart_4817486 baseEnd_4817486 := by
    simpa [prefixWord, tailWord_4817486, baseEnd_4817486] using wordTrace_append hprefix tailTrace_4817486
  have hstable : (prefixWord ++ tailWord_4817486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817486).length < 2 ^ (prefixWord ++ tailWord_4817486).sum := by decide
  have hdescent : baseEnd_4817486 < baseStart_4817486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817496 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 1, 6]
def baseStart_4817496 : Nat := 118140960795 + 4817496 * 2 ^ 59
def prefixEnd_4817496 : Nat := 4983230072969 + 3 ^ 40 * 4817496 * 2
def baseEnd_4817496 : Nat := 824563666370796252814915

theorem tailTrace_4817496 : CollatzResearch.WordTrace tailWord_4817496 prefixEnd_4817496 824563666370796252814915 := by
  unfold tailWord_4817496
  simp only [CollatzResearch.WordTrace]
  refine ⟨87854257077521114829208171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117139009436694819772277561 87854257077521114829208171)
  ·
    refine ⟨131781385616281672243812257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87854257077521114829208171 131781385616281672243812257)
    ·
      refine ⟨98836039212211254182859193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131781385616281672243812257 98836039212211254182859193)
      ·
        refine ⟨74127029409158440637144395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98836039212211254182859193 74127029409158440637144395)
        ·
          refine ⟨111190544113737660955716593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74127029409158440637144395 111190544113737660955716593)
          ·
            refine ⟨83392908085303245716787445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111190544113737660955716593 83392908085303245716787445)
            ·
              refine ⟨7818085132997179285948823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83392908085303245716787445 7818085132997179285948823)
              ·
                refine ⟨11727127699495768928923235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7818085132997179285948823 11727127699495768928923235)
                ·
                  refine ⟨17590691549243653393384853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11727127699495768928923235 17590691549243653393384853)
                  ·
                    refine ⟨824563666370796252814915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17590691549243653393384853 824563666370796252814915)
                    ·
                      rfl

theorem cell23_4817496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_4817496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817496 prefixEnd_4817496 := by exact prefixLift 4817496
  have htrace : WordTrace (prefixWord ++ tailWord_4817496) baseStart_4817496 baseEnd_4817496 := by
    simpa [prefixWord, tailWord_4817496, baseEnd_4817496] using wordTrace_append hprefix tailTrace_4817496
  have hstable : (prefixWord ++ tailWord_4817496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817496).length < 2 ^ (prefixWord ++ tailWord_4817496).sum := by decide
  have hdescent : baseEnd_4817496 < baseStart_4817496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817500 : List Nat := [2, 2, 4, 1, 3, 1, 2, 2, 1, 5]
def baseStart_4817500 : Nat := 118140960795 + 4817500 * 2 ^ 59
def prefixEnd_4817500 : Nat := 4983230072969 + 3 ^ 40 * 4817500 * 2
def baseEnd_4817500 : Nat := 824564351011668914264909

theorem tailTrace_4817500 : CollatzResearch.WordTrace tailWord_4817500 prefixEnd_4817500 824564351011668914264909 := by
  unfold tailWord_4817500
  simp only [CollatzResearch.WordTrace]
  refine ⟨87854330023513869170780977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117139106698018492227707969 87854330023513869170780977)
  ·
    refine ⟨65890747517635401878085733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87854330023513869170780977 65890747517635401878085733)
    ·
      refine ⟨12354515159556637852141075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65890747517635401878085733 12354515159556637852141075)
      ·
        refine ⟨18531772739334956778211613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12354515159556637852141075 18531772739334956778211613)
        ·
          refine ⟨6949414777250608791829355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18531772739334956778211613 6949414777250608791829355)
          ·
            refine ⟨10424122165875913187744033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6949414777250608791829355 10424122165875913187744033)
            ·
              refine ⟨7818091624406934890808025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10424122165875913187744033 7818091624406934890808025)
              ·
                refine ⟨5863568718305201168106019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7818091624406934890808025 5863568718305201168106019)
                ·
                  refine ⟨8795353077457801752159029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5863568718305201168106019 8795353077457801752159029)
                  ·
                    refine ⟨824564351011668914264909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8795353077457801752159029 824564351011668914264909)
                    ·
                      rfl

theorem cell23_4817500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_4817500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817500 prefixEnd_4817500 := by exact prefixLift 4817500
  have htrace : WordTrace (prefixWord ++ tailWord_4817500) baseStart_4817500 baseEnd_4817500 := by
    simpa [prefixWord, tailWord_4817500, baseEnd_4817500] using wordTrace_append hprefix tailTrace_4817500
  have hstable : (prefixWord ++ tailWord_4817500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817500).length < 2 ^ (prefixWord ++ tailWord_4817500).sum := by decide
  have hdescent : baseEnd_4817500 < baseStart_4817500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817516 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_4817516 : Nat := 118140960795 + 4817516 * 2 ^ 59
def prefixEnd_4817516 : Nat := 4983230072969 + 3 ^ 40 * 4817516 * 2
def baseEnd_4817516 : Nat := 2473701268725478680194653

theorem tailTrace_4817516 : CollatzResearch.WordTrace tailWord_4817516 prefixEnd_4817516 2473701268725478680194653 := by
  unfold tailWord_4817516
  simp only [CollatzResearch.WordTrace]
  refine ⟨87854621807484886537072201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117139495743313182049429601 87854621807484886537072201)
  ·
    refine ⟨65890966355613664902804151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87854621807484886537072201 65890966355613664902804151)
    ·
      refine ⟨98836449533420497354206227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65890966355613664902804151 98836449533420497354206227)
      ·
        refine ⟨148254674300130746031309341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98836449533420497354206227 148254674300130746031309341)
        ·
          refine ⟨55595502862549029761741003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148254674300130746031309341 55595502862549029761741003)
          ·
            refine ⟨83393254293823544642611505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55595502862549029761741003 83393254293823544642611505)
            ·
              refine ⟨62544940720367658481958629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83393254293823544642611505 62544940720367658481958629)
              ·
                refine ⟨11727176385068935965367243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62544940720367658481958629 11727176385068935965367243)
                ·
                  refine ⟨17590764577603403948050865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11727176385068935965367243 17590764577603403948050865)
                  ·
                    refine ⟨13193073433202552961038149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17590764577603403948050865 13193073433202552961038149)
                    ·
                      refine ⟨2473701268725478680194653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13193073433202552961038149 2473701268725478680194653)
                      ·
                        rfl

theorem cell23_4817516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_4817516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817516 prefixEnd_4817516 := by exact prefixLift 4817516
  have htrace : WordTrace (prefixWord ++ tailWord_4817516) baseStart_4817516 baseEnd_4817516 := by
    simpa [prefixWord, tailWord_4817516, baseEnd_4817516] using wordTrace_append hprefix tailTrace_4817516
  have hstable : (prefixWord ++ tailWord_4817516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817516).length < 2 ^ (prefixWord ++ tailWord_4817516).sum := by decide
  have hdescent : baseEnd_4817516 < baseStart_4817516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817586 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_4817586 : Nat := 118140960795 + 4817586 * 2 ^ 59
def prefixEnd_4817586 : Nat := 4983230072969 + 3 ^ 40 * 4817586 * 2
def baseEnd_4817586 : Nat := 824579070790431135439777

theorem tailTrace_4817586 : CollatzResearch.WordTrace tailWord_4817586 prefixEnd_4817586 824579070790431135439777 := by
  unfold tailWord_4817586
  simp only [CollatzResearch.WordTrace]
  refine ⟨43927949181179043757298153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117141197816477450019461741 43927949181179043757298153)
  ·
    refine ⟨32945961885884282817973615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43927949181179043757298153 32945961885884282817973615)
    ·
      refine ⟨49418942828826424226960423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32945961885884282817973615 49418942828826424226960423)
      ·
        refine ⟨74128414243239636340440635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49418942828826424226960423 74128414243239636340440635)
        ·
          refine ⟨111192621364859454510660953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74128414243239636340440635 111192621364859454510660953)
          ·
            refine ⟨83394466023644590882995715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111192621364859454510660953 83394466023644590882995715)
            ·
              refine ⟨125091699035466886324493573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83394466023644590882995715 125091699035466886324493573)
              ·
                refine ⟨23454693569150041185842545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125091699035466886324493573 23454693569150041185842545)
                ·
                  refine ⟨17591020176862530889381909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23454693569150041185842545 17591020176862530889381909)
                  ·
                    refine ⟨824579070790431135439777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17591020176862530889381909 824579070790431135439777)
                    ·
                      rfl

theorem cell23_4817586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_4817586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817586 prefixEnd_4817586 := by exact prefixLift 4817586
  have htrace : WordTrace (prefixWord ++ tailWord_4817586) baseStart_4817586 baseEnd_4817586 := by
    simpa [prefixWord, tailWord_4817586, baseEnd_4817586] using wordTrace_append hprefix tailTrace_4817586
  have hstable : (prefixWord ++ tailWord_4817586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817586).length < 2 ^ (prefixWord ++ tailWord_4817586).sum := by decide
  have hdescent : baseEnd_4817586 < baseStart_4817586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817593 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 5, 4, 2]
def baseStart_4817593 : Nat := 118140960795 + 4817593 * 2 ^ 59
def prefixEnd_4817593 : Nat := 4983230072969 + 3 ^ 40 * 4817593 * 2
def baseEnd_4817593 : Nat := 2473740806735874878931799

theorem tailTrace_4817593 : CollatzResearch.WordTrace tailWord_4817593 prefixEnd_4817593 2473740806735874878931799 := by
  unfold tailWord_4817593
  simp only [CollatzResearch.WordTrace]
  refine ⟨175712052035690815224697433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117141368023793876816464955 175712052035690815224697433)
  ·
    refine ⟨131784039026768111418523075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175712052035690815224697433 131784039026768111418523075)
    ·
      refine ⟨197676058540152167127784613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131784039026768111418523075 197676058540152167127784613)
      ·
        refine ⟨37064260976278531336459615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197676058540152167127784613 37064260976278531336459615)
        ·
          refine ⟨55596391464417797004689423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37064260976278531336459615 55596391464417797004689423)
          ·
            refine ⟨83394587196626695507034135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55596391464417797004689423 83394587196626695507034135)
            ·
              refine ⟨125091880794940043260551203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83394587196626695507034135 125091880794940043260551203)
              ·
                refine ⟨187637821192410064890826805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125091880794940043260551203 187637821192410064890826805)
                ·
                  refine ⟨17591045736788443583515013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 187637821192410064890826805 17591045736788443583515013)
                  ·
                    refine ⟨3298321075647833171909065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17591045736788443583515013 3298321075647833171909065)
                    ·
                      refine ⟨2473740806735874878931799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298321075647833171909065 2473740806735874878931799)
                      ·
                        rfl

theorem cell23_4817593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_4817593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817593 prefixEnd_4817593 := by exact prefixLift 4817593
  have htrace : WordTrace (prefixWord ++ tailWord_4817593) baseStart_4817593 baseEnd_4817593 := by
    simpa [prefixWord, tailWord_4817593, baseEnd_4817593] using wordTrace_append hprefix tailTrace_4817593
  have hstable : (prefixWord ++ tailWord_4817593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817593).length < 2 ^ (prefixWord ++ tailWord_4817593).sum := by decide
  have hdescent : baseEnd_4817593 < baseStart_4817593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817610 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 1, 4, 2]
def baseStart_4817610 : Nat := 118140960795 + 4817610 * 2 ^ 59
def prefixEnd_4817610 : Nat := 4983230072969 + 3 ^ 40 * 4817610 * 2
def baseEnd_4817610 : Nat := 2473749535907001312419221

theorem tailTrace_4817610 : CollatzResearch.WordTrace tailWord_4817610 prefixEnd_4817610 2473749535907001312419221 := by
  unfold tailWord_4817610
  simp only [CollatzResearch.WordTrace]
  refine ⟨43928168019157306782016571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117141781384419484752044189 43928168019157306782016571)
  ·
    refine ⟨65892252028735960173024857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43928168019157306782016571 65892252028735960173024857)
    ·
      refine ⟨49419189021551970129768643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65892252028735960173024857 49419189021551970129768643)
      ·
        refine ⟨74128783532327955194652965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49419189021551970129768643 74128783532327955194652965)
        ·
          refine ⟨13899146912311491598997431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74128783532327955194652965 13899146912311491598997431)
          ·
            refine ⟨20848720368467237398496147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13899146912311491598997431 20848720368467237398496147)
            ·
              refine ⟨31273080552700856097744221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20848720368467237398496147 31273080552700856097744221)
              ·
                refine ⟨11727405207262821036654083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31273080552700856097744221 11727405207262821036654083)
                ·
                  refine ⟨17591107810894231554981125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11727405207262821036654083 17591107810894231554981125)
                  ·
                    refine ⟨3298332714542668416558961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17591107810894231554981125 3298332714542668416558961)
                    ·
                      refine ⟨2473749535907001312419221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298332714542668416558961 2473749535907001312419221)
                      ·
                        rfl

theorem cell23_4817610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_4817610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817610 prefixEnd_4817610 := by exact prefixLift 4817610
  have htrace : WordTrace (prefixWord ++ tailWord_4817610) baseStart_4817610 baseEnd_4817610 := by
    simpa [prefixWord, tailWord_4817610, baseEnd_4817610] using wordTrace_append hprefix tailTrace_4817610
  have hstable : (prefixWord ++ tailWord_4817610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817610).length < 2 ^ (prefixWord ++ tailWord_4817610).sum := by decide
  have hdescent : baseEnd_4817610 < baseStart_4817610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817650 : List Nat := [3, 2, 1, 3, 1, 2, 2, 4, 5]
def baseStart_4817650 : Nat := 118140960795 + 4817650 * 2 ^ 59
def prefixEnd_4817650 : Nat := 4983230072969 + 3 ^ 40 * 4817650 * 2
def baseEnd_4817650 : Nat := 274863341681464572879893

theorem tailTrace_4817650 : CollatzResearch.WordTrace tailWord_4817650 prefixEnd_4817650 274863341681464572879893 := by
  unfold tailWord_4817650
  simp only [CollatzResearch.WordTrace]
  refine ⟨43928532749121078489880601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117142753997656209306348269 43928532749121078489880601)
  ·
    refine ⟨32946399561840808867410451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43928532749121078489880601 32946399561840808867410451)
    ·
      refine ⟨49419599342761213301115677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32946399561840808867410451 49419599342761213301115677)
      ·
        refine ⟨18532349753535454987918379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49419599342761213301115677 18532349753535454987918379)
        ·
          refine ⟨27798524630303182481877569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18532349753535454987918379 27798524630303182481877569)
          ·
            refine ⟨20848893472727386861408177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27798524630303182481877569 20848893472727386861408177)
            ·
              refine ⟨15636670104545540146056133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20848893472727386861408177 15636670104545540146056133)
              ·
                refine ⟨2931875644602288777385525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15636670104545540146056133 2931875644602288777385525)
                ·
                  refine ⟨274863341681464572879893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2931875644602288777385525 274863341681464572879893)
                  ·
                    rfl

theorem cell23_4817650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_4817650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817650 prefixEnd_4817650 := by exact prefixLift 4817650
  have htrace : WordTrace (prefixWord ++ tailWord_4817650) baseStart_4817650 baseEnd_4817650 := by
    simpa [prefixWord, tailWord_4817650, baseEnd_4817650] using wordTrace_append hprefix tailTrace_4817650
  have hstable : (prefixWord ++ tailWord_4817650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817650).length < 2 ^ (prefixWord ++ tailWord_4817650).sum := by decide
  have hdescent : baseEnd_4817650 < baseStart_4817650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817656 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_4817656 : Nat := 118140960795 + 4817656 * 2 ^ 59
def prefixEnd_4817656 : Nat := 4983230072969 + 3 ^ 40 * 4817656 * 2
def baseEnd_4817656 : Nat := 2473773156017108132444009

theorem tailTrace_4817656 : CollatzResearch.WordTrace tailWord_4817656 prefixEnd_4817656 2473773156017108132444009 := by
  unfold tailWord_4817656
  simp only [CollatzResearch.WordTrace]
  refine ⟨87857174917231288492120411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117142899889641717989493881 87857174917231288492120411)
  ·
    refine ⟨131785762375846932738180617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87857174917231288492120411 131785762375846932738180617)
    ·
      refine ⟨98839321781885199553635463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131785762375846932738180617 98839321781885199553635463)
      ·
        refine ⟨148258982672827799330453195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98839321781885199553635463 148258982672827799330453195)
        ·
          refine ⟨222388474009241698995679793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148258982672827799330453195 222388474009241698995679793)
          ·
            refine ⟨166791355506931274246759845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222388474009241698995679793 166791355506931274246759845)
            ·
              refine ⟨31273379157549613921267471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166791355506931274246759845 31273379157549613921267471)
              ·
                refine ⟨46910068736324420881901207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31273379157549613921267471 46910068736324420881901207)
                ·
                  refine ⟨70365103104486631322851811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46910068736324420881901207 70365103104486631322851811)
                  ·
                    refine ⟨105547654656729946984277717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70365103104486631322851811 105547654656729946984277717)
                    ·
                      refine ⟨2473773156017108132444009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105547654656729946984277717 2473773156017108132444009)
                      ·
                        rfl

theorem cell23_4817656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_4817656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817656 prefixEnd_4817656 := by exact prefixLift 4817656
  have htrace : WordTrace (prefixWord ++ tailWord_4817656) baseStart_4817656 baseEnd_4817656 := by
    simpa [prefixWord, tailWord_4817656, baseEnd_4817656] using wordTrace_append hprefix tailTrace_4817656
  have hstable : (prefixWord ++ tailWord_4817656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817656).length < 2 ^ (prefixWord ++ tailWord_4817656).sum := by decide
  have hdescent : baseEnd_4817656 < baseStart_4817656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817676 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 1, 10]
def baseStart_4817676 : Nat := 118140960795 + 4817676 * 2 ^ 59
def prefixEnd_4817676 : Nat := 4983230072969 + 3 ^ 40 * 4817676 * 2
def baseEnd_4817676 : Nat := 824594475210066018064639

theorem tailTrace_4817676 : CollatzResearch.WordTrace tailWord_4817676 prefixEnd_4817676 824594475210066018064639 := by
  unfold tailWord_4817676
  simp only [CollatzResearch.WordTrace]
  refine ⟨87857539647195060199984441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117143386196260080266645921 87857539647195060199984441)
  ·
    refine ⟨65893154735396295149988331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87857539647195060199984441 65893154735396295149988331)
    ·
      refine ⟨98839732103094442724982497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65893154735396295149988331 98839732103094442724982497)
      ·
        refine ⟨74129799077320832043736873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98839732103094442724982497 74129799077320832043736873)
        ·
          refine ⟨55597349307990624032802655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74129799077320832043736873 55597349307990624032802655)
          ·
            refine ⟨83396023961985936049203983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55597349307990624032802655 83396023961985936049203983)
            ·
              refine ⟨125094035942978904073805975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83396023961985936049203983 125094035942978904073805975)
              ·
                refine ⟨187641053914468356110708963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125094035942978904073805975 187641053914468356110708963)
                ·
                  refine ⟨281461580871702534166063445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187641053914468356110708963 281461580871702534166063445)
                  ·
                    refine ⟨824594475210066018064639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 281461580871702534166063445 824594475210066018064639)
                    ·
                      rfl

theorem cell23_4817676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_4817676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817676 prefixEnd_4817676 := by exact prefixLift 4817676
  have htrace : WordTrace (prefixWord ++ tailWord_4817676) baseStart_4817676 baseEnd_4817676 := by
    simpa [prefixWord, tailWord_4817676, baseEnd_4817676] using wordTrace_append hprefix tailTrace_4817676
  have hstable : (prefixWord ++ tailWord_4817676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817676).length < 2 ^ (prefixWord ++ tailWord_4817676).sum := by decide
  have hdescent : baseEnd_4817676 < baseStart_4817676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817683 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 4]
def baseStart_4817683 : Nat := 118140960795 + 4817683 * 2 ^ 59
def prefixEnd_4817683 : Nat := 4983230072969 + 3 ^ 40 * 4817683 * 2
def baseEnd_4817683 : Nat := 2473787019994779526806385

theorem tailTrace_4817683 : CollatzResearch.WordTrace tailWord_4817683 prefixEnd_4817683 2473787019994779526806385 := by
  unfold tailWord_4817683
  simp only [CollatzResearch.WordTrace]
  refine ⟨175715334605364760595473703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117143556403576507063649135 175715334605364760595473703)
  ·
    refine ⟨263573001908047140893210555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175715334605364760595473703 263573001908047140893210555)
    ·
      refine ⟨395359502862070711339815833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263573001908047140893210555 395359502862070711339815833)
      ·
        refine ⟨296519627146553033504861875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395359502862070711339815833 296519627146553033504861875)
        ·
          refine ⟨444779440719829550257292813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296519627146553033504861875 444779440719829550257292813)
          ·
            refine ⟨166792290269936081346484805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 444779440719829550257292813 166792290269936081346484805)
            ·
              refine ⟨31273554425613015252465901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166792290269936081346484805 31273554425613015252465901)
              ·
                refine ⟨11727582909604880719674713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31273554425613015252465901 11727582909604880719674713)
                ·
                  refine ⟨8795687182203660539756035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11727582909604880719674713 8795687182203660539756035)
                  ·
                    refine ⟨13193530773305490809634053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8795687182203660539756035 13193530773305490809634053)
                    ·
                      refine ⟨2473787019994779526806385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13193530773305490809634053 2473787019994779526806385)
                      ·
                        rfl

theorem cell23_4817683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_4817683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817683 prefixEnd_4817683 := by exact prefixLift 4817683
  have htrace : WordTrace (prefixWord ++ tailWord_4817683) baseStart_4817683 baseEnd_4817683 := by
    simpa [prefixWord, tailWord_4817683, baseEnd_4817683] using wordTrace_append hprefix tailTrace_4817683
  have hstable : (prefixWord ++ tailWord_4817683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817683).length < 2 ^ (prefixWord ++ tailWord_4817683).sum := by decide
  have hdescent : baseEnd_4817683 < baseStart_4817683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817800 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 1, 6]
def baseStart_4817800 : Nat := 118140960795 + 4817800 * 2 ^ 59
def prefixEnd_4817800 : Nat := 4983230072969 + 3 ^ 40 * 4817800 * 2
def baseEnd_4817800 : Nat := 824615699077118523014449

theorem tailTrace_4817800 : CollatzResearch.WordTrace tailWord_4817800 prefixEnd_4817800 824615699077118523014449 := by
  unfold tailWord_4817800
  simp only [CollatzResearch.WordTrace]
  refine ⟨87859800972970444788741427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117146401297293926384988569 87859800972970444788741427)
  ·
    refine ⟨131789701459455667183112141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87859800972970444788741427 131789701459455667183112141)
    ·
      refine ⟨49421138047295875193667053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131789701459455667183112141 49421138047295875193667053)
      ·
        refine ⟨18532926767735953197625145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49421138047295875193667053 18532926767735953197625145)
        ·
          refine ⟨13899695075801964898218859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18532926767735953197625145 13899695075801964898218859)
          ·
            refine ⟨20849542613702947347328289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13899695075801964898218859 20849542613702947347328289)
            ·
              refine ⟨15637156960277210510496217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20849542613702947347328289 15637156960277210510496217)
              ·
                refine ⟨11727867720207907882872163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15637156960277210510496217 11727867720207907882872163)
                ·
                  refine ⟨17591801580311861824308245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11727867720207907882872163 17591801580311861824308245)
                  ·
                    refine ⟨824615699077118523014449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17591801580311861824308245 824615699077118523014449)
                    ·
                      rfl

theorem cell23_4817800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_4817800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817800 prefixEnd_4817800 := by exact prefixLift 4817800
  have htrace : WordTrace (prefixWord ++ tailWord_4817800) baseStart_4817800 baseEnd_4817800 := by
    simpa [prefixWord, tailWord_4817800, baseEnd_4817800] using wordTrace_append hprefix tailTrace_4817800
  have hstable : (prefixWord ++ tailWord_4817800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817800).length < 2 ^ (prefixWord ++ tailWord_4817800).sum := by decide
  have hdescent : baseEnd_4817800 < baseStart_4817800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817813 : List Nat := [1, 3, 2, 1, 1, 5, 10]
def baseStart_4817813 : Nat := 118140960795 + 4817813 * 2 ^ 59
def prefixEnd_4817813 : Nat := 4983230072969 + 3 ^ 40 * 4817813 * 2
def baseEnd_4817813 : Nat := 30541404598516839730627

theorem tailTrace_4817813 : CollatzResearch.WordTrace tailWord_4817813 prefixEnd_4817813 30541404598516839730627 := by
  unfold tailWord_4817813
  simp only [CollatzResearch.WordTrace]
  refine ⟨175720076094893792797706093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117146717396595861865137395 175720076094893792797706093)
  ·
    refine ⟨65895028535585172299139785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175720076094893792797706093 65895028535585172299139785)
    ·
      refine ⟨49421271401688879224354839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65895028535585172299139785 49421271401688879224354839)
      ·
        refine ⟨74131907102533318836532259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49421271401688879224354839 74131907102533318836532259)
        ·
          refine ⟨111197860653799978254798389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74131907102533318836532259 111197860653799978254798389)
          ·
            refine ⟨10424799436293747961387349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111197860653799978254798389 10424799436293747961387349)
            ·
              refine ⟨30541404598516839730627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10424799436293747961387349 30541404598516839730627)
              ·
                rfl

theorem cell23_4817813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 10].length) (baseStart_4817813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817813 prefixEnd_4817813 := by exact prefixLift 4817813
  have htrace : WordTrace (prefixWord ++ tailWord_4817813) baseStart_4817813 baseEnd_4817813 := by
    simpa [prefixWord, tailWord_4817813, baseEnd_4817813] using wordTrace_append hprefix tailTrace_4817813
  have hstable : (prefixWord ++ tailWord_4817813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817813).length < 2 ^ (prefixWord ++ tailWord_4817813).sum := by decide
  have hdescent : baseEnd_4817813 < baseStart_4817813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817874 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_4817874 : Nat := 118140960795 + 4817874 * 2 ^ 59
def prefixEnd_4817874 : Nat := 4983230072969 + 3 ^ 40 * 4817874 * 2
def baseEnd_4817874 : Nat := 2473885094799788279518007

theorem tailTrace_4817874 : CollatzResearch.WordTrace tailWord_4817874 prefixEnd_4817874 2473885094799788279518007 := by
  unfold tailWord_4817874
  simp only [CollatzResearch.WordTrace]
  refine ⟨43930575236918200053919169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117148200631781866810451117 43930575236918200053919169)
  ·
    refine ⟨32947931427688650040439377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43930575236918200053919169 32947931427688650040439377)
    ·
      refine ⟨24710948570766487530329533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32947931427688650040439377 24710948570766487530329533)
      ·
        refine ⟨9266605714037432823873575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24710948570766487530329533 9266605714037432823873575)
        ·
          refine ⟨13899908571056149235810363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9266605714037432823873575 13899908571056149235810363)
          ·
            refine ⟨20849862856584223853715545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13899908571056149235810363 20849862856584223853715545)
            ·
              refine ⟨15637397142438167890286659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20849862856584223853715545 15637397142438167890286659)
              ·
                refine ⟨23456095713657251835429989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15637397142438167890286659 23456095713657251835429989)
                ·
                  refine ⟨4398017946310734719143123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23456095713657251835429989 4398017946310734719143123)
                  ·
                    refine ⟨6597026919466102078714685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4398017946310734719143123 6597026919466102078714685)
                    ·
                      refine ⟨2473885094799788279518007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6597026919466102078714685 2473885094799788279518007)
                      ·
                        rfl

theorem cell23_4817874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_4817874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817874 prefixEnd_4817874 := by exact prefixLift 4817874
  have htrace : WordTrace (prefixWord ++ tailWord_4817874) baseStart_4817874 baseEnd_4817874 := by
    simpa [prefixWord, tailWord_4817874, baseEnd_4817874] using wordTrace_append hprefix tailTrace_4817874
  have hstable : (prefixWord ++ tailWord_4817874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817874).length < 2 ^ (prefixWord ++ tailWord_4817874).sum := by decide
  have hdescent : baseEnd_4817874 < baseStart_4817874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817931 : List Nat := [1, 1, 1, 1, 6, 3, 2, 2, 2, 2, 2]
def baseStart_4817931 : Nat := 118140960795 + 4817931 * 2 ^ 59
def prefixEnd_4817931 : Nat := 4983230072969 + 3 ^ 40 * 4817931 * 2
def baseEnd_4817931 : Nat := 2473914363197094556505245

theorem tailTrace_4817931 : CollatzResearch.WordTrace tailWord_4817931 prefixEnd_4817931 2473914363197094556505245 := by
  unfold tailWord_4817931
  simp only [CollatzResearch.WordTrace]
  refine ⟨175724379908466298950501647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117149586605644199300334431 175724379908466298950501647)
  ·
    refine ⟨263586569862699448425752471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175724379908466298950501647 263586569862699448425752471)
    ·
      refine ⟨395379854794049172638628707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263586569862699448425752471 395379854794049172638628707)
      ·
        refine ⟨593069782191073758957943061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395379854794049172638628707 593069782191073758957943061)
        ·
          refine ⟨27800146040206582451153581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 593069782191073758957943061 27800146040206582451153581)
          ·
            refine ⟨10425054765077468419182593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27800146040206582451153581 10425054765077468419182593)
            ·
              refine ⟨7818791073808101314386945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10425054765077468419182593 7818791073808101314386945)
              ·
                refine ⟨5864093305356075985790209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7818791073808101314386945 5864093305356075985790209)
                ·
                  refine ⟨4398069979017056989342657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5864093305356075985790209 4398069979017056989342657)
                  ·
                    refine ⟨3298552484262792742006993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4398069979017056989342657 3298552484262792742006993)
                    ·
                      refine ⟨2473914363197094556505245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298552484262792742006993 2473914363197094556505245)
                      ·
                        rfl

theorem cell23_4817931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 2, 2].length) (baseStart_4817931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817931 prefixEnd_4817931 := by exact prefixLift 4817931
  have htrace : WordTrace (prefixWord ++ tailWord_4817931) baseStart_4817931 baseEnd_4817931 := by
    simpa [prefixWord, tailWord_4817931, baseEnd_4817931] using wordTrace_append hprefix tailTrace_4817931
  have hstable : (prefixWord ++ tailWord_4817931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817931).length < 2 ^ (prefixWord ++ tailWord_4817931).sum := by decide
  have hdescent : baseEnd_4817931 < baseStart_4817931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817957 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 2, 5, 2]
def baseStart_4817957 : Nat := 118140960795 + 4817957 * 2 ^ 59
def prefixEnd_4817957 : Nat := 4983230072969 + 3 ^ 40 * 4817957 * 2
def baseEnd_4817957 : Nat := 2473927713694111454780125

theorem tailTrace_4817957 : CollatzResearch.WordTrace tailWord_4817957 prefixEnd_4817957 2473927713694111454780125 := by
  unfold tailWord_4817957
  simp only [CollatzResearch.WordTrace]
  refine ⟨175725328206372105390948125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117150218804248070260632083 175725328206372105390948125)
  ·
    refine ⟨65896998077389539521605547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175725328206372105390948125 65896998077389539521605547)
    ·
      refine ⟨98845497116084309282408321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65896998077389539521605547 98845497116084309282408321)
      ·
        refine ⟨74134122837063231961806241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98845497116084309282408321 74134122837063231961806241)
        ·
          refine ⟨55600592127797423971354681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74134122837063231961806241 55600592127797423971354681)
          ·
            refine ⟨41700444095848067978516011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55600592127797423971354681 41700444095848067978516011)
            ·
              refine ⟨62550666143772101967774017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41700444095848067978516011 62550666143772101967774017)
              ·
                refine ⟨46912999607829076475830513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62550666143772101967774017 46912999607829076475830513)
                ·
                  refine ⟨35184749705871807356872885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46912999607829076475830513 35184749705871807356872885)
                  ·
                    refine ⟨3298570284925481939706833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35184749705871807356872885 3298570284925481939706833)
                    ·
                      refine ⟨2473927713694111454780125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298570284925481939706833 2473927713694111454780125)
                      ·
                        rfl

theorem cell23_4817957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_4817957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817957 prefixEnd_4817957 := by exact prefixLift 4817957
  have htrace : WordTrace (prefixWord ++ tailWord_4817957) baseStart_4817957 baseEnd_4817957 := by
    simpa [prefixWord, tailWord_4817957, baseEnd_4817957] using wordTrace_append hprefix tailTrace_4817957
  have hstable : (prefixWord ++ tailWord_4817957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817957).length < 2 ^ (prefixWord ++ tailWord_4817957).sum := by decide
  have hdescent : baseEnd_4817957 < baseStart_4817957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4817987 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 4, 4, 2]
def baseStart_4817987 : Nat := 118140960795 + 4817987 * 2 ^ 59
def prefixEnd_4817987 : Nat := 4983230072969 + 3 ^ 40 * 4817987 * 2
def baseEnd_4817987 : Nat := 2473943118113746337404987

theorem tailTrace_4817987 : CollatzResearch.WordTrace tailWord_4817987 prefixEnd_4817987 2473943118113746337404987 := by
  unfold tailWord_4817987
  simp only [CollatzResearch.WordTrace]
  refine ⟨175726422396263420514540215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117150948264175613676360143 175726422396263420514540215)
  ·
    refine ⟨263589633594395130771810323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175726422396263420514540215 263589633594395130771810323)
    ·
      refine ⟨395384450391592696157715485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263589633594395130771810323 395384450391592696157715485)
      ·
        refine ⟨148269168896847261059143307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 395384450391592696157715485 148269168896847261059143307)
        ·
          refine ⟨222403753345270891588714961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148269168896847261059143307 222403753345270891588714961)
          ·
            refine ⟨166802815008953168691536221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222403753345270891588714961 166802815008953168691536221)
            ·
              refine ⟨62551055628357438259326083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166802815008953168691536221 62551055628357438259326083)
              ·
                refine ⟨93826583442536157388989125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62551055628357438259326083 93826583442536157388989125)
                ·
                  refine ⟨17592484395475529510435461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93826583442536157388989125 17592484395475529510435461)
                  ·
                    refine ⟨3298590824151661783206649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17592484395475529510435461 3298590824151661783206649)
                    ·
                      refine ⟨2473943118113746337404987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298590824151661783206649 2473943118113746337404987)
                      ·
                        rfl

theorem cell23_4817987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 4, 2].length) (baseStart_4817987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4817987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4817987 prefixEnd_4817987 := by exact prefixLift 4817987
  have htrace : WordTrace (prefixWord ++ tailWord_4817987) baseStart_4817987 baseEnd_4817987 := by
    simpa [prefixWord, tailWord_4817987, baseEnd_4817987] using wordTrace_append hprefix tailTrace_4817987
  have hstable : (prefixWord ++ tailWord_4817987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4817987).length < 2 ^ (prefixWord ++ tailWord_4817987).sum := by decide
  have hdescent : baseEnd_4817987 < baseStart_4817987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4817987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818004 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_4818004 : Nat := 118140960795 + 4818004 * 2 ^ 59
def prefixEnd_4818004 : Nat := 4983230072969 + 3 ^ 40 * 4818004 * 2
def baseEnd_4818004 : Nat := 2473951847284872770892409

theorem tailTrace_4818004 : CollatzResearch.WordTrace tailWord_4818004 prefixEnd_4818004 2473951847284872770892409 := by
  unfold tailWord_4818004
  simp only [CollatzResearch.WordTrace]
  refine ⟨87863521218600916208954533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117151361624801221611939377 87863521218600916208954533)
  ·
    refine ⟨16474410228487671789178975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87863521218600916208954533 16474410228487671789178975)
    ·
      refine ⟨24711615342731507683768463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16474410228487671789178975 24711615342731507683768463)
      ·
        refine ⟨37067423014097261525652695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24711615342731507683768463 37067423014097261525652695)
        ·
          refine ⟨55601134521145892288479043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37067423014097261525652695 55601134521145892288479043)
          ·
            refine ⟨83401701781718838432718565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55601134521145892288479043 83401701781718838432718565)
            ·
              refine ⟨15637819084072282206134731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83401701781718838432718565 15637819084072282206134731)
              ·
                refine ⟨23456728626108423309202097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15637819084072282206134731 23456728626108423309202097)
                ·
                  refine ⟨17592546469581317481901573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23456728626108423309202097 17592546469581317481901573)
                  ·
                    refine ⟨3298602463046497027856545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17592546469581317481901573 3298602463046497027856545)
                    ·
                      refine ⟨2473951847284872770892409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298602463046497027856545 2473951847284872770892409)
                      ·
                        rfl

theorem cell23_4818004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_4818004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818004 prefixEnd_4818004 := by exact prefixLift 4818004
  have htrace : WordTrace (prefixWord ++ tailWord_4818004) baseStart_4818004 baseEnd_4818004 := by
    simpa [prefixWord, tailWord_4818004, baseEnd_4818004] using wordTrace_append hprefix tailTrace_4818004
  have hstable : (prefixWord ++ tailWord_4818004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818004).length < 2 ^ (prefixWord ++ tailWord_4818004).sum := by decide
  have hdescent : baseEnd_4818004 < baseStart_4818004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818047 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 2, 9, 2]
def baseStart_4818047 : Nat := 118140960795 + 4818047 * 2 ^ 59
def prefixEnd_4818047 : Nat := 4983230072969 + 3 ^ 40 * 4818047 * 2
def baseEnd_4818047 : Nat := 2473973926953016102654711

theorem tailTrace_4818047 : CollatzResearch.WordTrace tailWord_4818047 prefixEnd_4818047 2473973926953016102654711 := by
  unfold tailWord_4818047
  simp only [CollatzResearch.WordTrace]
  refine ⟨175728610776046050761724395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117152407184030700507816263 175728610776046050761724395)
  ·
    refine ⟨263592916164069076142586593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175728610776046050761724395 263592916164069076142586593)
    ·
      refine ⟨197694687123051807106939945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263592916164069076142586593 197694687123051807106939945)
      ·
        refine ⟨148271015342288855330204959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197694687123051807106939945 148271015342288855330204959)
        ·
          refine ⟨222406523013433282995307439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148271015342288855330204959 222406523013433282995307439)
          ·
            refine ⟨333609784520149924492961159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222406523013433282995307439 333609784520149924492961159)
            ·
              refine ⟨500414676780224886739441739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333609784520149924492961159 500414676780224886739441739)
              ·
                refine ⟨750622015170337330109162609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500414676780224886739441739 750622015170337330109162609)
                ·
                  refine ⟨562966511377752997581871957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 750622015170337330109162609 562966511377752997581871957)
                  ·
                    refine ⟨3298631902604021470206281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 562966511377752997581871957 3298631902604021470206281)
                    ·
                      refine ⟨2473973926953016102654711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298631902604021470206281 2473973926953016102654711)
                      ·
                        rfl

theorem cell23_4818047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 9, 2].length) (baseStart_4818047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818047 prefixEnd_4818047 := by exact prefixLift 4818047
  have htrace : WordTrace (prefixWord ++ tailWord_4818047) baseStart_4818047 baseEnd_4818047 := by
    simpa [prefixWord, tailWord_4818047, baseEnd_4818047] using wordTrace_append hprefix tailTrace_4818047
  have hstable : (prefixWord ++ tailWord_4818047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818047).length < 2 ^ (prefixWord ++ tailWord_4818047).sum := by decide
  have hdescent : baseEnd_4818047 < baseStart_4818047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818074 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 3, 5]
def baseStart_4818074 : Nat := 118140960795 + 4818074 * 2 ^ 59
def prefixEnd_4818074 : Nat := 4983230072969 + 3 ^ 40 * 4818074 * 2
def baseEnd_4818074 : Nat := 824662596976895832339029

theorem tailTrace_4818074 : CollatzResearch.WordTrace tailWord_4818074 prefixEnd_4818074 824662596976895832339029 := by
  unfold tailWord_4818074
  simp only [CollatzResearch.WordTrace]
  refine ⟨43932398886737058593239319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117153063697965489581971517 43932398886737058593239319)
  ·
    refine ⟨65898598330105587889858979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43932398886737058593239319 65898598330105587889858979)
    ·
      refine ⟨98847897495158381834788469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65898598330105587889858979 98847897495158381834788469)
      ·
        refine ⟨9266990390171098297011419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98847897495158381834788469 9266990390171098297011419)
        ·
          refine ⟨13900485585256647445517129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9266990390171098297011419 13900485585256647445517129)
          ·
            refine ⟨10425364188942485584137847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13900485585256647445517129 10425364188942485584137847)
            ·
              refine ⟨15638046283413728376206771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10425364188942485584137847 15638046283413728376206771)
              ·
                refine ⟨23457069425120592564310157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15638046283413728376206771 23457069425120592564310157)
                ·
                  refine ⟨8796401034420222211616309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23457069425120592564310157 8796401034420222211616309)
                  ·
                    refine ⟨824662596976895832339029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8796401034420222211616309 824662596976895832339029)
                    ·
                      rfl

theorem cell23_4818074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_4818074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818074 prefixEnd_4818074 := by exact prefixLift 4818074
  have htrace : WordTrace (prefixWord ++ tailWord_4818074) baseStart_4818074 baseEnd_4818074 := by
    simpa [prefixWord, tailWord_4818074, baseEnd_4818074] using wordTrace_append hprefix tailTrace_4818074
  have hstable : (prefixWord ++ tailWord_4818074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818074).length < 2 ^ (prefixWord ++ tailWord_4818074).sum := by decide
  have hdescent : baseEnd_4818074 < baseStart_4818074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818081 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 2, 3, 2]
def baseStart_4818081 : Nat := 118140960795 + 4818081 * 2 ^ 59
def prefixEnd_4818081 : Nat := 4983230072969 + 3 ^ 40 * 4818081 * 2
def baseEnd_4818081 : Nat := 2473991385295268969629555

theorem tailTrace_4818081 : CollatzResearch.WordTrace tailWord_4818081 prefixEnd_4818081 2473991385295268969629555 := by
  unfold tailWord_4818081
  simp only [CollatzResearch.WordTrace]
  refine ⟨175729850857922874568462097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117153233905281916378974731 175729850857922874568462097)
  ·
    refine ⟨131797388143442155926346573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175729850857922874568462097 131797388143442155926346573)
    ·
      refine ⟨49424020553790808472379965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131797388143442155926346573 49424020553790808472379965)
      ·
        refine ⟨18534007707671553177142487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49424020553790808472379965 18534007707671553177142487)
        ·
          refine ⟨27801011561507329765713731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18534007707671553177142487 27801011561507329765713731)
          ·
            refine ⟨41701517342260994648570597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27801011561507329765713731 41701517342260994648570597)
            ·
              refine ⟨7819034501673936496606987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41701517342260994648570597 7819034501673936496606987)
              ·
                refine ⟨11728551752510904744910481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7819034501673936496606987 11728551752510904744910481)
                ·
                  refine ⟨8796413814383178558682861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11728551752510904744910481 8796413814383178558682861)
                  ·
                    refine ⟨3298655180393691959506073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8796413814383178558682861 3298655180393691959506073)
                    ·
                      refine ⟨2473991385295268969629555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298655180393691959506073 2473991385295268969629555)
                      ·
                        rfl

theorem cell23_4818081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_4818081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818081 prefixEnd_4818081 := by exact prefixLift 4818081
  have htrace : WordTrace (prefixWord ++ tailWord_4818081) baseStart_4818081 baseEnd_4818081 := by
    simpa [prefixWord, tailWord_4818081, baseEnd_4818081] using wordTrace_append hprefix tailTrace_4818081
  have hstable : (prefixWord ++ tailWord_4818081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818081).length < 2 ^ (prefixWord ++ tailWord_4818081).sum := by decide
  have hdescent : baseEnd_4818081 < baseStart_4818081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818105 : List Nat := [1, 2, 1, 4, 1, 5, 2, 2, 1, 1, 3]
def baseStart_4818105 : Nat := 118140960795 + 4818105 * 2 ^ 59
def prefixEnd_4818105 : Nat := 4983230072969 + 3 ^ 40 * 4818105 * 2
def baseEnd_4818105 : Nat := 2474003708830976875729445

theorem tailTrace_4818105 : CollatzResearch.WordTrace tailWord_4818105 prefixEnd_4818105 2474003708830976875729445 := by
  unfold tailWord_4818105
  simp only [CollatzResearch.WordTrace]
  refine ⟨175730726209835926667335769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117153817473223951111557179 175730726209835926667335769)
  ·
    refine ⟨131798044657376945000501827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175730726209835926667335769 131798044657376945000501827)
    ·
      refine ⟨197697066986065417500752741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131798044657376945000501827 197697066986065417500752741)
      ·
        refine ⟨37068200059887265781391139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197697066986065417500752741 37068200059887265781391139)
        ·
          refine ⟨55602300089830898672086709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37068200059887265781391139 55602300089830898672086709)
          ·
            refine ⟨5212715633421646750508129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55602300089830898672086709 5212715633421646750508129)
            ·
              refine ⟨3909536725066235062881097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5212715633421646750508129 3909536725066235062881097)
              ·
                refine ⟨2932152543799676297160823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3909536725066235062881097 2932152543799676297160823)
                ·
                  refine ⟨4398228815699514445741235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932152543799676297160823 4398228815699514445741235)
                  ·
                    refine ⟨6597343223549271668611853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4398228815699514445741235 6597343223549271668611853)
                    ·
                      refine ⟨2474003708830976875729445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6597343223549271668611853 2474003708830976875729445)
                      ·
                        rfl

theorem cell23_4818105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_4818105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818105 prefixEnd_4818105 := by exact prefixLift 4818105
  have htrace : WordTrace (prefixWord ++ tailWord_4818105) baseStart_4818105 baseEnd_4818105 := by
    simpa [prefixWord, tailWord_4818105, baseEnd_4818105] using wordTrace_append hprefix tailTrace_4818105
  have hstable : (prefixWord ++ tailWord_4818105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818105).length < 2 ^ (prefixWord ++ tailWord_4818105).sum := by decide
  have hdescent : baseEnd_4818105 < baseStart_4818105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818132 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4818132 : Nat := 118140960795 + 4818132 * 2 ^ 59
def prefixEnd_4818132 : Nat := 4983230072969 + 3 ^ 40 * 4818132 * 2
def baseEnd_4818132 : Nat := 2474017572808648270091821

theorem tailTrace_4818132 : CollatzResearch.WordTrace tailWord_4818132 prefixEnd_4818132 2474017572808648270091821 := by
  unfold tailWord_4818132
  simp only [CollatzResearch.WordTrace]
  refine ⟨87865855490369055139284325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117154473987158740185712433 87865855490369055139284325)
  ·
    refine ⟨16474847904444197838615811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87865855490369055139284325 16474847904444197838615811)
    ·
      refine ⟨24712271856666296757923717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16474847904444197838615811 24712271856666296757923717)
      ·
        refine ⟨4633550973124930642110697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24712271856666296757923717 4633550973124930642110697)
        ·
          refine ⟨3475163229843697981583023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4633550973124930642110697 3475163229843697981583023)
          ·
            refine ⟨5212744844765546972374535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475163229843697981583023 5212744844765546972374535)
            ·
              refine ⟨7819117267148320458561803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5212744844765546972374535 7819117267148320458561803)
              ·
                refine ⟨11728675900722480687842705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7819117267148320458561803 11728675900722480687842705)
                ·
                  refine ⟨8796506925541860515882029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11728675900722480687842705 8796506925541860515882029)
                  ·
                    refine ⟨3298690097078197693455761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8796506925541860515882029 3298690097078197693455761)
                    ·
                      refine ⟨2474017572808648270091821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298690097078197693455761 2474017572808648270091821)
                      ·
                        rfl

theorem cell23_4818132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4818132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818132 prefixEnd_4818132 := by exact prefixLift 4818132
  have htrace : WordTrace (prefixWord ++ tailWord_4818132) baseStart_4818132 baseEnd_4818132 := by
    simpa [prefixWord, tailWord_4818132, baseEnd_4818132] using wordTrace_append hprefix tailTrace_4818132
  have hstable : (prefixWord ++ tailWord_4818132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818132).length < 2 ^ (prefixWord ++ tailWord_4818132).sum := by decide
  have hdescent : baseEnd_4818132 < baseStart_4818132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818144 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 3]
def baseStart_4818144 : Nat := 118140960795 + 4818144 * 2 ^ 59
def prefixEnd_4818144 : Nat := 4983230072969 + 3 ^ 40 * 4818144 * 2
def baseEnd_4818144 : Nat := 2474023734576502223141765

theorem tailTrace_4818144 : CollatzResearch.WordTrace tailWord_4818144 prefixEnd_4818144 2474023734576502223141765 := by
  unfold tailWord_4818144
  simp only [CollatzResearch.WordTrace]
  refine ⟨87866074328347318164002743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117154765771129757552003657 87866074328347318164002743)
  ·
    refine ⟨131799111492520977246004115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87866074328347318164002743 131799111492520977246004115)
    ·
      refine ⟨197698667238781465869006173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131799111492520977246004115 197698667238781465869006173)
      ·
        refine ⟨74137000214543049700877315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197698667238781465869006173 74137000214543049700877315)
        ·
          refine ⟨111205500321814574551315973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74137000214543049700877315 111205500321814574551315973)
          ·
            refine ⟨20851031310340232728371745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111205500321814574551315973 20851031310340232728371745)
            ·
              refine ⟨15638273482755174546278809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20851031310340232728371745 15638273482755174546278809)
              ·
                refine ⟨11728705112066380909709107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15638273482755174546278809 11728705112066380909709107)
                ·
                  refine ⟨17593057668099571364563661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11728705112066380909709107 17593057668099571364563661)
                  ·
                    refine ⟨6597396625537339261711373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17593057668099571364563661 6597396625537339261711373)
                    ·
                      refine ⟨2474023734576502223141765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6597396625537339261711373 2474023734576502223141765)
                      ·
                        rfl

theorem cell23_4818144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_4818144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818144 prefixEnd_4818144 := by exact prefixLift 4818144
  have htrace : WordTrace (prefixWord ++ tailWord_4818144) baseStart_4818144 baseEnd_4818144 := by
    simpa [prefixWord, tailWord_4818144, baseEnd_4818144] using wordTrace_append hprefix tailTrace_4818144
  have hstable : (prefixWord ++ tailWord_4818144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818144).length < 2 ^ (prefixWord ++ tailWord_4818144).sum := by decide
  have hdescent : baseEnd_4818144 < baseStart_4818144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818145 : List Nat := [1, 2, 3, 1, 3, 3, 2, 3, 1, 2, 2]
def baseStart_4818145 : Nat := 118140960795 + 4818145 * 2 ^ 59
def prefixEnd_4818145 : Nat := 4983230072969 + 3 ^ 40 * 4818145 * 2
def baseEnd_4818145 : Nat := 2474024248057156719229261

theorem tailTrace_4818145 : CollatzResearch.WordTrace tailWord_4818145 prefixEnd_4818145 2474024248057156719229261 := by
  unfold tailWord_4818145
  simp only [CollatzResearch.WordTrace]
  refine ⟨175732185129691013498791889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117154790086460675665861259 175732185129691013498791889)
  ·
    refine ⟨131799138847268260124093917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175732185129691013498791889 131799138847268260124093917)
    ·
      refine ⟨49424677067725597546535219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131799138847268260124093917 49424677067725597546535219)
      ·
        refine ⟨74137015601588396319802829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49424677067725597546535219 74137015601588396319802829)
        ·
          refine ⟨27801380850595648619926061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74137015601588396319802829 27801380850595648619926061)
          ·
            refine ⟨10425517818973368232472273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27801380850595648619926061 10425517818973368232472273)
            ·
              refine ⟨7819138364230026174354205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10425517818973368232472273 7819138364230026174354205)
              ·
                refine ⟨2932176886586259815382827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7819138364230026174354205 2932176886586259815382827)
                ·
                  refine ⟨4398265329879389723074241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932176886586259815382827 4398265329879389723074241)
                  ·
                    refine ⟨3298698997409542292305681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4398265329879389723074241 3298698997409542292305681)
                    ·
                      refine ⟨2474024248057156719229261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298698997409542292305681 2474024248057156719229261)
                      ·
                        rfl

theorem cell23_4818145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_4818145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818145 prefixEnd_4818145 := by exact prefixLift 4818145
  have htrace : WordTrace (prefixWord ++ tailWord_4818145) baseStart_4818145 baseEnd_4818145 := by
    simpa [prefixWord, tailWord_4818145, baseEnd_4818145] using wordTrace_append hprefix tailTrace_4818145
  have hstable : (prefixWord ++ tailWord_4818145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818145).length < 2 ^ (prefixWord ++ tailWord_4818145).sum := by decide
  have hdescent : baseEnd_4818145 < baseStart_4818145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818188 : List Nat := [2, 2, 1, 2, 2, 4, 2, 2, 1, 3, 2]
def baseStart_4818188 : Nat := 118140960795 + 4818188 * 2 ^ 59
def prefixEnd_4818188 : Nat := 4983230072969 + 3 ^ 40 * 4818188 * 2
def baseEnd_4818188 : Nat := 2474046327725300050991563

theorem tailTrace_4818188 : CollatzResearch.WordTrace tailWord_4818188 prefixEnd_4818188 2474046327725300050991563 := by
  unfold tailWord_4818188
  simp only [CollatzResearch.WordTrace]
  refine ⟨87866876734267615921303609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117155835645690154561738145 87866876734267615921303609)
  ·
    refine ⟨65900157550700711940977707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87866876734267615921303609 65900157550700711940977707)
    ·
      refine ⟨98850236326051067911466561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65900157550700711940977707 98850236326051067911466561)
      ·
        refine ⟨74137677244538300933599921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98850236326051067911466561 74137677244538300933599921)
        ·
          refine ⟨55603257933403725700199941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74137677244538300933599921 55603257933403725700199941)
          ·
            refine ⟨10425610862513198568787489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55603257933403725700199941 10425610862513198568787489)
            ·
              refine ⟨7819208146884898926590617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10425610862513198568787489 7819208146884898926590617)
              ·
                refine ⟨5864406110163674194942963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7819208146884898926590617 5864406110163674194942963)
                ·
                  refine ⟨8796609165245511292414445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5864406110163674194942963 8796609165245511292414445)
                  ·
                    refine ⟨3298728436967066734655417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8796609165245511292414445 3298728436967066734655417)
                    ·
                      refine ⟨2474046327725300050991563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298728436967066734655417 2474046327725300050991563)
                      ·
                        rfl

theorem cell23_4818188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_4818188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818188 prefixEnd_4818188 := by exact prefixLift 4818188
  have htrace : WordTrace (prefixWord ++ tailWord_4818188) baseStart_4818188 baseEnd_4818188 := by
    simpa [prefixWord, tailWord_4818188, baseEnd_4818188] using wordTrace_append hprefix tailTrace_4818188
  have hstable : (prefixWord ++ tailWord_4818188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818188).length < 2 ^ (prefixWord ++ tailWord_4818188).sum := by decide
  have hdescent : baseEnd_4818188 < baseStart_4818188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818234 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3]
def baseStart_4818234 : Nat := 118140960795 + 4818234 * 2 ^ 59
def prefixEnd_4818234 : Nat := 4983230072969 + 3 ^ 40 * 4818234 * 2
def baseEnd_4818234 : Nat := 2474069947835406871016351

theorem tailTrace_4818234 : CollatzResearch.WordTrace tailWord_4818234 prefixEnd_4818234 2474069947835406871016351 := by
  unfold tailWord_4818234
  simp only [CollatzResearch.WordTrace]
  refine ⟨43933857806592145424695439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117156954150912387799187837 43933857806592145424695439)
  ·
    refine ⟨65900786709888218137043159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43933857806592145424695439 65900786709888218137043159)
    ·
      refine ⟨98851180064832327205564739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65900786709888218137043159 98851180064832327205564739)
      ·
        refine ⟨148276770097248490808347109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98851180064832327205564739 148276770097248490808347109)
        ·
          refine ⟨27801894393234092026565083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148276770097248490808347109 27801894393234092026565083)
          ·
            refine ⟨41702841589851138039847625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27801894393234092026565083 41702841589851138039847625)
            ·
              refine ⟨31277131192388353529885719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41702841589851138039847625 31277131192388353529885719)
              ·
                refine ⟨46915696788582530294828579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31277131192388353529885719 46915696788582530294828579)
                ·
                  refine ⟨70373545182873795442242869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46915696788582530294828579 70373545182873795442242869)
                  ·
                    refine ⟨6597519860894418322710269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70373545182873795442242869 6597519860894418322710269)
                    ·
                      refine ⟨2474069947835406871016351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6597519860894418322710269 2474069947835406871016351)
                      ·
                        rfl

theorem cell23_4818234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_4818234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818234 prefixEnd_4818234 := by exact prefixLift 4818234
  have htrace : WordTrace (prefixWord ++ tailWord_4818234) baseStart_4818234 baseEnd_4818234 := by
    simpa [prefixWord, tailWord_4818234, baseEnd_4818234] using wordTrace_append hprefix tailTrace_4818234
  have hstable : (prefixWord ++ tailWord_4818234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818234).length < 2 ^ (prefixWord ++ tailWord_4818234).sum := by decide
  have hdescent : baseEnd_4818234 < baseStart_4818234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818301 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_4818301 : Nat := 118140960795 + 4818301 * 2 ^ 59
def prefixEnd_4818301 : Nat := 4983230072969 + 3 ^ 40 * 4818301 * 2
def baseEnd_4818301 : Nat := 824701450346419369626181

theorem tailTrace_4818301 : CollatzResearch.WordTrace tailWord_4818301 prefixEnd_4818301 824701450346419369626181 := by
  unfold tailWord_4818301
  simp only [CollatzResearch.WordTrace]
  refine ⟨175737874917125852141470757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117158583278083901427647171 175737874917125852141470757)
  ·
    refine ⟨32950851546961097276525767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175737874917125852141470757 32950851546961097276525767)
    ·
      refine ⟨49426277320441645914788651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32950851546961097276525767 49426277320441645914788651)
      ·
        refine ⟨74139415980662468872182977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49426277320441645914788651 74139415980662468872182977)
        ·
          refine ⟨55604561985496851654137233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74139415980662468872182977 55604561985496851654137233)
          ·
            refine ⟨41703421489122638740602925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55604561985496851654137233 41703421489122638740602925)
            ·
              refine ⟨15638783058420989527726097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41703421489122638740602925 15638783058420989527726097)
              ·
                refine ⟨11729087293815742145794573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15638783058420989527726097 11729087293815742145794573)
                ·
                  refine ⟨4398407735180903304672965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11729087293815742145794573 4398407735180903304672965)
                  ·
                    refine ⟨824701450346419369626181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4398407735180903304672965 824701450346419369626181)
                    ·
                      rfl

theorem cell23_4818301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_4818301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818301 prefixEnd_4818301 := by exact prefixLift 4818301
  have htrace : WordTrace (prefixWord ++ tailWord_4818301) baseStart_4818301 baseEnd_4818301 := by
    simpa [prefixWord, tailWord_4818301, baseEnd_4818301] using wordTrace_append hprefix tailTrace_4818301
  have hstable : (prefixWord ++ tailWord_4818301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818301).length < 2 ^ (prefixWord ++ tailWord_4818301).sum := by decide
  have hdescent : baseEnd_4818301 < baseStart_4818301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818305 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 2, 5]
def baseStart_4818305 : Nat := 118140960795 + 4818305 * 2 ^ 59
def prefixEnd_4818305 : Nat := 4983230072969 + 3 ^ 40 * 4818305 * 2
def baseEnd_4818305 : Nat := 824702134987292031076175

theorem tailTrace_4818305 : CollatzResearch.WordTrace tailWord_4818305 prefixEnd_4818305 824702134987292031076175 := by
  unfold tailWord_4818305
  simp only [CollatzResearch.WordTrace]
  refine ⟨175738020809111360824616369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117158680539407573883077579 175738020809111360824616369)
  ·
    refine ⟨131803515606833520618462277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175738020809111360824616369 131803515606833520618462277)
    ·
      refine ⟨24713159176281285115961677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131803515606833520618462277 24713159176281285115961677)
      ·
        refine ⟨9267434691105481918485629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24713159176281285115961677 9267434691105481918485629)
        ·
          refine ⟨3475288009164555719432111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9267434691105481918485629 3475288009164555719432111)
          ·
            refine ⟨5212932013746833579148167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475288009164555719432111 5212932013746833579148167)
            ·
              refine ⟨7819398020620250368722251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5212932013746833579148167 7819398020620250368722251)
              ·
                refine ⟨11729097030930375553083377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7819398020620250368722251 11729097030930375553083377)
                ·
                  refine ⟨8796822773197781664812533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11729097030930375553083377 8796822773197781664812533)
                  ·
                    refine ⟨824702134987292031076175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8796822773197781664812533 824702134987292031076175)
                    ·
                      rfl

theorem cell23_4818305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_4818305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818305 prefixEnd_4818305 := by exact prefixLift 4818305
  have htrace : WordTrace (prefixWord ++ tailWord_4818305) baseStart_4818305 baseEnd_4818305 := by
    simpa [prefixWord, tailWord_4818305, baseEnd_4818305] using wordTrace_append hprefix tailTrace_4818305
  have hstable : (prefixWord ++ tailWord_4818305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818305).length < 2 ^ (prefixWord ++ tailWord_4818305).sum := by decide
  have hdescent : baseEnd_4818305 < baseStart_4818305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818308 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_4818308 : Nat := 118140960795 + 4818308 * 2 ^ 59
def prefixEnd_4818308 : Nat := 4983230072969 + 3 ^ 40 * 4818308 * 2
def baseEnd_4818308 : Nat := 2474107945403839581491011

theorem tailTrace_4818308 : CollatzResearch.WordTrace tailWord_4818308 prefixEnd_4818308 2474107945403839581491011 := by
  unfold tailWord_4818308
  simp only [CollatzResearch.WordTrace]
  refine ⟨87869065114050246168487789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117158753485400328224650385 87869065114050246168487789)
  ·
    refine ⟨32950899417768842313182921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87869065114050246168487789 32950899417768842313182921)
    ·
      refine ⟨24713174563326631734887191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32950899417768842313182921 24713174563326631734887191)
      ·
        refine ⟨37069761844989947602330787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24713174563326631734887191 37069761844989947602330787)
        ·
          refine ⟨55604642767484921403496181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37069761844989947602330787 55604642767484921403496181)
          ·
            refine ⟨5212935259451711381577767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55604642767484921403496181 5212935259451711381577767)
            ·
              refine ⟨7819402889177567072366651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5212935259451711381577767 7819402889177567072366651)
              ·
                refine ⟨11729104333766350608549977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7819402889177567072366651 11729104333766350608549977)
                ·
                  refine ⟨8796828250324762956412483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11729104333766350608549977 8796828250324762956412483)
                  ·
                    refine ⟨13195242375487144434618725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8796828250324762956412483 13195242375487144434618725)
                    ·
                      refine ⟨2474107945403839581491011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13195242375487144434618725 2474107945403839581491011)
                      ·
                        rfl

theorem cell23_4818308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_4818308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818308 prefixEnd_4818308 := by exact prefixLift 4818308
  have htrace : WordTrace (prefixWord ++ tailWord_4818308) baseStart_4818308 baseEnd_4818308 := by
    simpa [prefixWord, tailWord_4818308, baseEnd_4818308] using wordTrace_append hprefix tailTrace_4818308
  have hstable : (prefixWord ++ tailWord_4818308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818308).length < 2 ^ (prefixWord ++ tailWord_4818308).sum := by decide
  have hdescent : baseEnd_4818308 < baseStart_4818308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818311 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_4818311 : Nat := 118140960795 + 4818311 * 2 ^ 59
def prefixEnd_4818311 : Nat := 4983230072969 + 3 ^ 40 * 4818311 * 2
def baseEnd_4818311 : Nat := 2474109485845803069753497

theorem tailTrace_4818311 : CollatzResearch.WordTrace tailWord_4818311 prefixEnd_4818311 2474109485845803069753497 := by
  unfold tailWord_4818311
  simp only [CollatzResearch.WordTrace]
  refine ⟨175738239647089623849334787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117158826431393082566223191 175738239647089623849334787)
  ·
    refine ⟨263607359470634435774002181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175738239647089623849334787 263607359470634435774002181)
    ·
      refine ⟨49426379900743956707625409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 263607359470634435774002181 49426379900743956707625409)
      ·
        refine ⟨37069784925557967530719057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49426379900743956707625409 37069784925557967530719057)
        ·
          refine ⟨27802338694168475648039293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37069784925557967530719057 27802338694168475648039293)
          ·
            refine ⟨10425877010313178368014735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27802338694168475648039293 10425877010313178368014735)
            ·
              refine ⟨15638815515469767552022103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10425877010313178368014735 15638815515469767552022103)
              ·
                refine ⟨23458223273204651328033155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15638815515469767552022103 23458223273204651328033155)
                ·
                  refine ⟨35187334909806976992049733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23458223273204651328033155 35187334909806976992049733)
                  ·
                    refine ⟨6597625295588808186009325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35187334909806976992049733 6597625295588808186009325)
                    ·
                      refine ⟨2474109485845803069753497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6597625295588808186009325 2474109485845803069753497)
                      ·
                        rfl

theorem cell23_4818311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_4818311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818311 prefixEnd_4818311 := by exact prefixLift 4818311
  have htrace : WordTrace (prefixWord ++ tailWord_4818311) baseStart_4818311 baseEnd_4818311 := by
    simpa [prefixWord, tailWord_4818311, baseEnd_4818311] using wordTrace_append hprefix tailTrace_4818311
  have hstable : (prefixWord ++ tailWord_4818311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818311).length < 2 ^ (prefixWord ++ tailWord_4818311).sum := by decide
  have hdescent : baseEnd_4818311 < baseStart_4818311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818384 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 5]
def baseStart_4818384 : Nat := 118140960795 + 4818384 * 2 ^ 59
def prefixEnd_4818384 : Nat := 4983230072969 + 3 ^ 40 * 4818384 * 2
def baseEnd_4818384 : Nat := 2474146969933581284140661

theorem tailTrace_4818384 : CollatzResearch.WordTrace tailWord_4818384 prefixEnd_4818384 2474146969933581284140661 := by
  unfold tailWord_4818384
  simp only [CollatzResearch.WordTrace]
  refine ⟨87870451087912578658371103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117160601450550104877828137 87870451087912578658371103)
  ·
    refine ⟨131805676631868867987556655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87870451087912578658371103 131805676631868867987556655)
    ·
      refine ⟨197708514947803301981334983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131805676631868867987556655 197708514947803301981334983)
      ·
        refine ⟨296562772421704952972002475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197708514947803301981334983 296562772421704952972002475)
        ·
          refine ⟨444844158632557429458003713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296562772421704952972002475 444844158632557429458003713)
          ·
            refine ⟨333633118974418072093502785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444844158632557429458003713 333633118974418072093502785)
            ·
              refine ⟨250224839230813554070127089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333633118974418072093502785 250224839230813554070127089)
              ·
                refine ⟨187668629423110165552595317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250224839230813554070127089 187668629423110165552595317)
                ·
                  refine ⟨17593934008416578020555811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 187668629423110165552595317 17593934008416578020555811)
                  ·
                    refine ⟨26390901012624867030833717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17593934008416578020555811 26390901012624867030833717)
                    ·
                      refine ⟨2474146969933581284140661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26390901012624867030833717 2474146969933581284140661)
                      ·
                        rfl

theorem cell23_4818384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_4818384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818384 prefixEnd_4818384 := by exact prefixLift 4818384
  have htrace : WordTrace (prefixWord ++ tailWord_4818384) baseStart_4818384 baseEnd_4818384 := by
    simpa [prefixWord, tailWord_4818384, baseEnd_4818384] using wordTrace_append hprefix tailTrace_4818384
  have hstable : (prefixWord ++ tailWord_4818384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818384).length < 2 ^ (prefixWord ++ tailWord_4818384).sum := by decide
  have hdescent : baseEnd_4818384 < baseStart_4818384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818401 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_4818401 : Nat := 118140960795 + 4818401 * 2 ^ 59
def prefixEnd_4818401 : Nat := 4983230072969 + 3 ^ 40 * 4818401 * 2
def baseEnd_4818401 : Nat := 2474155699104707717628083

theorem tailTrace_4818401 : CollatzResearch.WordTrace tailWord_4818401 prefixEnd_4818401 2474155699104707717628083 := by
  unfold tailWord_4818401
  simp only [CollatzResearch.WordTrace]
  refine ⟨175741522216763569220111057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117161014811175712813407371 175741522216763569220111057)
  ·
    refine ⟨131806141662572676915083293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175741522216763569220111057 131806141662572676915083293)
    ·
      refine ⟨49427303123464753843156235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131806141662572676915083293 49427303123464753843156235)
      ·
        refine ⟨74140954685197130764734353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49427303123464753843156235 74140954685197130764734353)
        ·
          refine ⟨55605716013897848073550765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74140954685197130764734353 55605716013897848073550765)
          ·
            refine ⟨20852143505211693027581537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55605716013897848073550765 20852143505211693027581537)
            ·
              refine ⟨15639107628908769770686153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20852143505211693027581537 15639107628908769770686153)
              ·
                refine ⟨11729330721681577328014615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15639107628908769770686153 11729330721681577328014615)
                ·
                  refine ⟨17593996082522365992021923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11729330721681577328014615 17593996082522365992021923)
                  ·
                    refine ⟨26390994123783548988032885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17593996082522365992021923 26390994123783548988032885)
                    ·
                      refine ⟨2474155699104707717628083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26390994123783548988032885 2474155699104707717628083)
                      ·
                        rfl

theorem cell23_4818401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_4818401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818401 prefixEnd_4818401 := by exact prefixLift 4818401
  have htrace : WordTrace (prefixWord ++ tailWord_4818401) baseStart_4818401 baseEnd_4818401 := by
    simpa [prefixWord, tailWord_4818401, baseEnd_4818401] using wordTrace_append hprefix tailTrace_4818401
  have hstable : (prefixWord ++ tailWord_4818401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818401).length < 2 ^ (prefixWord ++ tailWord_4818401).sum := by decide
  have hdescent : baseEnd_4818401 < baseStart_4818401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818408 : List Nat := [2, 1, 4, 1, 1, 2, 3, 3, 2, 4]
def baseStart_4818408 : Nat := 118140960795 + 4818408 * 2 ^ 59
def prefixEnd_4818408 : Nat := 4983230072969 + 3 ^ 40 * 4818408 * 2
def baseEnd_4818408 : Nat := 824719764489763063413517

theorem tailTrace_4818408 : CollatzResearch.WordTrace tailWord_4818408 prefixEnd_4818408 824719764489763063413517 := by
  unfold tailWord_4818408
  simp only [CollatzResearch.WordTrace]
  refine ⟨87870888763869104707807939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117161185018492139610410585 87870888763869104707807939)
  ·
    refine ⟨131806333145803657061711909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87870888763869104707807939 131806333145803657061711909)
    ·
      refine ⟨24713687464838185699070983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131806333145803657061711909 24713687464838185699070983)
      ·
        refine ⟨37070531197257278548606475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24713687464838185699070983 37070531197257278548606475)
        ·
          refine ⟨55605796795885917822909713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37070531197257278548606475 55605796795885917822909713)
          ·
            refine ⟨41704347596914438367182285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55605796795885917822909713 41704347596914438367182285)
            ·
              refine ⟨15639130348842914387693357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41704347596914438367182285 15639130348842914387693357)
              ·
                refine ⟨5864673880816092895385009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15639130348842914387693357 5864673880816092895385009)
                ·
                  refine ⟨4398505410612069671538757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5864673880816092895385009 4398505410612069671538757)
                  ·
                    refine ⟨824719764489763063413517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4398505410612069671538757 824719764489763063413517)
                    ·
                      rfl

theorem cell23_4818408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_4818408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818408 prefixEnd_4818408 := by exact prefixLift 4818408
  have htrace : WordTrace (prefixWord ++ tailWord_4818408) baseStart_4818408 baseEnd_4818408 := by
    simpa [prefixWord, tailWord_4818408, baseEnd_4818408] using wordTrace_append hprefix tailTrace_4818408
  have hstable : (prefixWord ++ tailWord_4818408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818408).length < 2 ^ (prefixWord ++ tailWord_4818408).sum := by decide
  have hdescent : baseEnd_4818408 < baseStart_4818408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818465 : List Nat := [1, 2, 3, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_4818465 : Nat := 118140960795 + 4818465 * 2 ^ 59
def prefixEnd_4818465 : Nat := 4983230072969 + 3 ^ 40 * 4818465 * 2
def baseEnd_4818465 : Nat := 2474188561866595467227789

theorem tailTrace_4818465 : CollatzResearch.WordTrace tailWord_4818465 prefixEnd_4818465 2474188561866595467227789 := by
  unfold tailWord_4818465
  simp only [CollatzResearch.WordTrace]
  refine ⟨175743856488531708150440849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117162570992354472100293899 175743856488531708150440849)
  ·
    refine ⟨131807892366398781112830637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175743856488531708150440849 131807892366398781112830637)
    ·
      refine ⟨49427959637399542917311489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131807892366398781112830637 49427959637399542917311489)
      ·
        refine ⟨37070969728049657187983617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49427959637399542917311489 37070969728049657187983617)
        ·
          refine ⟨27803227296037242890987713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37070969728049657187983617 27803227296037242890987713)
          ·
            refine ⟨20852420472027932168240785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27803227296037242890987713 20852420472027932168240785)
            ·
              refine ⟨15639315354020949126180589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20852420472027932168240785 15639315354020949126180589)
              ·
                refine ⟨5864743257757855922317721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15639315354020949126180589 5864743257757855922317721)
                ·
                  refine ⟨4398557443318391941738291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5864743257757855922317721 4398557443318391941738291)
                  ·
                    refine ⟨6597836164977587912607437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4398557443318391941738291 6597836164977587912607437)
                    ·
                      refine ⟨2474188561866595467227789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6597836164977587912607437 2474188561866595467227789)
                      ·
                        rfl

theorem cell23_4818465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_4818465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818465 prefixEnd_4818465 := by exact prefixLift 4818465
  have htrace : WordTrace (prefixWord ++ tailWord_4818465) baseStart_4818465 baseEnd_4818465 := by
    simpa [prefixWord, tailWord_4818465, baseEnd_4818465] using wordTrace_append hprefix tailTrace_4818465
  have hstable : (prefixWord ++ tailWord_4818465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818465).length < 2 ^ (prefixWord ++ tailWord_4818465).sum := by decide
  have hdescent : baseEnd_4818465 < baseStart_4818465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818486 : List Nat := [5, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_4818486 : Nat := 118140960795 + 4818486 * 2 ^ 59
def prefixEnd_4818486 : Nat := 4983230072969 + 3 ^ 40 * 4818486 * 2
def baseEnd_4818486 : Nat := 2474199344960339885065193

theorem tailTrace_4818486 : CollatzResearch.WordTrace tailWord_4818486 prefixEnd_4818486 2474199344960339885065193 := by
  unfold tailWord_4818486
  simp only [CollatzResearch.WordTrace]
  refine ⟨10984038901340976796059707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117163081614303752491303541 10984038901340976796059707)
  ·
    refine ⟨16476058352011465194089561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10984038901340976796059707 16476058352011465194089561)
    ·
      refine ⟨12357043764008598895567171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16476058352011465194089561 12357043764008598895567171)
      ·
        refine ⟨18535565646012898343350757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12357043764008598895567171 18535565646012898343350757)
        ·
          refine ⟨3475418558627418439378267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18535565646012898343350757 3475418558627418439378267)
          ·
            refine ⟨5213127837941127659067401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475418558627418439378267 5213127837941127659067401)
            ·
              refine ⟨3909845878455845744300551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5213127837941127659067401 3909845878455845744300551)
              ·
                refine ⟨5864768817683768616450827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909845878455845744300551 5864768817683768616450827)
                ·
                  refine ⟨8797153226525652924676241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5864768817683768616450827 8797153226525652924676241)
                  ·
                    refine ⟨6597864919894239693507181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8797153226525652924676241 6597864919894239693507181)
                    ·
                      refine ⟨2474199344960339885065193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6597864919894239693507181 2474199344960339885065193)
                      ·
                        rfl

theorem cell23_4818486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_4818486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818486 prefixEnd_4818486 := by exact prefixLift 4818486
  have htrace : WordTrace (prefixWord ++ tailWord_4818486) baseStart_4818486 baseEnd_4818486 := by
    simpa [prefixWord, tailWord_4818486, baseEnd_4818486] using wordTrace_append hprefix tailTrace_4818486
  have hstable : (prefixWord ++ tailWord_4818486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818486).length < 2 ^ (prefixWord ++ tailWord_4818486).sum := by decide
  have hdescent : baseEnd_4818486 < baseStart_4818486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818492 : List Nat := [2, 2, 2, 2, 4, 1, 1, 3, 1, 3, 2]
def baseStart_4818492 : Nat := 118140960795 + 4818492 * 2 ^ 59
def prefixEnd_4818492 : Nat := 4983230072969 + 3 ^ 40 * 4818492 * 2
def baseEnd_4818492 : Nat := 2474202425844266861590165

theorem tailTrace_4818492 : CollatzResearch.WordTrace tailWord_4818492 prefixEnd_4818492 2474202425844266861590165 := by
  unfold tailWord_4818492
  simp only [CollatzResearch.WordTrace]
  refine ⟨87872420629716945880836865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117163227506289261174449153 87872420629716945880836865)
  ·
    refine ⟨65904315472287709410627649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87872420629716945880836865 65904315472287709410627649)
    ·
      refine ⟨49428236604215782057970737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65904315472287709410627649 49428236604215782057970737)
      ·
        refine ⟨37071177453161836543478053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49428236604215782057970737 37071177453161836543478053)
        ·
          refine ⟨6950845772467844351902135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37071177453161836543478053 6950845772467844351902135)
          ·
            refine ⟨10426268658701766527853203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6950845772467844351902135 10426268658701766527853203)
            ·
              refine ⟨15639402988052649791779805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10426268658701766527853203 15639402988052649791779805)
              ·
                refine ⟨5864776120519743671917427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15639402988052649791779805 5864776120519743671917427)
                ·
                  refine ⟨8797164180779615507876141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5864776120519743671917427 8797164180779615507876141)
                  ·
                    refine ⟨3298936567792355815453553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8797164180779615507876141 3298936567792355815453553)
                    ·
                      refine ⟨2474202425844266861590165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3298936567792355815453553 2474202425844266861590165)
                      ·
                        rfl

theorem cell23_4818492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_4818492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818492 prefixEnd_4818492 := by exact prefixLift 4818492
  have htrace : WordTrace (prefixWord ++ tailWord_4818492) baseStart_4818492 baseEnd_4818492 := by
    simpa [prefixWord, tailWord_4818492, baseEnd_4818492] using wordTrace_append hprefix tailTrace_4818492
  have hstable : (prefixWord ++ tailWord_4818492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818492).length < 2 ^ (prefixWord ++ tailWord_4818492).sum := by decide
  have hdescent : baseEnd_4818492 < baseStart_4818492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818501 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_4818501 : Nat := 118140960795 + 4818501 * 2 ^ 59
def prefixEnd_4818501 : Nat := 4983230072969 + 3 ^ 40 * 4818501 * 2
def baseEnd_4818501 : Nat := 2474207047170157326377623

theorem tailTrace_4818501 : CollatzResearch.WordTrace tailWord_4818501 prefixEnd_4818501 2474207047170157326377623 := by
  unfold tailWord_4818501
  simp only [CollatzResearch.WordTrace]
  refine ⟨175745169516401286298751357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117163446344267524199167571 175745169516401286298751357)
  ·
    refine ⟨65904438568650482362031759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175745169516401286298751357 65904438568650482362031759)
    ·
      refine ⟨98856657852975723543047639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65904438568650482362031759 98856657852975723543047639)
      ·
        refine ⟨148284986779463585314571459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98856657852975723543047639 148284986779463585314571459)
        ·
          refine ⟨222427480169195377971857189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148284986779463585314571459 222427480169195377971857189)
          ·
            refine ⟨41705152531724133369723223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222427480169195377971857189 41705152531724133369723223)
            ·
              refine ⟨62557728797586200054584835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41705152531724133369723223 62557728797586200054584835)
              ·
                refine ⟨93836593196379300081877253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62557728797586200054584835 93836593196379300081877253)
                ·
                  refine ⟨17594361224321118765351985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93836593196379300081877253 17594361224321118765351985)
                  ·
                    refine ⟨13195770918240839074013989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17594361224321118765351985 13195770918240839074013989)
                    ·
                      refine ⟨2474207047170157326377623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13195770918240839074013989 2474207047170157326377623)
                      ·
                        rfl

theorem cell23_4818501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_4818501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818501 prefixEnd_4818501 := by exact prefixLift 4818501
  have htrace : WordTrace (prefixWord ++ tailWord_4818501) baseStart_4818501 baseEnd_4818501 := by
    simpa [prefixWord, tailWord_4818501, baseEnd_4818501] using wordTrace_append hprefix tailTrace_4818501
  have hstable : (prefixWord ++ tailWord_4818501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818501).length < 2 ^ (prefixWord ++ tailWord_4818501).sum := by decide
  have hdescent : baseEnd_4818501 < baseStart_4818501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818551 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_4818551 : Nat := 118140960795 + 4818551 * 2 ^ 59
def prefixEnd_4818551 : Nat := 4983230072969 + 3 ^ 40 * 4818551 * 2
def baseEnd_4818551 : Nat := 2474232721202882130752393

theorem tailTrace_4818551 : CollatzResearch.WordTrace tailWord_4818551 prefixEnd_4818551 2474232721202882130752393 := by
  unfold tailWord_4818551
  simp only [CollatzResearch.WordTrace]
  refine ⟨175746993166220144838071507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117164662110813429892047671 175746993166220144838071507)
  ·
    refine ⟨263620489749330217257107261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175746993166220144838071507 263620489749330217257107261)
    ·
      refine ⟨98857683655998831471415223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263620489749330217257107261 98857683655998831471415223)
      ·
        refine ⟨148286525483998247207122835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98857683655998831471415223 148286525483998247207122835)
        ·
          refine ⟨222429788225997370810684253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148286525483998247207122835 222429788225997370810684253)
          ·
            refine ⟨83411170584749014054006595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222429788225997370810684253 83411170584749014054006595)
            ·
              refine ⟨125116755877123521081009893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83411170584749014054006595 125116755877123521081009893)
              ·
                refine ⟨23459391726960660202689355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125116755877123521081009893 23459391726960660202689355)
                ·
                  refine ⟨35189087590440990304034033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23459391726960660202689355 35189087590440990304034033)
                  ·
                    refine ⟨26391815692830742728025525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35189087590440990304034033 26391815692830742728025525)
                    ·
                      refine ⟨2474232721202882130752393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26391815692830742728025525 2474232721202882130752393)
                      ·
                        rfl

theorem cell23_4818551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_4818551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818551 prefixEnd_4818551 := by exact prefixLift 4818551
  have htrace : WordTrace (prefixWord ++ tailWord_4818551) baseStart_4818551 baseEnd_4818551 := by
    simpa [prefixWord, tailWord_4818551, baseEnd_4818551] using wordTrace_append hprefix tailTrace_4818551
  have hstable : (prefixWord ++ tailWord_4818551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818551).length < 2 ^ (prefixWord ++ tailWord_4818551).sum := by decide
  have hdescent : baseEnd_4818551 < baseStart_4818551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818581 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_4818581 : Nat := 118140960795 + 4818581 * 2 ^ 59
def prefixEnd_4818581 : Nat := 4983230072969 + 3 ^ 40 * 4818581 * 2
def baseEnd_4818581 : Nat := 2474248125622517013377255

theorem tailTrace_4818581 : CollatzResearch.WordTrace tailWord_4818581 prefixEnd_4818581 2474248125622517013377255 := by
  unfold tailWord_4818581
  simp only [CollatzResearch.WordTrace]
  refine ⟨175748087356111459961663597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117165391570740973307775731 175748087356111459961663597)
  ·
    refine ⟨65905532758541797485623849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175748087356111459961663597 65905532758541797485623849)
    ·
      refine ⟨49429149568906348114217887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65905532758541797485623849 49429149568906348114217887)
      ·
        refine ⟨74143724353359522171326831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49429149568906348114217887 74143724353359522171326831)
        ·
          refine ⟨111215586530039283256990247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74143724353359522171326831 111215586530039283256990247)
          ·
            refine ⟨166823379795058924885485371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111215586530039283256990247 166823379795058924885485371)
            ·
              refine ⟨250235069692588387328228057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166823379795058924885485371 250235069692588387328228057)
              ·
                refine ⟨187676302269441290496171043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250235069692588387328228057 187676302269441290496171043)
                ·
                  refine ⟨281514453404161935744256565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187676302269441290496171043 281514453404161935744256565)
                  ·
                    refine ⟨26391980006640181476024053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 281514453404161935744256565 26391980006640181476024053)
                    ·
                      refine ⟨2474248125622517013377255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26391980006640181476024053 2474248125622517013377255)
                      ·
                        rfl

theorem cell23_4818581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_4818581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818581 prefixEnd_4818581 := by exact prefixLift 4818581
  have htrace : WordTrace (prefixWord ++ tailWord_4818581) baseStart_4818581 baseEnd_4818581 := by
    simpa [prefixWord, tailWord_4818581, baseEnd_4818581] using wordTrace_append hprefix tailTrace_4818581
  have hstable : (prefixWord ++ tailWord_4818581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818581).length < 2 ^ (prefixWord ++ tailWord_4818581).sum := by decide
  have hdescent : baseEnd_4818581 < baseStart_4818581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818615 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 3]
def baseStart_4818615 : Nat := 118140960795 + 4818615 * 2 ^ 59
def prefixEnd_4818615 : Nat := 4983230072969 + 3 ^ 40 * 4818615 * 2
def baseEnd_4818615 : Nat := 2474265583964769880352099

theorem tailTrace_4818615 : CollatzResearch.WordTrace tailWord_4818615 prefixEnd_4818615 2474265583964769880352099 := by
  unfold tailWord_4818615
  simp only [CollatzResearch.WordTrace]
  refine ⟨175749327437988283768401299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117166218291992189178934199 175749327437988283768401299)
  ·
    refine ⟨263623991156982425652601949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175749327437988283768401299 263623991156982425652601949)
    ·
      refine ⟨98858996683868409619725731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263623991156982425652601949 98858996683868409619725731)
      ·
        refine ⟨148288495025802614429588597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98858996683868409619725731 148288495025802614429588597)
        ·
          refine ⟨13902046408668995102773931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148288495025802614429588597 13902046408668995102773931)
          ·
            refine ⟨20853069613003492654160897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13902046408668995102773931 20853069613003492654160897)
            ·
              refine ⟨15639802209752619490620673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20853069613003492654160897 15639802209752619490620673)
              ·
                refine ⟨11729851657314464617965505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15639802209752619490620673 11729851657314464617965505)
                ·
                  refine ⟨8797388742985848463474129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11729851657314464617965505 8797388742985848463474129)
                  ·
                    refine ⟨6598041557239386347605597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8797388742985848463474129 6598041557239386347605597)
                    ·
                      refine ⟨2474265583964769880352099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6598041557239386347605597 2474265583964769880352099)
                      ·
                        rfl

theorem cell23_4818615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_4818615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818615 prefixEnd_4818615 := by exact prefixLift 4818615
  have htrace : WordTrace (prefixWord ++ tailWord_4818615) baseStart_4818615 baseEnd_4818615 := by
    simpa [prefixWord, tailWord_4818615, baseEnd_4818615] using wordTrace_append hprefix tailTrace_4818615
  have hstable : (prefixWord ++ tailWord_4818615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818615).length < 2 ^ (prefixWord ++ tailWord_4818615).sum := by decide
  have hdescent : baseEnd_4818615 < baseStart_4818615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818618 : List Nat := [3, 1, 1, 1, 2, 4, 1, 4, 6]
def baseStart_4818618 : Nat := 118140960795 + 4818618 * 2 ^ 59
def prefixEnd_4818618 : Nat := 4983230072969 + 3 ^ 40 * 4818618 * 2
def baseEnd_4818618 : Nat := 274918569378525929846065

theorem tailTrace_4818618 : CollatzResearch.WordTrace tailWord_4818618 prefixEnd_4818618 274918569378525929846065 := by
  unfold tailWord_4818618
  simp only [CollatzResearch.WordTrace]
  refine ⟨43937359214244353820190127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117166291237984943520507005 43937359214244353820190127)
  ·
    refine ⟨65906038821366530730285191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43937359214244353820190127 65906038821366530730285191)
    ·
      refine ⟨98859058232049796095427787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65906038821366530730285191 98859058232049796095427787)
      ·
        refine ⟨148288587348074694143141681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98859058232049796095427787 148288587348074694143141681)
        ·
          refine ⟨111216440511056020607356261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148288587348074694143141681 111216440511056020607356261)
          ·
            refine ⟨20853082595823003863879299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111216440511056020607356261 20853082595823003863879299)
            ·
              refine ⟨31279623893734505795818949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20853082595823003863879299 31279623893734505795818949)
              ·
                refine ⟨5864929480075219836716053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31279623893734505795818949 5864929480075219836716053)
                ·
                  refine ⟨274918569378525929846065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5864929480075219836716053 274918569378525929846065)
                  ·
                    rfl

theorem cell23_4818618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_4818618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818618 prefixEnd_4818618 := by exact prefixLift 4818618
  have htrace : WordTrace (prefixWord ++ tailWord_4818618) baseStart_4818618 baseEnd_4818618 := by
    simpa [prefixWord, tailWord_4818618, baseEnd_4818618] using wordTrace_append hprefix tailTrace_4818618
  have hstable : (prefixWord ++ tailWord_4818618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818618).length < 2 ^ (prefixWord ++ tailWord_4818618).sum := by decide
  have hdescent : baseEnd_4818618 < baseStart_4818618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818646 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_4818646 : Nat := 118140960795 + 4818646 * 2 ^ 59
def prefixEnd_4818646 : Nat := 4983230072969 + 3 ^ 40 * 4818646 * 2
def baseEnd_4818646 : Nat := 2474281501865059259064457

theorem tailTrace_4818646 : CollatzResearch.WordTrace tailWord_4818646 prefixEnd_4818646 2474281501865059259064457 := by
  unfold tailWord_4818646
  simp only [CollatzResearch.WordTrace]
  refine ⟨10984403631304748503923737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117166972067250650708519861 10984403631304748503923737)
  ·
    refine ⟨8238302723478561377942803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10984403631304748503923737 8238302723478561377942803)
    ·
      refine ⟨12357454085217842066914205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8238302723478561377942803 12357454085217842066914205)
      ·
        refine ⟨4634045281956690775092827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12357454085217842066914205 4634045281956690775092827)
        ·
          refine ⟨6951067922935036162639241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4634045281956690775092827 6951067922935036162639241)
          ·
            refine ⟨5213300942201277121979431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6951067922935036162639241 5213300942201277121979431)
            ·
              refine ⟨7819951413301915682969147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5213300942201277121979431 7819951413301915682969147)
              ·
                refine ⟨11729927119952873524453721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7819951413301915682969147 11729927119952873524453721)
                ·
                  refine ⟨8797445339964655143340291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11729927119952873524453721 8797445339964655143340291)
                  ·
                    refine ⟨13196168009946982715010437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8797445339964655143340291 13196168009946982715010437)
                    ·
                      refine ⟨2474281501865059259064457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13196168009946982715010437 2474281501865059259064457)
                      ·
                        rfl

theorem cell23_4818646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_4818646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818646 prefixEnd_4818646 := by exact prefixLift 4818646
  have htrace : WordTrace (prefixWord ++ tailWord_4818646) baseStart_4818646 baseEnd_4818646 := by
    simpa [prefixWord, tailWord_4818646, baseEnd_4818646] using wordTrace_append hprefix tailTrace_4818646
  have hstable : (prefixWord ++ tailWord_4818646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818646).length < 2 ^ (prefixWord ++ tailWord_4818646).sum := by decide
  have hdescent : baseEnd_4818646 < baseStart_4818646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818648 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 3, 5]
def baseStart_4818648 : Nat := 118140960795 + 4818648 * 2 ^ 59
def prefixEnd_4818648 : Nat := 4983230072969 + 3 ^ 40 * 4818648 * 2
def baseEnd_4818648 : Nat := 824760842942122750413149

theorem tailTrace_4818648 : CollatzResearch.WordTrace tailWord_4818648 prefixEnd_4818648 824760842942122750413149 := by
  unfold tailWord_4818648
  simp only [CollatzResearch.WordTrace]
  refine ⟨87875265523434365202176299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117167020697912486936235065 87875265523434365202176299)
  ·
    refine ⟨131812898285151547803264449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87875265523434365202176299 131812898285151547803264449)
    ·
      refine ⟨98859673713863660852448337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131812898285151547803264449 98859673713863660852448337)
      ·
        refine ⟨74144755285397745639336253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98859673713863660852448337 74144755285397745639336253)
        ·
          refine ⟨27804283232024154614751095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74144755285397745639336253 27804283232024154614751095)
          ·
            refine ⟨41706424848036231922126643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27804283232024154614751095 41706424848036231922126643)
            ·
              refine ⟨62559637272054347883189965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41706424848036231922126643 62559637272054347883189965)
              ·
                refine ⟨23459863977020380456196237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62559637272054347883189965 23459863977020380456196237)
                ·
                  refine ⟨8797448991382642671073589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23459863977020380456196237 8797448991382642671073589)
                  ·
                    refine ⟨824760842942122750413149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8797448991382642671073589 824760842942122750413149)
                    ·
                      rfl

theorem cell23_4818648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_4818648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818648 prefixEnd_4818648 := by exact prefixLift 4818648
  have htrace : WordTrace (prefixWord ++ tailWord_4818648) baseStart_4818648 baseEnd_4818648 := by
    simpa [prefixWord, tailWord_4818648, baseEnd_4818648] using wordTrace_append hprefix tailTrace_4818648
  have hstable : (prefixWord ++ tailWord_4818648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818648).length < 2 ^ (prefixWord ++ tailWord_4818648).sum := by decide
  have hdescent : baseEnd_4818648 < baseStart_4818648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818655 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 1, 5, 2]
def baseStart_4818655 : Nat := 118140960795 + 4818655 * 2 ^ 59
def prefixEnd_4818655 : Nat := 4983230072969 + 3 ^ 40 * 4818655 * 2
def baseEnd_4818655 : Nat := 2474286123190949723851915

theorem tailTrace_4818655 : CollatzResearch.WordTrace tailWord_4818655 prefixEnd_4818655 2474286123190949723851915 := by
  unfold tailWord_4818655
  simp only [CollatzResearch.WordTrace]
  refine ⟨175750786357843370599857419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117167190905228913733238279 175750786357843370599857419)
  ·
    refine ⟨263626179536765055899786129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175750786357843370599857419 263626179536765055899786129)
    ·
      refine ⟨197719634652573791924839597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263626179536765055899786129 197719634652573791924839597)
      ·
        refine ⟨74144862994715171971814849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197719634652573791924839597 74144862994715171971814849)
        ·
          refine ⟨55608647246036378978861137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74144862994715171971814849 55608647246036378978861137)
          ·
            refine ⟨41706485434527284234145853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55608647246036378978861137 41706485434527284234145853)
            ·
              refine ⟨15639932037947731587804695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41706485434527284234145853 15639932037947731587804695)
              ·
                refine ⟨23459898056921597381707043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15639932037947731587804695 23459898056921597381707043)
                ·
                  refine ⟨35189847085382396072560565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23459898056921597381707043 35189847085382396072560565)
                  ·
                    refine ⟨3299048164254599631802553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35189847085382396072560565 3299048164254599631802553)
                    ·
                      refine ⟨2474286123190949723851915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3299048164254599631802553 2474286123190949723851915)
                      ·
                        rfl

theorem cell23_4818655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_4818655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818655 prefixEnd_4818655 := by exact prefixLift 4818655
  have htrace : WordTrace (prefixWord ++ tailWord_4818655) baseStart_4818655 baseEnd_4818655 := by
    simpa [prefixWord, tailWord_4818655, baseEnd_4818655] using wordTrace_append hprefix tailTrace_4818655
  have hstable : (prefixWord ++ tailWord_4818655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818655).length < 2 ^ (prefixWord ++ tailWord_4818655).sum := by decide
  have hdescent : baseEnd_4818655 < baseStart_4818655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818688 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 5]
def baseStart_4818688 : Nat := 118140960795 + 4818688 * 2 ^ 59
def prefixEnd_4818688 : Nat := 4983230072969 + 3 ^ 40 * 4818688 * 2
def baseEnd_4818688 : Nat := 2474303068052548094739263

theorem tailTrace_4818688 : CollatzResearch.WordTrace tailWord_4818688 prefixEnd_4818688 2474303068052548094739263 := by
  unfold tailWord_4818688
  simp only [CollatzResearch.WordTrace]
  refine ⟨87875994983361908617904359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117167993311149211490539145 87875994983361908617904359)
  ·
    refine ⟨131813992475042862926856539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87875994983361908617904359 131813992475042862926856539)
    ·
      refine ⟨197720988712564294390284809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131813992475042862926856539 197720988712564294390284809)
      ·
        refine ⟨148290741534423220792713607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197720988712564294390284809 148290741534423220792713607)
        ·
          refine ⟨222436112301634831189070411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148290741534423220792713607 222436112301634831189070411)
          ·
            refine ⟨333654168452452246783605617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222436112301634831189070411 333654168452452246783605617)
            ·
              refine ⟨250240626339339185087704213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333654168452452246783605617 250240626339339185087704213)
              ·
                refine ⟨11730029359656524300986135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 250240626339339185087704213 11730029359656524300986135)
                ·
                  refine ⟨17595044039484786451479203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11730029359656524300986135 17595044039484786451479203)
                  ·
                    refine ⟨26392566059227179677218805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17595044039484786451479203 26392566059227179677218805)
                    ·
                      refine ⟨2474303068052548094739263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26392566059227179677218805 2474303068052548094739263)
                      ·
                        rfl

theorem cell23_4818688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_4818688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818688 prefixEnd_4818688 := by exact prefixLift 4818688
  have htrace : WordTrace (prefixWord ++ tailWord_4818688) baseStart_4818688 baseEnd_4818688 := by
    simpa [prefixWord, tailWord_4818688, baseEnd_4818688] using wordTrace_append hprefix tailTrace_4818688
  have hstable : (prefixWord ++ tailWord_4818688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818688).length < 2 ^ (prefixWord ++ tailWord_4818688).sum := by decide
  have hdescent : baseEnd_4818688 < baseStart_4818688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818722 : List Nat := [3, 3, 1, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_4818722 : Nat := 118140960795 + 4818722 * 2 ^ 59
def prefixEnd_4818722 : Nat := 4983230072969 + 3 ^ 40 * 4818722 * 2
def baseEnd_4818722 : Nat := 2474320526394800961714107

theorem tailTrace_4818722 : CollatzResearch.WordTrace tailWord_4818722 prefixEnd_4818722 2474320526394800961714107 := by
  unfold tailWord_4818722
  simp only [CollatzResearch.WordTrace]
  refine ⟨43938307512150160260636605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117168820032400427361697613 43938307512150160260636605)
  ·
    refine ⟨16476865317056310097738727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43938307512150160260636605 16476865317056310097738727)
    ·
      refine ⟨24715297975584465146608091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16476865317056310097738727 24715297975584465146608091)
      ·
        refine ⟨37072946963376697719912137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24715297975584465146608091 37072946963376697719912137)
        ·
          refine ⟨27804710222532523289934103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37072946963376697719912137 27804710222532523289934103)
          ·
            refine ⟨41707065333798784934901155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27804710222532523289934103 41707065333798784934901155)
            ·
              refine ⟨62560598000698177402351733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41707065333798784934901155 62560598000698177402351733)
              ·
                refine ⟨5865056062565454131470475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62560598000698177402351733 5865056062565454131470475)
                ·
                  refine ⟨8797584093848181197205713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5865056062565454131470475 8797584093848181197205713)
                  ·
                    refine ⟨6598188070386135897904285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8797584093848181197205713 6598188070386135897904285)
                    ·
                      refine ⟨2474320526394800961714107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6598188070386135897904285 2474320526394800961714107)
                      ·
                        rfl

theorem cell23_4818722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_4818722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818722 prefixEnd_4818722 := by exact prefixLift 4818722
  have htrace : WordTrace (prefixWord ++ tailWord_4818722) baseStart_4818722 baseEnd_4818722 := by
    simpa [prefixWord, tailWord_4818722, baseEnd_4818722] using wordTrace_append hprefix tailTrace_4818722
  have hstable : (prefixWord ++ tailWord_4818722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818722).length < 2 ^ (prefixWord ++ tailWord_4818722).sum := by decide
  have hdescent : baseEnd_4818722 < baseStart_4818722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818742 : List Nat := [5, 1, 2, 2, 1, 2, 2, 8]
def baseStart_4818742 : Nat := 118140960795 + 4818742 * 2 ^ 59
def prefixEnd_4818742 : Nat := 4983230072969 + 3 ^ 40 * 4818742 * 2
def baseEnd_4818742 : Nat := 91641881333625588276445

theorem tailTrace_4818742 : CollatzResearch.WordTrace tailWord_4818742 prefixEnd_4818742 91641881333625588276445 := by
  unfold tailWord_4818742
  simp only [CollatzResearch.WordTrace]
  refine ⟨10984622469283011528642155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117169306339018789638849653 10984622469283011528642155)
  ·
    refine ⟨16476933703924517292963233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10984622469283011528642155 16476933703924517292963233)
    ·
      refine ⟨12357700277943387969722425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16476933703924517292963233 12357700277943387969722425)
      ·
        refine ⟨9268275208457540977291819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12357700277943387969722425 9268275208457540977291819)
        ·
          refine ⟨13902412812686311465937729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9268275208457540977291819 13902412812686311465937729)
          ·
            refine ⟨10426809609514733599453297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13902412812686311465937729 10426809609514733599453297)
            ·
              refine ⟨7820107207136050199589973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10426809609514733599453297 7820107207136050199589973)
              ·
                refine ⟨91641881333625588276445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7820107207136050199589973 91641881333625588276445)
                ·
                  rfl

theorem cell23_4818742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_4818742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818742 prefixEnd_4818742 := by exact prefixLift 4818742
  have htrace : WordTrace (prefixWord ++ tailWord_4818742) baseStart_4818742 baseEnd_4818742 := by
    simpa [prefixWord, tailWord_4818742, baseEnd_4818742] using wordTrace_append hprefix tailTrace_4818742
  have hstable : (prefixWord ++ tailWord_4818742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818742).length < 2 ^ (prefixWord ++ tailWord_4818742).sum := by decide
  have hdescent : baseEnd_4818742 < baseStart_4818742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818762 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 3, 3, 2]
def baseStart_4818762 : Nat := 118140960795 + 4818762 * 2 ^ 59
def prefixEnd_4818762 : Nat := 4983230072969 + 3 ^ 40 * 4818762 * 2
def baseEnd_4818762 : Nat := 2474341065620980805213923

theorem tailTrace_4818762 : CollatzResearch.WordTrace tailWord_4818762 prefixEnd_4818762 2474341065620980805213923 := by
  unfold tailWord_4818762
  simp only [CollatzResearch.WordTrace]
  refine ⟨43938672242113931968500635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117169792645637151916001693 43938672242113931968500635)
  ·
    refine ⟨65908008363170897952750953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43938672242113931968500635 65908008363170897952750953)
    ·
      refine ⟨49431006272378173464563215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65908008363170897952750953 49431006272378173464563215)
      ·
        refine ⟨74146509408567260196844823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49431006272378173464563215 74146509408567260196844823)
        ·
          refine ⟨111219764112850890295267235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74146509408567260196844823 111219764112850890295267235)
          ·
            refine ⟨166829646169276335442900853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111219764112850890295267235 166829646169276335442900853)
            ·
              refine ⟨15640279328369656447771955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166829646169276335442900853 15640279328369656447771955)
              ·
                refine ⟨23460418992554484671657933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15640279328369656447771955 23460418992554484671657933)
                ·
                  refine ⟨8797657122207931751871725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23460418992554484671657933 8797657122207931751871725)
                  ·
                    refine ⟨3299121420827974406951897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8797657122207931751871725 3299121420827974406951897)
                    ·
                      refine ⟨2474341065620980805213923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3299121420827974406951897 2474341065620980805213923)
                      ·
                        rfl

theorem cell23_4818762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_4818762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818762 prefixEnd_4818762 := by exact prefixLift 4818762
  have htrace : WordTrace (prefixWord ++ tailWord_4818762) baseStart_4818762 baseEnd_4818762 := by
    simpa [prefixWord, tailWord_4818762, baseEnd_4818762] using wordTrace_append hprefix tailTrace_4818762
  have hstable : (prefixWord ++ tailWord_4818762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818762).length < 2 ^ (prefixWord ++ tailWord_4818762).sum := by decide
  have hdescent : baseEnd_4818762 < baseStart_4818762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818768 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 4, 6]
def baseStart_4818768 : Nat := 118140960795 + 4818768 * 2 ^ 59
def prefixEnd_4818768 : Nat := 4983230072969 + 3 ^ 40 * 4818768 * 2
def baseEnd_4818768 : Nat := 824781382168302593912965

theorem tailTrace_4818768 : CollatzResearch.WordTrace tailWord_4818768 prefixEnd_4818768 824781382168302593912965 := by
  unfold tailWord_4818768
  simp only [CollatzResearch.WordTrace]
  refine ⟨87877453903216995449360479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117169938537622660599147305 87877453903216995449360479)
  ·
    refine ⟨131816180854825493174040719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87877453903216995449360479 131816180854825493174040719)
    ·
      refine ⟨197724271282238239761061079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131816180854825493174040719 197724271282238239761061079)
      ·
        refine ⟨296586406923357359641591619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197724271282238239761061079 296586406923357359641591619)
        ·
          refine ⟨444879610385036039462387429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296586406923357359641591619 444879610385036039462387429)
          ·
            refine ⟨83414926947194257399197643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 444879610385036039462387429 83414926947194257399197643)
            ·
              refine ⟨125122390420791386098796465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83414926947194257399197643 125122390420791386098796465)
              ·
                refine ⟨93841792815593539574097349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125122390420791386098796465 93841792815593539574097349)
                ·
                  refine ⟨17595336152923788670143253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93841792815593539574097349 17595336152923788670143253)
                  ·
                    refine ⟨824781382168302593912965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17595336152923788670143253 824781382168302593912965)
                    ·
                      rfl

theorem cell23_4818768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_4818768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818768 prefixEnd_4818768 := by exact prefixLift 4818768
  have htrace : WordTrace (prefixWord ++ tailWord_4818768) baseStart_4818768 baseEnd_4818768 := by
    simpa [prefixWord, tailWord_4818768, baseEnd_4818768] using wordTrace_append hprefix tailTrace_4818768
  have hstable : (prefixWord ++ tailWord_4818768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818768).length < 2 ^ (prefixWord ++ tailWord_4818768).sum := by decide
  have hdescent : baseEnd_4818768 < baseStart_4818768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818786 : List Nat := [3, 3, 2, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_4818786 : Nat := 118140960795 + 4818786 * 2 ^ 59
def prefixEnd_4818786 : Nat := 4983230072969 + 3 ^ 40 * 4818786 * 2
def baseEnd_4818786 : Nat := 2474353389156688711313813

theorem tailTrace_4818786 : CollatzResearch.WordTrace tailWord_4818786 prefixEnd_4818786 2474353389156688711313813 := by
  unfold tailWord_4818786
  simp only [CollatzResearch.WordTrace]
  refine ⟨43938891080092194993219053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117170376213579186648584141 43938891080092194993219053)
  ·
    refine ⟨16477084155034573122457145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43938891080092194993219053 16477084155034573122457145)
    ·
      refine ⟨12357813116275929841842859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16477084155034573122457145 12357813116275929841842859)
      ·
        refine ⟨18536719674413894762764289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12357813116275929841842859 18536719674413894762764289)
        ·
          refine ⟨13902539755810421072073217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18536719674413894762764289 13902539755810421072073217)
          ·
            refine ⟨10426904816857815804054913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13902539755810421072073217 10426904816857815804054913)
            ·
              refine ⟨7820178612643361853041185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10426904816857815804054913 7820178612643361853041185)
              ·
                refine ⟨5865133959482521389780889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7820178612643361853041185 5865133959482521389780889)
                ·
                  refine ⟨4398850469611891042335667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5865133959482521389780889 4398850469611891042335667)
                  ·
                    refine ⟨6598275704417836563503501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4398850469611891042335667 6598275704417836563503501)
                    ·
                      refine ⟨2474353389156688711313813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6598275704417836563503501 2474353389156688711313813)
                      ·
                        rfl

theorem cell23_4818786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_4818786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818786 prefixEnd_4818786 := by exact prefixLift 4818786
  have htrace : WordTrace (prefixWord ++ tailWord_4818786) baseStart_4818786 baseEnd_4818786 := by
    simpa [prefixWord, tailWord_4818786, baseEnd_4818786] using wordTrace_append hprefix tailTrace_4818786
  have hstable : (prefixWord ++ tailWord_4818786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818786).length < 2 ^ (prefixWord ++ tailWord_4818786).sum := by decide
  have hdescent : baseEnd_4818786 < baseStart_4818786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818792 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_4818792 : Nat := 118140960795 + 4818792 * 2 ^ 59
def prefixEnd_4818792 : Nat := 4983230072969 + 3 ^ 40 * 4818792 * 2
def baseEnd_4818792 : Nat := 2474356470040615687838785

theorem tailTrace_4818792 : CollatzResearch.WordTrace tailWord_4818792 prefixEnd_4818792 2474356470040615687838785 := by
  unfold tailWord_4818792
  simp only [CollatzResearch.WordTrace]
  refine ⟨87877891579173521498797315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117170522105564695331729753 87877891579173521498797315)
  ·
    refine ⟨131816837368760282248195973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87877891579173521498797315 131816837368760282248195973)
    ·
      refine ⟨24715657006642552921536745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131816837368760282248195973 24715657006642552921536745)
      ·
        refine ⟨18536742754981914691152559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24715657006642552921536745 18536742754981914691152559)
        ·
          refine ⟨27805114132472872036728839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18536742754981914691152559 27805114132472872036728839)
          ·
            refine ⟨41707671198709308055093259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27805114132472872036728839 41707671198709308055093259)
            ·
              refine ⟨62561506798063962082639889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41707671198709308055093259 62561506798063962082639889)
              ·
                refine ⟨46921130098547971561979917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62561506798063962082639889 46921130098547971561979917)
                ·
                  refine ⟨17595423786955489335742469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46921130098547971561979917 17595423786955489335742469)
                  ·
                    refine ⟨3299141960054154250451713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17595423786955489335742469 3299141960054154250451713)
                    ·
                      refine ⟨2474356470040615687838785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3299141960054154250451713 2474356470040615687838785)
                      ·
                        rfl

theorem cell23_4818792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_4818792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818792 prefixEnd_4818792 := by exact prefixLift 4818792
  have htrace : WordTrace (prefixWord ++ tailWord_4818792) baseStart_4818792 baseEnd_4818792 := by
    simpa [prefixWord, tailWord_4818792, baseEnd_4818792] using wordTrace_append hprefix tailTrace_4818792
  have hstable : (prefixWord ++ tailWord_4818792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818792).length < 2 ^ (prefixWord ++ tailWord_4818792).sum := by decide
  have hdescent : baseEnd_4818792 < baseStart_4818792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818808 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_4818808 : Nat := 118140960795 + 4818808 * 2 ^ 59
def prefixEnd_4818808 : Nat := 4983230072969 + 3 ^ 40 * 4818808 * 2
def baseEnd_4818808 : Nat := 2474364685731087625238711

theorem tailTrace_4818808 : CollatzResearch.WordTrace tailWord_4818808 prefixEnd_4818808 2474364685731087625238711 := by
  unfold tailWord_4818808
  simp only [CollatzResearch.WordTrace]
  refine ⟨87878183363144538865088539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117170911150859385153451385 87878183363144538865088539)
  ·
    refine ⟨131817275044716808297632809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87878183363144538865088539 131817275044716808297632809)
    ·
      refine ⟨98862956283537606223224607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131817275044716808297632809 98862956283537606223224607)
      ·
        refine ⟨148294434425306409334836911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98862956283537606223224607 148294434425306409334836911)
        ·
          refine ⟨222441651637959614002255367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148294434425306409334836911 222441651637959614002255367)
          ·
            refine ⟨333662477456939421003383051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222441651637959614002255367 333662477456939421003383051)
            ·
              refine ⟨500493716185409131505074577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333662477456939421003383051 500493716185409131505074577)
              ·
                refine ⟨375370287139056848628805933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500493716185409131505074577 375370287139056848628805933)
                ·
                  refine ⟨140763857677146318235802225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375370287139056848628805933 140763857677146318235802225)
                  ·
                    refine ⟨105572893257859738676851669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 140763857677146318235802225 105572893257859738676851669)
                    ·
                      refine ⟨2474364685731087625238711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105572893257859738676851669 2474364685731087625238711)
                      ·
                        rfl

theorem cell23_4818808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_4818808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818808 prefixEnd_4818808 := by exact prefixLift 4818808
  have htrace : WordTrace (prefixWord ++ tailWord_4818808) baseStart_4818808 baseEnd_4818808 := by
    simpa [prefixWord, tailWord_4818808, baseEnd_4818808] using wordTrace_append hprefix tailTrace_4818808
  have hstable : (prefixWord ++ tailWord_4818808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818808).length < 2 ^ (prefixWord ++ tailWord_4818808).sum := by decide
  have hdescent : baseEnd_4818808 < baseStart_4818808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818809 : List Nat := [1, 2, 1, 3, 2, 2, 1, 5, 2, 2, 2]
def baseStart_4818809 : Nat := 118140960795 + 4818809 * 2 ^ 59
def prefixEnd_4818809 : Nat := 4983230072969 + 3 ^ 40 * 4818809 * 2
def baseEnd_4818809 : Nat := 2474365199211742121326207

theorem tailTrace_4818809 : CollatzResearch.WordTrace tailWord_4818809 prefixEnd_4818809 2474365199211742121326207 := by
  unfold tailWord_4818809
  simp only [CollatzResearch.WordTrace]
  refine ⟨175756403199285454900963481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117170935466190303267308987 175756403199285454900963481)
  ·
    refine ⟨131817302399464091175722611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175756403199285454900963481 131817302399464091175722611)
    ·
      refine ⟨197725953599196136763583917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131817302399464091175722611 197725953599196136763583917)
      ·
        refine ⟨74147232599698551286343969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197725953599196136763583917 74147232599698551286343969)
        ·
          refine ⟨55610424449773913464757977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74147232599698551286343969 55610424449773913464757977)
          ·
            refine ⟨41707818337330435098568483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55610424449773913464757977 41707818337330435098568483)
            ·
              refine ⟨62561727505995652647852725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41707818337330435098568483 62561727505995652647852725)
              ·
                refine ⟨5865161953687092435736193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62561727505995652647852725 5865161953687092435736193)
                ·
                  refine ⟨4398871465265319326802145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5865161953687092435736193 4398871465265319326802145)
                  ·
                    refine ⟨3299153598948989495101609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4398871465265319326802145 3299153598948989495101609)
                    ·
                      refine ⟨2474365199211742121326207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3299153598948989495101609 2474365199211742121326207)
                      ·
                        rfl

theorem cell23_4818809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_4818809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818809 prefixEnd_4818809 := by exact prefixLift 4818809
  have htrace : WordTrace (prefixWord ++ tailWord_4818809) baseStart_4818809 baseEnd_4818809 := by
    simpa [prefixWord, tailWord_4818809, baseEnd_4818809] using wordTrace_append hprefix tailTrace_4818809
  have hstable : (prefixWord ++ tailWord_4818809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818809).length < 2 ^ (prefixWord ++ tailWord_4818809).sum := by decide
  have hdescent : baseEnd_4818809 < baseStart_4818809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818825 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 1, 5, 3]
def baseStart_4818825 : Nat := 118140960795 + 4818825 * 2 ^ 59
def prefixEnd_4818825 : Nat := 4983230072969 + 3 ^ 40 * 4818825 * 2
def baseEnd_4818825 : Nat := 2474373414902214058726133

theorem tailTrace_4818825 : CollatzResearch.WordTrace tailWord_4818825 prefixEnd_4818825 2474373414902214058726133 := by
  unfold tailWord_4818825
  simp only [CollatzResearch.WordTrace]
  refine ⟨175756986767227489633545929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117171324511484993089030619 175756986767227489633545929)
  ·
    refine ⟨131817740075420617225159447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175756986767227489633545929 131817740075420617225159447)
    ·
      refine ⟨197726610113130925837739171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131817740075420617225159447 197726610113130925837739171)
      ·
        refine ⟨296589915169696388756608757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197726610113130925837739171 296589915169696388756608757)
        ·
          refine ⟨27805304547159036445932071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 296589915169696388756608757 27805304547159036445932071)
          ·
            refine ⟨41707956820738554668898107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27805304547159036445932071 41707956820738554668898107)
            ·
              refine ⟨62561935231107832003347161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41707956820738554668898107 62561935231107832003347161)
              ·
                refine ⟨46921451423330874002510371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62561935231107832003347161 46921451423330874002510371)
                ·
                  refine ⟨70382177134996311003765557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46921451423330874002510371 70382177134996311003765557)
                  ·
                    refine ⟨6598329106405904156603021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70382177134996311003765557 6598329106405904156603021)
                    ·
                      refine ⟨2474373414902214058726133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6598329106405904156603021 2474373414902214058726133)
                      ·
                        rfl

theorem cell23_4818825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 5, 3].length) (baseStart_4818825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818825 prefixEnd_4818825 := by exact prefixLift 4818825
  have htrace : WordTrace (prefixWord ++ tailWord_4818825) baseStart_4818825 baseEnd_4818825 := by
    simpa [prefixWord, tailWord_4818825, baseEnd_4818825] using wordTrace_append hprefix tailTrace_4818825
  have hstable : (prefixWord ++ tailWord_4818825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818825).length < 2 ^ (prefixWord ++ tailWord_4818825).sum := by decide
  have hdescent : baseEnd_4818825 < baseStart_4818825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818830 : List Nat := [4, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2]
def baseStart_4818830 : Nat := 118140960795 + 4818830 * 2 ^ 59
def prefixEnd_4818830 : Nat := 4983230072969 + 3 ^ 40 * 4818830 * 2
def baseEnd_4818830 : Nat := 2474375982305486539163611

theorem tailTrace_4818830 : CollatzResearch.WordTrace tailWord_4818830 prefixEnd_4818830 2474375982305486539163611 := by
  unfold tailWord_4818830
  simp only [CollatzResearch.WordTrace]
  refine ⟨21969646141526171935934743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117171446088139583658318629 21969646141526171935934743)
  ·
    refine ⟨32954469212289257903902115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21969646141526171935934743 32954469212289257903902115)
    ·
      refine ⟨49431703818433886855853173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32954469212289257903902115 49431703818433886855853173)
      ·
        refine ⟨4634222232978176892736235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49431703818433886855853173 4634222232978176892736235)
        ·
          refine ⟨6951333349467265339104353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4634222232978176892736235 6951333349467265339104353)
          ·
            refine ⟨5213500012100449004328265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6951333349467265339104353 5213500012100449004328265)
            ·
              refine ⟨3910125009075336753246199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5213500012100449004328265 3910125009075336753246199)
              ·
                refine ⟨5865187513613005129869299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3910125009075336753246199 5865187513613005129869299)
                ·
                  refine ⟨8797781270419507694803949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5865187513613005129869299 8797781270419507694803949)
                  ·
                    refine ⟨3299167976407315385551481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8797781270419507694803949 3299167976407315385551481)
                    ·
                      refine ⟨2474375982305486539163611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3299167976407315385551481 2474375982305486539163611)
                      ·
                        rfl

theorem cell23_4818830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_4818830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818830 prefixEnd_4818830 := by exact prefixLift 4818830
  have htrace : WordTrace (prefixWord ++ tailWord_4818830) baseStart_4818830 baseEnd_4818830 := by
    simpa [prefixWord, tailWord_4818830, baseEnd_4818830] using wordTrace_append hprefix tailTrace_4818830
  have hstable : (prefixWord ++ tailWord_4818830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818830).length < 2 ^ (prefixWord ++ tailWord_4818830).sum := by decide
  have hdescent : baseEnd_4818830 < baseStart_4818830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818842 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3]
def baseStart_4818842 : Nat := 118140960795 + 4818842 * 2 ^ 59
def prefixEnd_4818842 : Nat := 4983230072969 + 3 ^ 40 * 4818842 * 2
def baseEnd_4818842 : Nat := 2474382144073340492213555

theorem tailTrace_4818842 : CollatzResearch.WordTrace tailWord_4818842 prefixEnd_4818842 2474382144073340492213555 := by
  unfold tailWord_4818842
  simp only [CollatzResearch.WordTrace]
  refine ⟨43939401702041475384228695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117171737872110601024609853 43939401702041475384228695)
  ·
    refine ⟨65909102553062213076343043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43939401702041475384228695 65909102553062213076343043)
    ·
      refine ⟨98863653829593319614514565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65909102553062213076343043 98863653829593319614514565)
      ·
        refine ⟨18536935093048747427721481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98863653829593319614514565 18536935093048747427721481)
        ·
          refine ⟨13902701319786560570791111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18536935093048747427721481 13902701319786560570791111)
          ·
            refine ⟨20854051979679840856186667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13902701319786560570791111 20854051979679840856186667)
            ·
              refine ⟨31281077969519761284280001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20854051979679840856186667 31281077969519761284280001)
              ·
                refine ⟨23460808477139820963210001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31281077969519761284280001 23460808477139820963210001)
                ·
                  refine ⟨17595606357854865722407501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23460808477139820963210001 17595606357854865722407501)
                  ·
                    refine ⟨6598352384195574645902813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17595606357854865722407501 6598352384195574645902813)
                    ·
                      refine ⟨2474382144073340492213555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6598352384195574645902813 2474382144073340492213555)
                      ·
                        rfl

theorem cell23_4818842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_4818842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818842 prefixEnd_4818842 := by exact prefixLift 4818842
  have htrace : WordTrace (prefixWord ++ tailWord_4818842) baseStart_4818842 baseEnd_4818842 := by
    simpa [prefixWord, tailWord_4818842, baseEnd_4818842] using wordTrace_append hprefix tailTrace_4818842
  have hstable : (prefixWord ++ tailWord_4818842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818842).length < 2 ^ (prefixWord ++ tailWord_4818842).sum := by decide
  have hdescent : baseEnd_4818842 < baseStart_4818842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818922 : List Nat := [3, 1, 3, 1, 2, 1, 3, 3, 6]
def baseStart_4818922 : Nat := 118140960795 + 4818922 * 2 ^ 59
def prefixEnd_4818922 : Nat := 4983230072969 + 3 ^ 40 * 4818922 * 2
def baseEnd_4818922 : Nat := 274935913613966686579243

theorem tailTrace_4818922 : CollatzResearch.WordTrace tailWord_4818922 prefixEnd_4818922 274935913613966686579243 := by
  unfold tailWord_4818922
  simp only [CollatzResearch.WordTrace]
  refine ⟨43940131161969018799956755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117173683098584050133218013 43940131161969018799956755)
  ·
    refine ⟨65910196742953528199935133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43940131161969018799956755 65910196742953528199935133)
    ·
      refine ⟨24716323778607573074975675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65910196742953528199935133 24716323778607573074975675)
      ·
        refine ⟨37074485667911359612463513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24716323778607573074975675 37074485667911359612463513)
        ·
          refine ⟨27805864250933519709347635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37074485667911359612463513 27805864250933519709347635)
          ·
            refine ⟨41708796376400279564021453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27805864250933519709347635 41708796376400279564021453)
            ·
              refine ⟨15640798641150104836508045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41708796376400279564021453 15640798641150104836508045)
              ·
                refine ⟨5865299490431289313690517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15640798641150104836508045 5865299490431289313690517)
                ·
                  refine ⟨274935913613966686579243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5865299490431289313690517 274935913613966686579243)
                  ·
                    rfl

theorem cell23_4818922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_4818922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818922 prefixEnd_4818922 := by exact prefixLift 4818922
  have htrace : WordTrace (prefixWord ++ tailWord_4818922) baseStart_4818922 baseEnd_4818922 := by
    simpa [prefixWord, tailWord_4818922, baseEnd_4818922] using wordTrace_append hprefix tailTrace_4818922
  have hstable : (prefixWord ++ tailWord_4818922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818922).length < 2 ^ (prefixWord ++ tailWord_4818922).sum := by decide
  have hdescent : baseEnd_4818922 < baseStart_4818922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818983 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_4818983 : Nat := 118140960795 + 4818983 * 2 ^ 59
def prefixEnd_4818983 : Nat := 4983230072969 + 3 ^ 40 * 4818983 * 2
def baseEnd_4818983 : Nat := 2474454544845624440550407

theorem tailTrace_4818983 : CollatzResearch.WordTrace tailWord_4818983 prefixEnd_4818983 2474454544845624440550407 := by
  unfold tailWord_4818983
  simp only [CollatzResearch.WordTrace]
  refine ⟨175762749500655082617797603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117175166333770055078531735 175762749500655082617797603)
  ·
    refine ⟨263644124250982623926696405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175762749500655082617797603 263644124250982623926696405)
    ·
      refine ⟨6179159162132405248281947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 263644124250982623926696405 6179159162132405248281947)
      ·
        refine ⟨9268738743198607872422921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6179159162132405248281947 9268738743198607872422921)
        ·
          refine ⟨6951554057398955904317191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9268738743198607872422921 6951554057398955904317191)
          ·
            refine ⟨10427331086098433856475787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6951554057398955904317191 10427331086098433856475787)
            ·
              refine ⟨15640996629147650784713681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10427331086098433856475787 15640996629147650784713681)
              ·
                refine ⟨11730747471860738088535261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15640996629147650784713681 11730747471860738088535261)
                ·
                  refine ⟨4399030301947776783200723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11730747471860738088535261 4399030301947776783200723)
                  ·
                    refine ⟨6598545452921665174801085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4399030301947776783200723 6598545452921665174801085)
                    ·
                      refine ⟨2474454544845624440550407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6598545452921665174801085 2474454544845624440550407)
                      ·
                        rfl

theorem cell23_4818983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_4818983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818983 prefixEnd_4818983 := by exact prefixLift 4818983
  have htrace : WordTrace (prefixWord ++ tailWord_4818983) baseStart_4818983 baseEnd_4818983 := by
    simpa [prefixWord, tailWord_4818983, baseEnd_4818983] using wordTrace_append hprefix tailTrace_4818983
  have hstable : (prefixWord ++ tailWord_4818983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818983).length < 2 ^ (prefixWord ++ tailWord_4818983).sum := by decide
  have hdescent : baseEnd_4818983 < baseStart_4818983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818985 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 6]
def baseStart_4818985 : Nat := 118140960795 + 4818985 * 2 ^ 59
def prefixEnd_4818985 : Nat := 4983230072969 + 3 ^ 40 * 4818985 * 2
def baseEnd_4818985 : Nat := 2474455571806933432725397

theorem tailTrace_4818985 : CollatzResearch.WordTrace tailWord_4818985 prefixEnd_4818985 2474455571806933432725397 := by
  unfold tailWord_4818985
  simp only [CollatzResearch.WordTrace]
  refine ⟨175762822446647836959370409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117175214964431891306246939 175762822446647836959370409)
  ·
    refine ⟨131822116834985877719527807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175762822446647836959370409 131822116834985877719527807)
    ·
      refine ⟨197733175252478816579291711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131822116834985877719527807 197733175252478816579291711)
      ·
        refine ⟨296599762878718224868937567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197733175252478816579291711 296599762878718224868937567)
        ·
          refine ⟨444899644318077337303406351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296599762878718224868937567 444899644318077337303406351)
          ·
            refine ⟨667349466477116005955109527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444899644318077337303406351 667349466477116005955109527)
            ·
              refine ⟨1001024199715674008932664291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667349466477116005955109527 1001024199715674008932664291)
              ·
                refine ⟨1501536299573511013398996437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001024199715674008932664291 1501536299573511013398996437)
                ·
                  refine ⟨35192257021254164376538979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1501536299573511013398996437 35192257021254164376538979)
                  ·
                    refine ⟨52788385531881246564808469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35192257021254164376538979 52788385531881246564808469)
                    ·
                      refine ⟨2474455571806933432725397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52788385531881246564808469 2474455571806933432725397)
                      ·
                        rfl

theorem cell23_4818985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_4818985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818985 prefixEnd_4818985 := by exact prefixLift 4818985
  have htrace : WordTrace (prefixWord ++ tailWord_4818985) baseStart_4818985 baseEnd_4818985 := by
    simpa [prefixWord, tailWord_4818985, baseEnd_4818985] using wordTrace_append hprefix tailTrace_4818985
  have hstable : (prefixWord ++ tailWord_4818985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818985).length < 2 ^ (prefixWord ++ tailWord_4818985).sum := by decide
  have hdescent : baseEnd_4818985 < baseStart_4818985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4818995 : List Nat := [1, 1, 1, 2, 4, 1, 2, 11]
def baseStart_4818995 : Nat := 118140960795 + 4818995 * 2 ^ 59
def prefixEnd_4818995 : Nat := 4983230072969 + 3 ^ 40 * 4818995 * 2
def baseEnd_4818995 : Nat := 91646692837536236800013

theorem tailTrace_4818995 : CollatzResearch.WordTrace tailWord_4818995 prefixEnd_4818995 91646692837536236800013 := by
  unfold tailWord_4818995
  simp only [CollatzResearch.WordTrace]
  refine ⟨175763187176611608667234439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117175458117741072444822959 175763187176611608667234439)
  ·
    refine ⟨263644780764917413000851659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175763187176611608667234439 263644780764917413000851659)
    ·
      refine ⟨395467171147376119501277489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263644780764917413000851659 395467171147376119501277489)
      ·
        refine ⟨296600378360532089625958117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395467171147376119501277489 296600378360532089625958117)
        ·
          refine ⟨55612570942599766804867147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296600378360532089625958117 55612570942599766804867147)
          ·
            refine ⟨83418856413899650207300721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55612570942599766804867147 83418856413899650207300721)
            ·
              refine ⟨62564142310424737655475541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83418856413899650207300721 62564142310424737655475541)
              ·
                refine ⟨91646692837536236800013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 62564142310424737655475541 91646692837536236800013)
                ·
                  rfl

theorem cell23_4818995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 11].length) (baseStart_4818995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4818995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4818995 prefixEnd_4818995 := by exact prefixLift 4818995
  have htrace : WordTrace (prefixWord ++ tailWord_4818995) baseStart_4818995 baseEnd_4818995 := by
    simpa [prefixWord, tailWord_4818995, baseEnd_4818995] using wordTrace_append hprefix tailTrace_4818995
  have hstable : (prefixWord ++ tailWord_4818995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4818995).length < 2 ^ (prefixWord ++ tailWord_4818995).sum := by decide
  have hdescent : baseEnd_4818995 < baseStart_4818995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4818995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819036 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_4819036 : Nat := 118140960795 + 4819036 * 2 ^ 59
def prefixEnd_4819036 : Nat := 4983230072969 + 3 ^ 40 * 4819036 * 2
def baseEnd_4819036 : Nat := 2474481759320312733187663

theorem tailTrace_4819036 : CollatzResearch.WordTrace tailWord_4819036 prefixEnd_4819036 2474481759320312733187663 := by
  unfold tailWord_4819036
  simp only [CollatzResearch.WordTrace]
  refine ⟨87882341284731536334738481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117176455046308715112984641 87882341284731536334738481)
  ·
    refine ⟨65911755963548652251053861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87882341284731536334738481 65911755963548652251053861)
    ·
      refine ⟨12358454243165372297072599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65911755963548652251053861 12358454243165372297072599)
      ·
        refine ⟨18537681364748058445608899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12358454243165372297072599 18537681364748058445608899)
        ·
          refine ⟨27806522047122087668413349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18537681364748058445608899 27806522047122087668413349)
          ·
            refine ⟨5213722883835391437827503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27806522047122087668413349 5213722883835391437827503)
            ·
              refine ⟨7820584325753087156741255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5213722883835391437827503 7820584325753087156741255)
              ·
                refine ⟨11730876488629630735111883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7820584325753087156741255 11730876488629630735111883)
                ·
                  refine ⟨17596314732944446102667825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11730876488629630735111883 17596314732944446102667825)
                  ·
                    refine ⟨13197236049708334577000869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17596314732944446102667825 13197236049708334577000869)
                    ·
                      refine ⟨2474481759320312733187663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13197236049708334577000869 2474481759320312733187663)
                      ·
                        rfl

theorem cell23_4819036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_4819036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819036 prefixEnd_4819036 := by exact prefixLift 4819036
  have htrace : WordTrace (prefixWord ++ tailWord_4819036) baseStart_4819036 baseEnd_4819036 := by
    simpa [prefixWord, tailWord_4819036, baseEnd_4819036] using wordTrace_append hprefix tailTrace_4819036
  have hstable : (prefixWord ++ tailWord_4819036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819036).length < 2 ^ (prefixWord ++ tailWord_4819036).sum := by decide
  have hdescent : baseEnd_4819036 < baseStart_4819036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819052 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_4819052 : Nat := 118140960795 + 4819052 * 2 ^ 59
def prefixEnd_4819052 : Nat := 4983230072969 + 3 ^ 40 * 4819052 * 2
def baseEnd_4819052 : Nat := 2474489975010784670587589

theorem tailTrace_4819052 : CollatzResearch.WordTrace tailWord_4819052 prefixEnd_4819052 2474489975010784670587589 := by
  unfold tailWord_4819052
  simp only [CollatzResearch.WordTrace]
  refine ⟨87882633068702553701029705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117176844091603404934706273 87882633068702553701029705)
  ·
    refine ⟨65911974801526915275772279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87882633068702553701029705 65911974801526915275772279)
    ·
      refine ⟨98867962202290372913658419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65911974801526915275772279 98867962202290372913658419)
      ·
        refine ⟨148301943303435559370487629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98867962202290372913658419 148301943303435559370487629)
        ·
          refine ⟨55613228738788334763932861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148301943303435559370487629 55613228738788334763932861)
          ·
            refine ⟨20854960777045625536474823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55613228738788334763932861 20854960777045625536474823)
            ·
              refine ⟨31282441165568438304712235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20854960777045625536474823 31282441165568438304712235)
              ·
                refine ⟨46923661748352657457068353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31282441165568438304712235 46923661748352657457068353)
                ·
                  refine ⟨35192746311264493092801265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46923661748352657457068353 35192746311264493092801265)
                  ·
                    refine ⟨26394559733448369819600949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35192746311264493092801265 26394559733448369819600949)
                    ·
                      refine ⟨2474489975010784670587589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26394559733448369819600949 2474489975010784670587589)
                      ·
                        rfl

theorem cell23_4819052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_4819052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819052 prefixEnd_4819052 := by exact prefixLift 4819052
  have htrace : WordTrace (prefixWord ++ tailWord_4819052) baseStart_4819052 baseEnd_4819052 := by
    simpa [prefixWord, tailWord_4819052, baseEnd_4819052] using wordTrace_append hprefix tailTrace_4819052
  have hstable : (prefixWord ++ tailWord_4819052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819052).length < 2 ^ (prefixWord ++ tailWord_4819052).sum := by decide
  have hdescent : baseEnd_4819052 < baseStart_4819052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819119 : List Nat := [1, 1, 2, 1, 2, 3, 1, 7, 5]
def baseStart_4819119 : Nat := 118140960795 + 4819119 * 2 ^ 59
def prefixEnd_4819119 : Nat := 4983230072969 + 3 ^ 40 * 4819119 * 2
def baseEnd_4819119 : Nat := 274947153134959545383309

theorem tailTrace_4819119 : CollatzResearch.WordTrace tailWord_4819119 prefixEnd_4819119 274947153134959545383309 := by
  unfold tailWord_4819119
  simp only [CollatzResearch.WordTrace]
  refine ⟨175767709828162377844748411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117178473218774918563165607 175767709828162377844748411)
  ·
    refine ⟨263651564742243566767122617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175767709828162377844748411 263651564742243566767122617)
    ·
      refine ⟨197738673556682675075341963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263651564742243566767122617 197738673556682675075341963)
      ·
        refine ⟨296608010335024012613012945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197738673556682675075341963 296608010335024012613012945)
        ·
          refine ⟨222456007751268009459759709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296608010335024012613012945 222456007751268009459759709)
          ·
            refine ⟨83421002906725503547409891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222456007751268009459759709 83421002906725503547409891)
            ·
              refine ⟨125131504360088255321114837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83421002906725503547409891 125131504360088255321114837)
              ·
                refine ⟨2932769633439568484088629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 125131504360088255321114837 2932769633439568484088629)
                ·
                  refine ⟨274947153134959545383309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2932769633439568484088629 274947153134959545383309)
                  ·
                    rfl

theorem cell23_4819119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 5].length) (baseStart_4819119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819119 prefixEnd_4819119 := by exact prefixLift 4819119
  have htrace : WordTrace (prefixWord ++ tailWord_4819119) baseStart_4819119 baseEnd_4819119 := by
    simpa [prefixWord, tailWord_4819119, baseEnd_4819119] using wordTrace_append hprefix tailTrace_4819119
  have hstable : (prefixWord ++ tailWord_4819119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819119).length < 2 ^ (prefixWord ++ tailWord_4819119).sum := by decide
  have hdescent : baseEnd_4819119 < baseStart_4819119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819124 : List Nat := [2, 5, 3, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_4819124 : Nat := 118140960795 + 4819124 * 2 ^ 59
def prefixEnd_4819124 : Nat := 4983230072969 + 3 ^ 40 * 4819124 * 2
def baseEnd_4819124 : Nat := 2474526945617908388887259

theorem tailTrace_4819124 : CollatzResearch.WordTrace tailWord_4819124 prefixEnd_4819124 2474526945617908388887259 := by
  unfold tailWord_4819124
  simp only [CollatzResearch.WordTrace]
  refine ⟨87883946096572131849340213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117178594795429509132453617 87883946096572131849340213)
  ·
    refine ⟨8239119946553637360875645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87883946096572131849340213 8239119946553637360875645)
    ·
      refine ⟨3089669979957614010328367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8239119946553637360875645 3089669979957614010328367)
      ·
        refine ⟨4634504969936421015492551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3089669979957614010328367 4634504969936421015492551)
        ·
          refine ⟨6951757454904631523238827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4634504969936421015492551 6951757454904631523238827)
          ·
            refine ⟨10427636182356947284858241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6951757454904631523238827 10427636182356947284858241)
            ·
              refine ⟨7820727136767710463643681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10427636182356947284858241 7820727136767710463643681)
              ·
                refine ⟨5865545352575782847732761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7820727136767710463643681 5865545352575782847732761)
                ·
                  refine ⟨4399159014431837135799571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5865545352575782847732761 4399159014431837135799571)
                  ·
                    refine ⟨6598738521647755703699357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4399159014431837135799571 6598738521647755703699357)
                    ·
                      refine ⟨2474526945617908388887259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6598738521647755703699357 2474526945617908388887259)
                      ·
                        rfl

theorem cell23_4819124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_4819124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819124 prefixEnd_4819124 := by exact prefixLift 4819124
  have htrace : WordTrace (prefixWord ++ tailWord_4819124) baseStart_4819124 baseEnd_4819124 := by
    simpa [prefixWord, tailWord_4819124, baseEnd_4819124] using wordTrace_append hprefix tailTrace_4819124
  have hstable : (prefixWord ++ tailWord_4819124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819124).length < 2 ^ (prefixWord ++ tailWord_4819124).sum := by decide
  have hdescent : baseEnd_4819124 < baseStart_4819124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819129 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 2, 3, 3]
def baseStart_4819129 : Nat := 118140960795 + 4819129 * 2 ^ 59
def prefixEnd_4819129 : Nat := 4983230072969 + 3 ^ 40 * 4819129 * 2
def baseEnd_4819129 : Nat := 2474529513021180869324735

theorem tailTrace_4819129 : CollatzResearch.WordTrace tailWord_4819129 prefixEnd_4819129 2474529513021180869324735 := by
  unfold tailWord_4819129
  simp only [CollatzResearch.WordTrace]
  refine ⟨175768074558126149552612441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117178716372084099701741627 175768074558126149552612441)
  ·
    refine ⟨131826055918594612164459331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175768074558126149552612441 131826055918594612164459331)
    ·
      refine ⟨197739083877891918246688997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131826055918594612164459331 197739083877891918246688997)
      ·
        refine ⟨37076078227104734671254187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197739083877891918246688997 37076078227104734671254187)
        ·
          refine ⟨55614117340657102006881281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37076078227104734671254187 55614117340657102006881281)
          ·
            refine ⟨41710588005492826505160961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55614117340657102006881281 41710588005492826505160961)
            ·
              refine ⟨31282941004119619878870721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41710588005492826505160961 31282941004119619878870721)
              ·
                refine ⟨23462205753089714909153041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31282941004119619878870721 23462205753089714909153041)
                ·
                  refine ⟨17596654314817286181864781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23462205753089714909153041 17596654314817286181864781)
                  ·
                    refine ⟨6598745368056482318199293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17596654314817286181864781 6598745368056482318199293)
                    ·
                      refine ⟨2474529513021180869324735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6598745368056482318199293 2474529513021180869324735)
                      ·
                        rfl

theorem cell23_4819129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_4819129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819129 prefixEnd_4819129 := by exact prefixLift 4819129
  have htrace : WordTrace (prefixWord ++ tailWord_4819129) baseStart_4819129 baseEnd_4819129 := by
    simpa [prefixWord, tailWord_4819129, baseEnd_4819129] using wordTrace_append hprefix tailTrace_4819129
  have hstable : (prefixWord ++ tailWord_4819129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819129).length < 2 ^ (prefixWord ++ tailWord_4819129).sum := by decide
  have hdescent : baseEnd_4819129 < baseStart_4819129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819136 : List Nat := [2, 1, 1, 2, 5, 2, 1, 4, 5]
def baseStart_4819136 : Nat := 118140960795 + 4819136 * 2 ^ 59
def prefixEnd_4819136 : Nat := 4983230072969 + 3 ^ 40 * 4819136 * 2
def baseEnd_4819136 : Nat := 274948123042862482437467

theorem tailTrace_4819136 : CollatzResearch.WordTrace tailWord_4819136 prefixEnd_4819136 274948123042862482437467 := by
  unfold tailWord_4819136
  simp only [CollatzResearch.WordTrace]
  refine ⟨87884164934550394874058631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117178886579400526498744841 87884164934550394874058631)
  ·
    refine ⟨131826247401825592311087947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87884164934550394874058631 131826247401825592311087947)
    ·
      refine ⟨197739371102738388466631921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131826247401825592311087947 197739371102738388466631921)
      ·
        refine ⟨148304528327053791349973941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197739371102738388466631921 148304528327053791349973941)
        ·
          refine ⟨13903549530661292939060057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148304528327053791349973941 13903549530661292939060057)
          ·
            refine ⟨10427662147995969704295043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13903549530661292939060057 10427662147995969704295043)
            ·
              refine ⟨15641493221993954556442565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10427662147995969704295043 15641493221993954556442565)
              ·
                refine ⟨2932779979123866479332981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15641493221993954556442565 2932779979123866479332981)
                ·
                  refine ⟨274948123042862482437467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2932779979123866479332981 274948123042862482437467)
                  ·
                    rfl

theorem cell23_4819136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 5].length) (baseStart_4819136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819136 prefixEnd_4819136 := by exact prefixLift 4819136
  have htrace : WordTrace (prefixWord ++ tailWord_4819136) baseStart_4819136 baseEnd_4819136 := by
    simpa [prefixWord, tailWord_4819136, baseEnd_4819136] using wordTrace_append hprefix tailTrace_4819136
  have hstable : (prefixWord ++ tailWord_4819136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819136).length < 2 ^ (prefixWord ++ tailWord_4819136).sum := by decide
  have hdescent : baseEnd_4819136 < baseStart_4819136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819169 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_4819169 : Nat := 118140960795 + 4819169 * 2 ^ 59
def prefixEnd_4819169 : Nat := 4983230072969 + 3 ^ 40 * 4819169 * 2
def baseEnd_4819169 : Nat := 2474550052247360712824551

theorem tailTrace_4819169 : CollatzResearch.WordTrace tailWord_4819169 prefixEnd_4819169 2474550052247360712824551 := by
  unfold tailWord_4819169
  simp only [CollatzResearch.WordTrace]
  refine ⟨175769533477981236384068561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117179688985320824256045707 175769533477981236384068561)
  ·
    refine ⟨131827150108485927288051421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175769533477981236384068561 131827150108485927288051421)
    ·
      refine ⟨49435181290682222733019283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131827150108485927288051421 49435181290682222733019283)
      ·
        refine ⟨74152771936023334099528925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49435181290682222733019283 74152771936023334099528925)
        ·
          refine ⟨27807289476008750287323347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74152771936023334099528925 27807289476008750287323347)
          ·
            refine ⟨41710934214013125430985021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27807289476008750287323347 41710934214013125430985021)
            ·
              refine ⟨15641600330254922036619383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41710934214013125430985021 15641600330254922036619383)
              ·
                refine ⟨23462400495382383054929075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15641600330254922036619383 23462400495382383054929075)
                ·
                  refine ⟨35193600743073574582393613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23462400495382383054929075 35193600743073574582393613)
                  ·
                    refine ⟨13197600278652590468397605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35193600743073574582393613 13197600278652590468397605)
                    ·
                      refine ⟨2474550052247360712824551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13197600278652590468397605 2474550052247360712824551)
                      ·
                        rfl

theorem cell23_4819169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_4819169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819169 prefixEnd_4819169 := by exact prefixLift 4819169
  have htrace : WordTrace (prefixWord ++ tailWord_4819169) baseStart_4819169 baseEnd_4819169 := by
    simpa [prefixWord, tailWord_4819169, baseEnd_4819169] using wordTrace_append hprefix tailTrace_4819169
  have hstable : (prefixWord ++ tailWord_4819169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819169).length < 2 ^ (prefixWord ++ tailWord_4819169).sum := by decide
  have hdescent : baseEnd_4819169 < baseStart_4819169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819179 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 5, 4]
def baseStart_4819179 : Nat := 118140960795 + 4819179 * 2 ^ 59
def prefixEnd_4819179 : Nat := 4983230072969 + 3 ^ 40 * 4819179 * 2
def baseEnd_4819179 : Nat := 824851729017968557899835

theorem tailTrace_4819179 : CollatzResearch.WordTrace tailWord_4819179 prefixEnd_4819179 824851729017968557899835 := by
  unfold tailWord_4819179
  simp only [CollatzResearch.WordTrace]
  refine ⟨175769898207945008091932591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117179932138630005394621727 175769898207945008091932591)
  ·
    refine ⟨263654847311917512137898887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175769898207945008091932591 263654847311917512137898887)
    ·
      refine ⟨395482270967876268206848331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263654847311917512137898887 395482270967876268206848331)
      ·
        refine ⟨593223406451814402310272497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395482270967876268206848331 593223406451814402310272497)
        ·
          refine ⟨444917554838860801732704373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 593223406451814402310272497 444917554838860801732704373)
          ·
            refine ⟨41711020766143200162441035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 444917554838860801732704373 41711020766143200162441035)
            ·
              refine ⟨62566531149214800243661553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41711020766143200162441035 62566531149214800243661553)
              ·
                refine ⟨46924898361911100182746165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62566531149214800243661553 46924898361911100182746165)
                ·
                  refine ⟨4399209221429165642132453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46924898361911100182746165 4399209221429165642132453)
                  ·
                    refine ⟨824851729017968557899835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4399209221429165642132453 824851729017968557899835)
                    ·
                      rfl

theorem cell23_4819179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 4].length) (baseStart_4819179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819179 prefixEnd_4819179 := by exact prefixLift 4819179
  have htrace : WordTrace (prefixWord ++ tailWord_4819179) baseStart_4819179 baseEnd_4819179 := by
    simpa [prefixWord, tailWord_4819179, baseEnd_4819179] using wordTrace_append hprefix tailTrace_4819179
  have hstable : (prefixWord ++ tailWord_4819179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819179).length < 2 ^ (prefixWord ++ tailWord_4819179).sum := by decide
  have hdescent : baseEnd_4819179 < baseStart_4819179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819196 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 3, 4]
def baseStart_4819196 : Nat := 118140960795 + 4819196 * 2 ^ 59
def prefixEnd_4819196 : Nat := 4983230072969 + 3 ^ 40 * 4819196 * 2
def baseEnd_4819196 : Nat := 824854638741677369062309

theorem tailTrace_4819196 : CollatzResearch.WordTrace tailWord_4819196 prefixEnd_4819196 824854638741677369062309 := by
  unfold tailWord_4819196
  simp only [CollatzResearch.WordTrace]
  refine ⟨87885259124441709997650721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117180345499255613330200961 87885259124441709997650721)
  ·
    refine ⟨65913944343331282498238041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87885259124441709997650721 65913944343331282498238041)
    ·
      refine ⟨49435458257498461873678531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65913944343331282498238041 49435458257498461873678531)
      ·
        refine ⟨74153187386247692810517797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49435458257498461873678531 74153187386247692810517797)
        ·
          refine ⟨13903722634921442401972087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74153187386247692810517797 13903722634921442401972087)
          ·
            refine ⟨20855583952382163602958131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13903722634921442401972087 20855583952382163602958131)
            ·
              refine ⟨31283375928573245404437197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20855583952382163602958131 31283375928573245404437197)
              ·
                refine ⟨11731265973214967026663949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31283375928573245404437197 11731265973214967026663949)
                ·
                  refine ⟨4399224739955612634998981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11731265973214967026663949 4399224739955612634998981)
                  ·
                    refine ⟨824854638741677369062309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4399224739955612634998981 824854638741677369062309)
                    ·
                      rfl

theorem cell23_4819196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_4819196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819196 prefixEnd_4819196 := by exact prefixLift 4819196
  have htrace : WordTrace (prefixWord ++ tailWord_4819196) baseStart_4819196 baseEnd_4819196 := by
    simpa [prefixWord, tailWord_4819196, baseEnd_4819196] using wordTrace_append hprefix tailTrace_4819196
  have hstable : (prefixWord ++ tailWord_4819196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819196).length < 2 ^ (prefixWord ++ tailWord_4819196).sum := by decide
  have hdescent : baseEnd_4819196 < baseStart_4819196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819276 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_4819276 : Nat := 118140960795 + 4819276 * 2 ^ 59
def prefixEnd_4819276 : Nat := 4983230072969 + 3 ^ 40 * 4819276 * 2
def baseEnd_4819276 : Nat := 2474604994677391794186559

theorem tailTrace_4819276 : CollatzResearch.WordTrace tailWord_4819276 prefixEnd_4819276 2474604994677391794186559 := by
  unfold tailWord_4819276
  simp only [CollatzResearch.WordTrace]
  refine ⟨87886718044296796829106841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117182290725729062438809121 87886718044296796829106841)
  ·
    refine ⟨65915038533222597621830131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87886718044296796829106841 65915038533222597621830131)
    ·
      refine ⟨98872557799833896432745197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65915038533222597621830131 98872557799833896432745197)
      ·
        refine ⟨37077209174937711162279449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98872557799833896432745197 37077209174937711162279449)
        ·
          refine ⟨27807906881203283371709587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37077209174937711162279449 27807906881203283371709587)
          ·
            refine ⟨41711860321804925057564381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27807906881203283371709587 41711860321804925057564381)
            ·
              refine ⟨15641947620676846896586643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41711860321804925057564381 15641947620676846896586643)
              ·
                refine ⟨23462921431015270344879965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15641947620676846896586643 23462921431015270344879965)
                ·
                  refine ⟨8798595536630726379329987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23462921431015270344879965 8798595536630726379329987)
                  ·
                    refine ⟨13197893304946089568994981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8798595536630726379329987 13197893304946089568994981)
                    ·
                      refine ⟨2474604994677391794186559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13197893304946089568994981 2474604994677391794186559)
                      ·
                        rfl

theorem cell23_4819276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_4819276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819276 prefixEnd_4819276 := by exact prefixLift 4819276
  have htrace : WordTrace (prefixWord ++ tailWord_4819276) baseStart_4819276 baseEnd_4819276 := by
    simpa [prefixWord, tailWord_4819276, baseEnd_4819276] using wordTrace_append hprefix tailTrace_4819276
  have hstable : (prefixWord ++ tailWord_4819276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819276).length < 2 ^ (prefixWord ++ tailWord_4819276).sum := by decide
  have hdescent : baseEnd_4819276 < baseStart_4819276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819294 : List Nat := [4, 4, 2, 1, 1, 1, 2, 2, 6]
def baseStart_4819294 : Nat := 118140960795 + 4819294 * 2 ^ 59
def prefixEnd_4819294 : Nat := 4983230072969 + 3 ^ 40 * 4819294 * 2
def baseEnd_4819294 : Nat := 274957137481019191529053

theorem tailTrace_4819294 : CollatzResearch.WordTrace tailWord_4819294 prefixEnd_4819294 274957137481019191529053 := by
  unfold tailWord_4819294
  simp only [CollatzResearch.WordTrace]
  refine ⟨21971761575316047841546117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117182728401685588488245957 21971761575316047841546117)
  ·
    refine ⟨4119705295371758970289897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21971761575316047841546117 4119705295371758970289897)
    ·
      refine ⟨3089778971528819227717423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4119705295371758970289897 3089778971528819227717423)
      ·
        refine ⟨4634668457293228841576135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3089778971528819227717423 4634668457293228841576135)
        ·
          refine ⟨6952002685939843262364203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4634668457293228841576135 6952002685939843262364203)
          ·
            refine ⟨10428004028909764893546305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6952002685939843262364203 10428004028909764893546305)
            ·
              refine ⟨7821003021682323670159729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10428004028909764893546305 7821003021682323670159729)
              ·
                refine ⟨5865752266261742752619797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7821003021682323670159729 5865752266261742752619797)
                ·
                  refine ⟨274957137481019191529053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5865752266261742752619797 274957137481019191529053)
                  ·
                    rfl

theorem cell23_4819294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_4819294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819294 prefixEnd_4819294 := by exact prefixLift 4819294
  have htrace : WordTrace (prefixWord ++ tailWord_4819294) baseStart_4819294 baseEnd_4819294 := by
    simpa [prefixWord, tailWord_4819294, baseEnd_4819294] using wordTrace_append hprefix tailTrace_4819294
  have hstable : (prefixWord ++ tailWord_4819294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819294).length < 2 ^ (prefixWord ++ tailWord_4819294).sum := by decide
  have hdescent : baseEnd_4819294 < baseStart_4819294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819303 : List Nat := [1, 1, 5, 1, 3, 1, 1, 4, 2, 4]
def baseStart_4819303 : Nat := 118140960795 + 4819303 * 2 ^ 59
def prefixEnd_4819303 : Nat := 4983230072969 + 3 ^ 40 * 4819303 * 2
def baseEnd_4819303 : Nat := 824872952885021062849645

theorem tailTrace_4819303 : CollatzResearch.WordTrace tailWord_4819303 prefixEnd_4819303 824872952885021062849645 := by
  unfold tailWord_4819303
  simp only [CollatzResearch.WordTrace]
  refine ⟨175774420859495777269446563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117182947239663851512964375 175774420859495777269446563)
  ·
    refine ⟨263661631289243665904169845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175774420859495777269446563 263661631289243665904169845)
    ·
      refine ⟨24718277933366593678515923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 263661631289243665904169845 24718277933366593678515923)
      ·
        refine ⟨37077416900049890517773885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24718277933366593678515923 37077416900049890517773885)
        ·
          refine ⟨13904031337518708944165207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37077416900049890517773885 13904031337518708944165207)
          ·
            refine ⟨20856047006278063416247811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13904031337518708944165207 20856047006278063416247811)
            ·
              refine ⟨31284070509417095124371717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20856047006278063416247811 31284070509417095124371717)
              ·
                refine ⟨5865763220515705335819697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31284070509417095124371717 5865763220515705335819697)
                ·
                  refine ⟨4399322415386779001864773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5865763220515705335819697 4399322415386779001864773)
                  ·
                    refine ⟨824872952885021062849645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4399322415386779001864773 824872952885021062849645)
                    ·
                      rfl

theorem cell23_4819303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_4819303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819303 prefixEnd_4819303 := by exact prefixLift 4819303
  have htrace : WordTrace (prefixWord ++ tailWord_4819303) baseStart_4819303 baseEnd_4819303 := by
    simpa [prefixWord, tailWord_4819303, baseEnd_4819303] using wordTrace_append hprefix tailTrace_4819303
  have hstable : (prefixWord ++ tailWord_4819303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819303).length < 2 ^ (prefixWord ++ tailWord_4819303).sum := by decide
  have hdescent : baseEnd_4819303 < baseStart_4819303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819304 : List Nat := [2, 1, 4, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_4819304 : Nat := 118140960795 + 4819304 * 2 ^ 59
def prefixEnd_4819304 : Nat := 4983230072969 + 3 ^ 40 * 4819304 * 2
def baseEnd_4819304 : Nat := 2474619372135717684636431

theorem tailTrace_4819304 : CollatzResearch.WordTrace tailWord_4819304 prefixEnd_4819304 2474619372135717684636431 := by
  unfold tailWord_4819304
  simp only [CollatzResearch.WordTrace]
  refine ⟨87887228666246077220116483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117182971554994769626821977 87887228666246077220116483)
  ·
    refine ⟨131830842999369115830174725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87887228666246077220116483 131830842999369115830174725)
    ·
      refine ⟨24718283062381709218157761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131830842999369115830174725 24718283062381709218157761)
      ·
        refine ⟨18538712296786281913618321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24718283062381709218157761 18538712296786281913618321)
        ·
          refine ⟨13904034222589711435213741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18538712296786281913618321 13904034222589711435213741)
          ·
            refine ⟨5214012833471141788205153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13904034222589711435213741 5214012833471141788205153)
            ·
              refine ⟨3910509625103356341153865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5214012833471141788205153 3910509625103356341153865)
              ·
                refine ⟨2932882218827517255865399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3910509625103356341153865 2932882218827517255865399)
                ·
                  refine ⟨4399323328241275883798099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932882218827517255865399 4399323328241275883798099)
                  ·
                    refine ⟨6598984992361913825697149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4399323328241275883798099 6598984992361913825697149)
                    ·
                      refine ⟨2474619372135717684636431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6598984992361913825697149 2474619372135717684636431)
                      ·
                        rfl

theorem cell23_4819304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_4819304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819304 prefixEnd_4819304 := by exact prefixLift 4819304
  have htrace : WordTrace (prefixWord ++ tailWord_4819304) baseStart_4819304 baseEnd_4819304 := by
    simpa [prefixWord, tailWord_4819304, baseEnd_4819304] using wordTrace_append hprefix tailTrace_4819304
  have hstable : (prefixWord ++ tailWord_4819304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819304).length < 2 ^ (prefixWord ++ tailWord_4819304).sum := by decide
  have hdescent : baseEnd_4819304 < baseStart_4819304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819360 : List Nat := [2, 1, 1, 4, 1, 3, 3, 2, 2, 1, 3]
def baseStart_4819360 : Nat := 118140960795 + 4819360 * 2 ^ 59
def prefixEnd_4819360 : Nat := 4983230072969 + 3 ^ 40 * 4819360 * 2
def baseEnd_4819360 : Nat := 2474648127052369465536173

theorem tailTrace_4819360 : CollatzResearch.WordTrace tailWord_4819360 prefixEnd_4819360 2474648127052369465536173 := by
  unfold tailWord_4819360
  simp only [CollatzResearch.WordTrace]
  refine ⟨87888249910144638002135767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117184333213526184002847689 87888249910144638002135767)
  ·
    refine ⟨131832374865216957003203651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87888249910144638002135767 131832374865216957003203651)
    ·
      refine ⟨197748562297825435504805477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131832374865216957003203651 197748562297825435504805477)
      ·
        refine ⟨37077855430842269157151027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197748562297825435504805477 37077855430842269157151027)
        ·
          refine ⟨55616783146263403735726541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37077855430842269157151027 55616783146263403735726541)
          ·
            refine ⟨20856293679848776400897453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55616783146263403735726541 20856293679848776400897453)
            ·
              refine ⟨7821110129943291150336545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20856293679848776400897453 7821110129943291150336545)
              ·
                refine ⟨5865832597457468362752409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7821110129943291150336545 5865832597457468362752409)
                ·
                  refine ⟨4399374448093101272064307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5865832597457468362752409 4399374448093101272064307)
                  ·
                    refine ⟨6599061672139651908096461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4399374448093101272064307 6599061672139651908096461)
                    ·
                      refine ⟨2474648127052369465536173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6599061672139651908096461 2474648127052369465536173)
                      ·
                        rfl

theorem cell23_4819360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_4819360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819360 prefixEnd_4819360 := by exact prefixLift 4819360
  have htrace : WordTrace (prefixWord ++ tailWord_4819360) baseStart_4819360 baseEnd_4819360 := by
    simpa [prefixWord, tailWord_4819360, baseEnd_4819360] using wordTrace_append hprefix tailTrace_4819360
  have hstable : (prefixWord ++ tailWord_4819360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819360).length < 2 ^ (prefixWord ++ tailWord_4819360).sum := by decide
  have hdescent : baseEnd_4819360 < baseStart_4819360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819377 : List Nat := [1, 2, 2, 4, 1, 3, 3, 1, 2, 1, 3]
def baseStart_4819377 : Nat := 118140960795 + 4819377 * 2 ^ 59
def prefixEnd_4819377 : Nat := 4983230072969 + 3 ^ 40 * 4819377 * 2
def baseEnd_4819377 : Nat := 2474656856223495899023595

theorem tailTrace_4819377 : CollatzResearch.WordTrace tailWord_4819377 prefixEnd_4819377 2474656856223495899023595 := by
  unfold tailWord_4819377
  simp only [CollatzResearch.WordTrace]
  refine ⟨175777119861227687907640385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117184746574151791938426923 175777119861227687907640385)
  ·
    refine ⟨131832839895920765930730289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175777119861227687907640385 131832839895920765930730289)
    ·
      refine ⟨98874629921940574448047717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131832839895920765930730289 98874629921940574448047717)
      ·
        refine ⟨18538993110363857709008947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98874629921940574448047717 18538993110363857709008947)
        ·
          refine ⟨27808489665545786563513421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18538993110363857709008947 27808489665545786563513421)
          ·
            refine ⟨10428183624579669961317533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27808489665545786563513421 10428183624579669961317533)
            ·
              refine ⟨3910568859217376235494075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10428183624579669961317533 3910568859217376235494075)
              ·
                refine ⟨5865853288826064353241113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3910568859217376235494075 5865853288826064353241113)
                ·
                  refine ⟨4399389966619548264930835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5865853288826064353241113 4399389966619548264930835)
                  ·
                    refine ⟨6599084949929322397396253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4399389966619548264930835 6599084949929322397396253)
                    ·
                      refine ⟨2474656856223495899023595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6599084949929322397396253 2474656856223495899023595)
                      ·
                        rfl

theorem cell23_4819377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_4819377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819377 prefixEnd_4819377 := by exact prefixLift 4819377
  have htrace : WordTrace (prefixWord ++ tailWord_4819377) baseStart_4819377 baseEnd_4819377 := by
    simpa [prefixWord, tailWord_4819377, baseEnd_4819377] using wordTrace_append hprefix tailTrace_4819377
  have hstable : (prefixWord ++ tailWord_4819377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819377).length < 2 ^ (prefixWord ++ tailWord_4819377).sum := by decide
  have hdescent : baseEnd_4819377 < baseStart_4819377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819386 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3]
def baseStart_4819386 : Nat := 118140960795 + 4819386 * 2 ^ 59
def prefixEnd_4819386 : Nat := 4983230072969 + 3 ^ 40 * 4819386 * 2
def baseEnd_4819386 : Nat := 2474661477549386363811053

theorem tailTrace_4819386 : CollatzResearch.WordTrace tailWord_4819386 prefixEnd_4819386 2474661477549386363811053 := by
  unfold tailWord_4819386
  simp only [CollatzResearch.WordTrace]
  refine ⟨43944362029548770611179503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117184965412130054963145341 43944362029548770611179503)
  ·
    refine ⟨65916543044323155916769255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43944362029548770611179503 65916543044323155916769255)
    ·
      refine ⟨98874814566484733875153883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65916543044323155916769255 98874814566484733875153883)
      ·
        refine ⟨148312221849727100812730825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98874814566484733875153883 148312221849727100812730825)
        ·
          refine ⟨111234166387295325609548119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148312221849727100812730825 111234166387295325609548119)
          ·
            refine ⟨166851249580942988414322179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111234166387295325609548119 166851249580942988414322179)
            ·
              refine ⟨250276874371414482621483269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166851249580942988414322179 250276874371414482621483269)
              ·
                refine ⟨46926913944640215491528113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250276874371414482621483269 46926913944640215491528113)
                ·
                  refine ⟨35195185458480161618646085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46926913944640215491528113 35195185458480161618646085)
                  ·
                    refine ⟨6599097273465030303496141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35195185458480161618646085 6599097273465030303496141)
                    ·
                      refine ⟨2474661477549386363811053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6599097273465030303496141 2474661477549386363811053)
                      ·
                        rfl

theorem cell23_4819386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_4819386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819386 prefixEnd_4819386 := by exact prefixLift 4819386
  have htrace : WordTrace (prefixWord ++ tailWord_4819386) baseStart_4819386 baseEnd_4819386 := by
    simpa [prefixWord, tailWord_4819386, baseEnd_4819386] using wordTrace_append hprefix tailTrace_4819386
  have hstable : (prefixWord ++ tailWord_4819386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819386).length < 2 ^ (prefixWord ++ tailWord_4819386).sum := by decide
  have hdescent : baseEnd_4819386 < baseStart_4819386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819400 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 4, 2, 2]
def baseStart_4819400 : Nat := 118140960795 + 4819400 * 2 ^ 59
def prefixEnd_4819400 : Nat := 4983230072969 + 3 ^ 40 * 4819400 * 2
def baseEnd_4819400 : Nat := 2474668666278549309035989

theorem tailTrace_4819400 : CollatzResearch.WordTrace tailWord_4819400 prefixEnd_4819400 2474668666278549309035989 := by
  unfold tailWord_4819400
  simp only [CollatzResearch.WordTrace]
  refine ⟨87888979370072181417863827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117185305826762908557151769 87888979370072181417863827)
  ·
    refine ⟨131833469055108272126795741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87888979370072181417863827 131833469055108272126795741)
    ·
      refine ⟨49437550895665602047548403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131833469055108272126795741 49437550895665602047548403)
      ·
        refine ⟨74156326343498403071322605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49437550895665602047548403 74156326343498403071322605)
        ·
          refine ⟨27808622378811901151745977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74156326343498403071322605 27808622378811901151745977)
          ·
            refine ⟨20856466784108925863809483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27808622378811901151745977 20856466784108925863809483)
            ·
              refine ⟨31284700176163388795714225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20856466784108925863809483 31284700176163388795714225)
              ·
                refine ⟨23463525132122541596785669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31284700176163388795714225 23463525132122541596785669)
                ·
                  refine ⟨4399410962272976549397313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23463525132122541596785669 4399410962272976549397313)
                  ·
                    refine ⟨3299558221704732412047985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4399410962272976549397313 3299558221704732412047985)
                    ·
                      refine ⟨2474668666278549309035989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3299558221704732412047985 2474668666278549309035989)
                      ·
                        rfl

theorem cell23_4819400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_4819400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819400 prefixEnd_4819400 := by exact prefixLift 4819400
  have htrace : WordTrace (prefixWord ++ tailWord_4819400) baseStart_4819400 baseEnd_4819400 := by
    simpa [prefixWord, tailWord_4819400, baseEnd_4819400] using wordTrace_append hprefix tailTrace_4819400
  have hstable : (prefixWord ++ tailWord_4819400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819400).length < 2 ^ (prefixWord ++ tailWord_4819400).sum := by decide
  have hdescent : baseEnd_4819400 < baseStart_4819400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819423 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 7]
def baseStart_4819423 : Nat := 118140960795 + 4819423 * 2 ^ 59
def prefixEnd_4819423 : Nat := 4983230072969 + 3 ^ 40 * 4819423 * 2
def baseEnd_4819423 : Nat := 274964497370400302116487

theorem tailTrace_4819423 : CollatzResearch.WordTrace tailWord_4819423 prefixEnd_4819423 274964497370400302116487 := by
  unfold tailWord_4819423
  simp only [CollatzResearch.WordTrace]
  refine ⟨175778797619061037763814923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117185865079374025175876615 175778797619061037763814923)
  ·
    refine ⟨263668196428591556645722385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175778797619061037763814923 263668196428591556645722385)
    ·
      refine ⟨197751147321443667484291789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263668196428591556645722385 197751147321443667484291789)
      ·
        refine ⟨74156680245541375306609421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197751147321443667484291789 74156680245541375306609421)
        ·
          refine ⟨27808755092078015739978533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74156680245541375306609421 27808755092078015739978533)
          ·
            refine ⟨5214141579764627951245975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27808755092078015739978533 5214141579764627951245975)
            ·
              refine ⟨7821212369646941926868963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5214141579764627951245975 7821212369646941926868963)
              ·
                refine ⟨11731818554470412890303445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7821212369646941926868963 11731818554470412890303445)
                ·
                  refine ⟨274964497370400302116487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11731818554470412890303445 274964497370400302116487)
                  ·
                    rfl

theorem cell23_4819423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 7].length) (baseStart_4819423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819423 prefixEnd_4819423 := by exact prefixLift 4819423
  have htrace : WordTrace (prefixWord ++ tailWord_4819423) baseStart_4819423 baseEnd_4819423 := by
    simpa [prefixWord, tailWord_4819423, baseEnd_4819423] using wordTrace_append hprefix tailTrace_4819423
  have hstable : (prefixWord ++ tailWord_4819423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819423).length < 2 ^ (prefixWord ++ tailWord_4819423).sum := by decide
  have hdescent : baseEnd_4819423 < baseStart_4819423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819434 : List Nat := [3, 1, 3, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_4819434 : Nat := 118140960795 + 4819434 * 2 ^ 59
def prefixEnd_4819434 : Nat := 4983230072969 + 3 ^ 40 * 4819434 * 2
def baseEnd_4819434 : Nat := 2474686124620802176010833

theorem tailTrace_4819434 : CollatzResearch.WordTrace tailWord_4819434 prefixEnd_4819434 2474686124620802176010833 := by
  unfold tailWord_4819434
  simp only [CollatzResearch.WordTrace]
  refine ⟨43944799705505296660616339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117186132548014124428310237 43944799705505296660616339)
  ·
    refine ⟨65917199558257944990924509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43944799705505296660616339 65917199558257944990924509)
    ·
      refine ⟨24718949834346729371596691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65917199558257944990924509 24718949834346729371596691)
      ·
        refine ⟨37078424751520094057395037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24718949834346729371596691 37078424751520094057395037)
        ·
          refine ⟨13904409281820035271523139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37078424751520094057395037 13904409281820035271523139)
          ·
            refine ⟨20856613922730052907284709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13904409281820035271523139 20856613922730052907284709)
            ·
              refine ⟨3910615110511884920115883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20856613922730052907284709 3910615110511884920115883)
              ·
                refine ⟨5865922665767827380173825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3910615110511884920115883 5865922665767827380173825)
                ·
                  refine ⟨4399441999325870535130369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5865922665767827380173825 4399441999325870535130369)
                  ·
                    refine ⟨3299581499494402901347777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4399441999325870535130369 3299581499494402901347777)
                    ·
                      refine ⟨2474686124620802176010833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3299581499494402901347777 2474686124620802176010833)
                      ·
                        rfl

theorem cell23_4819434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_4819434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819434 prefixEnd_4819434 := by exact prefixLift 4819434
  have htrace : WordTrace (prefixWord ++ tailWord_4819434) baseStart_4819434 baseEnd_4819434 := by
    simpa [prefixWord, tailWord_4819434, baseEnd_4819434] using wordTrace_append hprefix tailTrace_4819434
  have hstable : (prefixWord ++ tailWord_4819434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819434).length < 2 ^ (prefixWord ++ tailWord_4819434).sum := by decide
  have hdescent : baseEnd_4819434 < baseStart_4819434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819436 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 4, 5]
def baseStart_4819436 : Nat := 118140960795 + 4819436 * 2 ^ 59
def prefixEnd_4819436 : Nat := 4983230072969 + 3 ^ 40 * 4819436 * 2
def baseEnd_4819436 : Nat := 824895717194037056061941

theorem tailTrace_4819436 : CollatzResearch.WordTrace tailWord_4819436 prefixEnd_4819436 824895717194037056061941 := by
  unfold tailWord_4819436
  simp only [CollatzResearch.WordTrace]
  refine ⟨87889635884006970492019081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117186181178675960656025441 87889635884006970492019081)
  ·
    refine ⟨65917226913005227869014311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87889635884006970492019081 65917226913005227869014311)
    ·
      refine ⟨98875840369507841803521467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65917226913005227869014311 98875840369507841803521467)
      ·
        refine ⟨148313760554261762705282201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98875840369507841803521467 148313760554261762705282201)
        ·
          refine ⟨111235320415696322028961651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148313760554261762705282201 111235320415696322028961651)
          ·
            refine ⟨166852980623544483043442477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111235320415696322028961651 166852980623544483043442477)
            ·
              refine ⟨62569867733829181141290929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166852980623544483043442477 62569867733829181141290929)
              ·
                refine ⟨46927400800371885855968197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62569867733829181141290929 46927400800371885855968197)
                ·
                  refine ⟨8798887650069728597994037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46927400800371885855968197 8798887650069728597994037)
                  ·
                    refine ⟨824895717194037056061941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8798887650069728597994037 824895717194037056061941)
                    ·
                      rfl

theorem cell23_4819436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_4819436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819436 prefixEnd_4819436 := by exact prefixLift 4819436
  have htrace : WordTrace (prefixWord ++ tailWord_4819436) baseStart_4819436 baseEnd_4819436 := by
    simpa [prefixWord, tailWord_4819436, baseEnd_4819436] using wordTrace_append hprefix tailTrace_4819436
  have hstable : (prefixWord ++ tailWord_4819436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819436).length < 2 ^ (prefixWord ++ tailWord_4819436).sum := by decide
  have hdescent : baseEnd_4819436 < baseStart_4819436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819453 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_4819453 : Nat := 118140960795 + 4819453 * 2 ^ 59
def prefixEnd_4819453 : Nat := 4983230072969 + 3 ^ 40 * 4819453 * 2
def baseEnd_4819453 : Nat := 824898626917745867224415

theorem tailTrace_4819453 : CollatzResearch.WordTrace tailWord_4819453 prefixEnd_4819453 824898626917745867224415 := by
  unfold tailWord_4819453
  simp only [CollatzResearch.WordTrace]
  refine ⟨175779891808952352887407013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117186594539301568591604675 175779891808952352887407013)
  ·
    refine ⟨32958729714178566166388815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175779891808952352887407013 32958729714178566166388815)
    ·
      refine ⟨49438094571267849249583223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32958729714178566166388815 49438094571267849249583223)
      ·
        refine ⟨74157141856901773874374835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49438094571267849249583223 74157141856901773874374835)
        ·
          refine ⟨111235712785352660811562253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74157141856901773874374835 111235712785352660811562253)
          ·
            refine ⟨41713392294507247804335845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111235712785352660811562253 41713392294507247804335845)
            ·
              refine ⟨7821261055220108963312971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41713392294507247804335845 7821261055220108963312971)
              ·
                refine ⟨11731891582830163444969457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7821261055220108963312971 11731891582830163444969457)
                ·
                  refine ⟨8798918687122622583727093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11731891582830163444969457 8798918687122622583727093)
                  ·
                    refine ⟨824898626917745867224415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8798918687122622583727093 824898626917745867224415)
                    ·
                      rfl

theorem cell23_4819453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_4819453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819453 prefixEnd_4819453 := by exact prefixLift 4819453
  have htrace : WordTrace (prefixWord ++ tailWord_4819453) baseStart_4819453 baseEnd_4819453 := by
    simpa [prefixWord, tailWord_4819453, baseEnd_4819453] using wordTrace_append hprefix tailTrace_4819453
  have hstable : (prefixWord ++ tailWord_4819453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819453).length < 2 ^ (prefixWord ++ tailWord_4819453).sum := by decide
  have hdescent : baseEnd_4819453 < baseStart_4819453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819493 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 4, 2, 3]
def baseStart_4819493 : Nat := 118140960795 + 4819493 * 2 ^ 59
def prefixEnd_4819493 : Nat := 4983230072969 + 3 ^ 40 * 4819493 * 2
def baseEnd_4819493 : Nat := 2474716419979417445173061

theorem tailTrace_4819493 : CollatzResearch.WordTrace tailWord_4819493 prefixEnd_4819493 2474716419979417445173061 := by
  unfold tailWord_4819493
  simp only [CollatzResearch.WordTrace]
  refine ⟨175781350728807439718863133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117187567152538293145908755 175781350728807439718863133)
  ·
    refine ⟨65918006523302789894573675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175781350728807439718863133 65918006523302789894573675)
    ·
      refine ⟨98877009784954184841860513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65918006523302789894573675 98877009784954184841860513)
      ·
        refine ⟨74157757338715638631395385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98877009784954184841860513 74157757338715638631395385)
        ·
          refine ⟨55618318004036728973546539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74157757338715638631395385 55618318004036728973546539)
          ·
            refine ⟨83427477006055093460319809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55618318004036728973546539 83427477006055093460319809)
            ·
              refine ⟨62570607754541320095239857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83427477006055093460319809 62570607754541320095239857)
              ·
                refine ⟨46927955815905990071429893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62570607754541320095239857 46927955815905990071429893)
                ·
                  refine ⟨8798991715482373138393105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46927955815905990071429893 8798991715482373138393105)
                  ·
                    refine ⟨6599243786611779853794829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8798991715482373138393105 6599243786611779853794829)
                    ·
                      refine ⟨2474716419979417445173061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6599243786611779853794829 2474716419979417445173061)
                      ·
                        rfl

theorem cell23_4819493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_4819493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819493 prefixEnd_4819493 := by exact prefixLift 4819493
  have htrace : WordTrace (prefixWord ++ tailWord_4819493) baseStart_4819493 baseEnd_4819493 := by
    simpa [prefixWord, tailWord_4819493, baseEnd_4819493] using wordTrace_append hprefix tailTrace_4819493
  have hstable : (prefixWord ++ tailWord_4819493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819493).length < 2 ^ (prefixWord ++ tailWord_4819493).sum := by decide
  have hdescent : baseEnd_4819493 < baseStart_4819493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819517 : List Nat := [1, 4, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_4819517 : Nat := 118140960795 + 4819517 * 2 ^ 59
def prefixEnd_4819517 : Nat := 4983230072969 + 3 ^ 40 * 4819517 * 2
def baseEnd_4819517 : Nat := 824909581171708450424317

theorem tailTrace_4819517 : CollatzResearch.WordTrace tailWord_4819517 prefixEnd_4819517 824909581171708450424317 := by
  unfold tailWord_4819517
  simp only [CollatzResearch.WordTrace]
  refine ⟨175782226080720491817736805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117188150720480327878491203 175782226080720491817736805)
  ·
    refine ⟨32959167390135092215825651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175782226080720491817736805 32959167390135092215825651)
    ·
      refine ⟨49438751085202638323738477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32959167390135092215825651 49438751085202638323738477)
      ·
        refine ⟨18539531656950989371401929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49438751085202638323738477 18539531656950989371401929)
        ·
          refine ⟨13904648742713242028551447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18539531656950989371401929 13904648742713242028551447)
          ·
            refine ⟨20856973114069863042827171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13904648742713242028551447 20856973114069863042827171)
            ·
              refine ⟨31285459671104794564240757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20856973114069863042827171 31285459671104794564240757)
              ·
                refine ⟨2933011844166074490397571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31285459671104794564240757 2933011844166074490397571)
                ·
                  refine ⟨4399517766249111735596357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933011844166074490397571 4399517766249111735596357)
                  ·
                    refine ⟨824909581171708450424317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4399517766249111735596357 824909581171708450424317)
                    ·
                      rfl

theorem cell23_4819517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_4819517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819517 prefixEnd_4819517 := by exact prefixLift 4819517
  have htrace : WordTrace (prefixWord ++ tailWord_4819517) baseStart_4819517 baseEnd_4819517 := by
    simpa [prefixWord, tailWord_4819517, baseEnd_4819517] using wordTrace_append hprefix tailTrace_4819517
  have hstable : (prefixWord ++ tailWord_4819517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819517).length < 2 ^ (prefixWord ++ tailWord_4819517).sum := by decide
  have hdescent : baseEnd_4819517 < baseStart_4819517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819530 : List Nat := [3, 1, 2, 1, 1, 6, 1, 2, 6]
def baseStart_4819530 : Nat := 118140960795 + 4819530 * 2 ^ 59
def prefixEnd_4819530 : Nat := 4983230072969 + 3 ^ 40 * 4819530 * 2
def baseEnd_4819530 : Nat := 274970602084848200045599

theorem tailTrace_4819530 : CollatzResearch.WordTrace tailWord_4819530 prefixEnd_4819530 274970602084848200045599 := by
  unfold tailWord_4819530
  simp only [CollatzResearch.WordTrace]
  refine ⟨43945675057418348759490011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117188466819782263358640029 43945675057418348759490011)
  ·
    refine ⟨65918512586127523139235017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43945675057418348759490011 65918512586127523139235017)
    ·
      refine ⟨49438884439595642354426263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65918512586127523139235017 49438884439595642354426263)
      ·
        refine ⟨74158326659393463531639395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49438884439595642354426263 74158326659393463531639395)
        ·
          refine ⟨111237489989090195297459093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74158326659393463531639395 111237489989090195297459093)
          ·
            refine ⟨5214257343238602904568395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111237489989090195297459093 5214257343238602904568395)
            ·
              refine ⟨7821386014857904356852593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5214257343238602904568395 7821386014857904356852593)
              ·
                refine ⟨5866039511143428267639445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7821386014857904356852593 5866039511143428267639445)
                ·
                  refine ⟨274970602084848200045599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5866039511143428267639445 274970602084848200045599)
                  ·
                    rfl

theorem cell23_4819530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_4819530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819530 prefixEnd_4819530 := by exact prefixLift 4819530
  have htrace : WordTrace (prefixWord ++ tailWord_4819530) baseStart_4819530 baseEnd_4819530 := by
    simpa [prefixWord, tailWord_4819530, baseEnd_4819530] using wordTrace_append hprefix tailTrace_4819530
  have hstable : (prefixWord ++ tailWord_4819530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819530).length < 2 ^ (prefixWord ++ tailWord_4819530).sum := by decide
  have hdescent : baseEnd_4819530 < baseStart_4819530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819536 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 7]
def baseStart_4819536 : Nat := 118140960795 + 4819536 * 2 ^ 59
def prefixEnd_4819536 : Nat := 4983230072969 + 3 ^ 40 * 4819536 * 2
def baseEnd_4819536 : Nat := 2474738499647560776935363

theorem tailTrace_4819536 : CollatzResearch.WordTrace tailWord_4819536 prefixEnd_4819536 2474738499647560776935363 := by
  unfold tailWord_4819536
  simp only [CollatzResearch.WordTrace]
  refine ⟨87891459533825829031339231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117188612711767772041785641 87891459533825829031339231)
  ·
    refine ⟨131837189300738743547008847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87891459533825829031339231 131837189300738743547008847)
    ·
      refine ⟨197755783951108115320513271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131837189300738743547008847 197755783951108115320513271)
      ·
        refine ⟨296633675926662172980769907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197755783951108115320513271 296633675926662172980769907)
        ·
          refine ⟨444950513889993259471154861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296633675926662172980769907 444950513889993259471154861)
          ·
            refine ⟨166856442708747472301683073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 444950513889993259471154861 166856442708747472301683073)
            ·
              refine ⟨125142332031560604226262305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166856442708747472301683073 125142332031560604226262305)
              ·
                refine ⟨93856749023670453169696729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125142332031560604226262305 93856749023670453169696729)
                ·
                  refine ⟨70392561767752839877272547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93856749023670453169696729 70392561767752839877272547)
                  ·
                    refine ⟨105588842651629259815908821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70392561767752839877272547 105588842651629259815908821)
                    ·
                      refine ⟨2474738499647560776935363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105588842651629259815908821 2474738499647560776935363)
                      ·
                        rfl

theorem cell23_4819536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_4819536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819536 prefixEnd_4819536 := by exact prefixLift 4819536
  have htrace : WordTrace (prefixWord ++ tailWord_4819536) baseStart_4819536 baseEnd_4819536 := by
    simpa [prefixWord, tailWord_4819536, baseEnd_4819536] using wordTrace_append hprefix tailTrace_4819536
  have hstable : (prefixWord ++ tailWord_4819536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819536).length < 2 ^ (prefixWord ++ tailWord_4819536).sum := by decide
  have hdescent : baseEnd_4819536 < baseStart_4819536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819580 : List Nat := [2, 2, 2, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_4819580 : Nat := 118140960795 + 4819580 * 2 ^ 59
def prefixEnd_4819580 : Nat := 4983230072969 + 3 ^ 40 * 4819580 * 2
def baseEnd_4819580 : Nat := 2474761092796358604785161

theorem tailTrace_4819580 : CollatzResearch.WordTrace tailWord_4819580 prefixEnd_4819580 2474761092796358604785161 := by
  unfold tailWord_4819580
  simp only [CollatzResearch.WordTrace]
  refine ⟨87892261939746126788640097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117189682586328169051520129 87892261939746126788640097)
  ·
    refine ⟨65919196454809595091480073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87892261939746126788640097 65919196454809595091480073)
    ·
      refine ⟨49439397341107196318610055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65919196454809595091480073 49439397341107196318610055)
      ·
        refine ⟨74159096011660794477915083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49439397341107196318610055 74159096011660794477915083)
        ·
          refine ⟨111238644017491191716872625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74159096011660794477915083 111238644017491191716872625)
          ·
            refine ⟨83428983013118393787654469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111238644017491191716872625 83428983013118393787654469)
            ·
              refine ⟨15642934314959698835185213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83428983013118393787654469 15642934314959698835185213)
              ·
                refine ⟨5866100368109887063194455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15642934314959698835185213 5866100368109887063194455)
                ·
                  refine ⟨8799150552164830594791683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5866100368109887063194455 8799150552164830594791683)
                  ·
                    refine ⟨13198725828247245892187525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8799150552164830594791683 13198725828247245892187525)
                    ·
                      refine ⟨2474761092796358604785161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13198725828247245892187525 2474761092796358604785161)
                      ·
                        rfl

theorem cell23_4819580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_4819580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819580 prefixEnd_4819580 := by exact prefixLift 4819580
  have htrace : WordTrace (prefixWord ++ tailWord_4819580) baseStart_4819580 baseEnd_4819580 := by
    simpa [prefixWord, tailWord_4819580, baseEnd_4819580] using wordTrace_append hprefix tailTrace_4819580
  have hstable : (prefixWord ++ tailWord_4819580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819580).length < 2 ^ (prefixWord ++ tailWord_4819580).sum := by decide
  have hdescent : baseEnd_4819580 < baseStart_4819580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819614 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_4819614 : Nat := 118140960795 + 4819614 * 2 ^ 59
def prefixEnd_4819614 : Nat := 4983230072969 + 3 ^ 40 * 4819614 * 2
def baseEnd_4819614 : Nat := 2474778551138611471760005

theorem tailTrace_4819614 : CollatzResearch.WordTrace tailWord_4819614 prefixEnd_4819614 2474778551138611471760005 := by
  unfold tailWord_4819614
  simp only [CollatzResearch.WordTrace]
  refine ⟨21973220495171134673002237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117190509307579384922678597 21973220495171134673002237)
  ·
    refine ⟨8239957685689175502375839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21973220495171134673002237 8239957685689175502375839)
    ·
      refine ⟨12359936528533763253563759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8239957685689175502375839 12359936528533763253563759)
      ·
        refine ⟨18539904792800644880345639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12359936528533763253563759 18539904792800644880345639)
        ·
          refine ⟨27809857189200967320518459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18539904792800644880345639 27809857189200967320518459)
          ·
            refine ⟨41714785783801450980777689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27809857189200967320518459 41714785783801450980777689)
            ·
              refine ⟨31286089337851088235583267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41714785783801450980777689 31286089337851088235583267)
              ·
                refine ⟨46929134006776632353374901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31286089337851088235583267 46929134006776632353374901)
                ·
                  refine ⟨4399606313135309283128897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46929134006776632353374901 4399606313135309283128897)
                  ·
                    refine ⟨3299704734851481962346673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4399606313135309283128897 3299704734851481962346673)
                    ·
                      refine ⟨2474778551138611471760005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3299704734851481962346673 2474778551138611471760005)
                      ·
                        rfl

theorem cell23_4819614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_4819614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819614 prefixEnd_4819614 := by exact prefixLift 4819614
  have htrace : WordTrace (prefixWord ++ tailWord_4819614) baseStart_4819614 baseEnd_4819614 := by
    simpa [prefixWord, tailWord_4819614, baseEnd_4819614] using wordTrace_append hprefix tailTrace_4819614
  have hstable : (prefixWord ++ tailWord_4819614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819614).length < 2 ^ (prefixWord ++ tailWord_4819614).sum := by decide
  have hdescent : baseEnd_4819614 < baseStart_4819614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819617 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_4819617 : Nat := 118140960795 + 4819617 * 2 ^ 59
def prefixEnd_4819617 : Nat := 4983230072969 + 3 ^ 40 * 4819617 * 2
def baseEnd_4819617 : Nat := 2474780091580574960022491

theorem tailTrace_4819617 : CollatzResearch.WordTrace tailWord_4819617 prefixEnd_4819617 2474780091580574960022491 := by
  unfold tailWord_4819617
  simp only [CollatzResearch.WordTrace]
  refine ⟨175785873380358208896377105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117190582253572139264251403 175785873380358208896377105)
  ·
    refine ⟨131839405035268656672282829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175785873380358208896377105 131839405035268656672282829)
    ·
      refine ⟨49439776888225746252106061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131839405035268656672282829 49439776888225746252106061)
      ·
        refine ⟨18539916333084654844539773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49439776888225746252106061 18539916333084654844539773)
        ·
          refine ⟨6952468624906745566702415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18539916333084654844539773 6952468624906745566702415)
          ·
            refine ⟨10428702937360118350053623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6952468624906745566702415 10428702937360118350053623)
            ·
              refine ⟨15643054406040177525080435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10428702937360118350053623 15643054406040177525080435)
              ·
                refine ⟨23464581609060266287620653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15643054406040177525080435 23464581609060266287620653)
                ·
                  refine ⟨8799218103397599857857745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23464581609060266287620653 8799218103397599857857745)
                  ·
                    refine ⟨6599413577548199893393309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8799218103397599857857745 6599413577548199893393309)
                    ·
                      refine ⟨2474780091580574960022491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6599413577548199893393309 2474780091580574960022491)
                      ·
                        rfl

theorem cell23_4819617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_4819617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819617 prefixEnd_4819617 := by exact prefixLift 4819617
  have htrace : WordTrace (prefixWord ++ tailWord_4819617) baseStart_4819617 baseEnd_4819617 := by
    simpa [prefixWord, tailWord_4819617, baseEnd_4819617] using wordTrace_append hprefix tailTrace_4819617
  have hstable : (prefixWord ++ tailWord_4819617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819617).length < 2 ^ (prefixWord ++ tailWord_4819617).sum := by decide
  have hdescent : baseEnd_4819617 < baseStart_4819617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819647 : List Nat := [1, 1, 2, 2, 2, 4, 1, 4, 2, 1, 3]
def baseStart_4819647 : Nat := 118140960795 + 4819647 * 2 ^ 59
def prefixEnd_4819647 : Nat := 4983230072969 + 3 ^ 40 * 4819647 * 2
def baseEnd_4819647 : Nat := 2474795496000209842647353

theorem tailTrace_4819647 : CollatzResearch.WordTrace tailWord_4819647 prefixEnd_4819647 2474795496000209842647353 := by
  unfold tailWord_4819647
  simp only [CollatzResearch.WordTrace]
  refine ⟨175786967570249524019969195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117191311713499682679979463 175786967570249524019969195)
  ·
    refine ⟨263680451355374286029953793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175786967570249524019969195 263680451355374286029953793)
    ·
      refine ⟨197760338516530714522465345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263680451355374286029953793 197760338516530714522465345)
      ·
        refine ⟨148320253887398035891849009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197760338516530714522465345 148320253887398035891849009)
        ·
          refine ⟨111240190415548526918886757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148320253887398035891849009 111240190415548526918886757)
          ·
            refine ⟨20857535702915348797291267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111240190415548526918886757 20857535702915348797291267)
            ·
              refine ⟨31286303554373023195936901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20857535702915348797291267 31286303554373023195936901)
              ·
                refine ⟨5866181916444941849238169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31286303554373023195936901 5866181916444941849238169)
                ·
                  refine ⟨4399636437333706386928627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5866181916444941849238169 4399636437333706386928627)
                  ·
                    refine ⟨6599454656000559580392941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4399636437333706386928627 6599454656000559580392941)
                    ·
                      refine ⟨2474795496000209842647353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6599454656000559580392941 2474795496000209842647353)
                      ·
                        rfl

theorem cell23_4819647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_4819647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819647 prefixEnd_4819647 := by exact prefixLift 4819647
  have htrace : WordTrace (prefixWord ++ tailWord_4819647) baseStart_4819647 baseEnd_4819647 := by
    simpa [prefixWord, tailWord_4819647, baseEnd_4819647] using wordTrace_append hprefix tailTrace_4819647
  have hstable : (prefixWord ++ tailWord_4819647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819647).length < 2 ^ (prefixWord ++ tailWord_4819647).sum := by decide
  have hdescent : baseEnd_4819647 < baseStart_4819647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819648 : List Nat := [2, 1, 1, 2, 4, 4, 2, 2, 1, 2, 2]
def baseStart_4819648 : Nat := 118140960795 + 4819648 * 2 ^ 59
def prefixEnd_4819648 : Nat := 4983230072969 + 3 ^ 40 * 4819648 * 2
def baseEnd_4819648 : Nat := 2474796009480864338734849

theorem tailTrace_4819648 : CollatzResearch.WordTrace tailWord_4819648 prefixEnd_4819648 2474796009480864338734849 := by
  unfold tailWord_4819648
  simp only [CollatzResearch.WordTrace]
  refine ⟨87893502021622950595377799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117191336028830600793837065 87893502021622950595377799)
  ·
    refine ⟨131840253032434425893066699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87893502021622950595377799 131840253032434425893066699)
    ·
      refine ⟨197760379548651638839600049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131840253032434425893066699 197760379548651638839600049)
      ·
        refine ⟨148320284661488729129700037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197760379548651638839600049 148320284661488729129700037)
        ·
          refine ⟨27810053374029136711818757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148320284661488729129700037 27810053374029136711818757)
          ·
            refine ⟨5214385007630463133466017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27810053374029136711818757 5214385007630463133466017)
            ·
              refine ⟨3910788755722847350099513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5214385007630463133466017 3910788755722847350099513)
              ·
                refine ⟨2933091566792135512574635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3910788755722847350099513 2933091566792135512574635)
                ·
                  refine ⟨4399637350188203268861953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933091566792135512574635 4399637350188203268861953)
                  ·
                    refine ⟨3299728012641152451646465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4399637350188203268861953 3299728012641152451646465)
                    ·
                      refine ⟨2474796009480864338734849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3299728012641152451646465 2474796009480864338734849)
                      ·
                        rfl

theorem cell23_4819648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 1, 2, 2].length) (baseStart_4819648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819648 prefixEnd_4819648 := by exact prefixLift 4819648
  have htrace : WordTrace (prefixWord ++ tailWord_4819648) baseStart_4819648 baseEnd_4819648 := by
    simpa [prefixWord, tailWord_4819648, baseEnd_4819648] using wordTrace_append hprefix tailTrace_4819648
  have hstable : (prefixWord ++ tailWord_4819648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819648).length < 2 ^ (prefixWord ++ tailWord_4819648).sum := by decide
  have hdescent : baseEnd_4819648 < baseStart_4819648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819740 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 1, 7]
def baseStart_4819740 : Nat := 118140960795 + 4819740 * 2 ^ 59
def prefixEnd_4819740 : Nat := 4983230072969 + 3 ^ 40 * 4819740 * 2
def baseEnd_4819740 : Nat := 824947749900359326261475

theorem tailTrace_4819740 : CollatzResearch.WordTrace tailWord_4819740 prefixEnd_4819740 824947749900359326261475 := by
  unfold tailWord_4819740
  simp only [CollatzResearch.WordTrace]
  refine ⟨87895179779456300451552337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117193573039275067268736449 87895179779456300451552337)
  ·
    refine ⟨65921384834592225338664253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87895179779456300451552337 65921384834592225338664253)
    ·
      refine ⟨24720519312972084501999095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65921384834592225338664253 24720519312972084501999095)
      ·
        refine ⟨37080778969458126752998643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24720519312972084501999095 37080778969458126752998643)
        ·
          refine ⟨55621168454187190129497965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37080778969458126752998643 55621168454187190129497965)
          ·
            refine ⟨20857938170320196298561737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55621168454187190129497965 20857938170320196298561737)
            ·
              refine ⟨15643453627740147223921303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20857938170320196298561737 15643453627740147223921303)
              ·
                refine ⟨23465180441610220835881955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15643453627740147223921303 23465180441610220835881955)
                ·
                  refine ⟨35197770662415331253822933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23465180441610220835881955 35197770662415331253822933)
                  ·
                    refine ⟨824947749900359326261475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35197770662415331253822933 824947749900359326261475)
                    ·
                      rfl

theorem cell23_4819740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_4819740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819740 prefixEnd_4819740 := by exact prefixLift 4819740
  have htrace : WordTrace (prefixWord ++ tailWord_4819740) baseStart_4819740 baseEnd_4819740 := by
    simpa [prefixWord, tailWord_4819740, baseEnd_4819740] using wordTrace_append hprefix tailTrace_4819740
  have hstable : (prefixWord ++ tailWord_4819740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819740).length < 2 ^ (prefixWord ++ tailWord_4819740).sum := by decide
  have hdescent : baseEnd_4819740 < baseStart_4819740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819744 : List Nat := [2, 1, 1, 5, 1, 4, 1, 3, 5]
def baseStart_4819744 : Nat := 118140960795 + 4819744 * 2 ^ 59
def prefixEnd_4819744 : Nat := 4983230072969 + 3 ^ 40 * 4819744 * 2
def baseEnd_4819744 : Nat := 274982811513743995903823

theorem tailTrace_4819744 : CollatzResearch.WordTrace tailWord_4819744 prefixEnd_4819744 274982811513743995903823 := by
  unfold tailWord_4819744
  simp only [CollatzResearch.WordTrace]
  refine ⟨87895252725449054793125143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117193670300598739724166857 87895252725449054793125143)
  ·
    refine ⟨131842879088173582189687715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87895252725449054793125143 131842879088173582189687715)
    ·
      refine ⟨197764318632260373284531573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131842879088173582189687715 197764318632260373284531573)
      ·
        refine ⟨18540404871774409995424835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197764318632260373284531573 18540404871774409995424835)
        ·
          refine ⟨27810607307661614993137253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18540404871774409995424835 27810607307661614993137253)
          ·
            refine ⟨5214488870186552811213235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27810607307661614993137253 5214488870186552811213235)
            ·
              refine ⟨7821733305279829216819853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5214488870186552811213235 7821733305279829216819853)
              ·
                refine ⟨2933149989479935956307445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7821733305279829216819853 2933149989479935956307445)
                ·
                  refine ⟨274982811513743995903823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2933149989479935956307445 274982811513743995903823)
                  ·
                    rfl

theorem cell23_4819744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 5].length) (baseStart_4819744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819744 prefixEnd_4819744 := by exact prefixLift 4819744
  have htrace : WordTrace (prefixWord ++ tailWord_4819744) baseStart_4819744 baseEnd_4819744 := by
    simpa [prefixWord, tailWord_4819744, baseEnd_4819744] using wordTrace_append hprefix tailTrace_4819744
  have hstable : (prefixWord ++ tailWord_4819744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819744).length < 2 ^ (prefixWord ++ tailWord_4819744).sum := by decide
  have hdescent : baseEnd_4819744 < baseStart_4819744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819753 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 1, 10]
def baseStart_4819753 : Nat := 118140960795 + 4819753 * 2 ^ 59
def prefixEnd_4819753 : Nat := 4983230072969 + 3 ^ 40 * 4819753 * 2
def baseEnd_4819753 : Nat := 824949974983195475973955

theorem tailTrace_4819753 : CollatzResearch.WordTrace tailWord_4819753 prefixEnd_4819753 824949974983195475973955 := by
  unfold tailWord_4819753
  simp only [CollatzResearch.WordTrace]
  refine ⟨175790833707865504123327913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117193889138577002748885275 175790833707865504123327913)
  ·
    refine ⟨131843125280899128092495935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175790833707865504123327913 131843125280899128092495935)
    ·
      refine ⟨197764687921348692138743903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131843125280899128092495935 197764687921348692138743903)
      ·
        refine ⟨296647031882023038208115855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197764687921348692138743903 296647031882023038208115855)
        ·
          refine ⟨444970547823034557312173783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296647031882023038208115855 444970547823034557312173783)
          ·
            refine ⟨667455821734551835968260675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444970547823034557312173783 667455821734551835968260675)
            ·
              refine ⟨1001183732601827753952391013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667455821734551835968260675 1001183732601827753952391013)
              ·
                refine ⟨187721949862842703866073315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1001183732601827753952391013 187721949862842703866073315)
                ·
                  refine ⟨281582924794264055799109973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187721949862842703866073315 281582924794264055799109973)
                  ·
                    refine ⟨824949974983195475973955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 281582924794264055799109973 824949974983195475973955)
                    ·
                      rfl

theorem cell23_4819753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_4819753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819753 prefixEnd_4819753 := by exact prefixLift 4819753
  have htrace : WordTrace (prefixWord ++ tailWord_4819753) baseStart_4819753 baseEnd_4819753 := by
    simpa [prefixWord, tailWord_4819753, baseEnd_4819753] using wordTrace_append hprefix tailTrace_4819753
  have hstable : (prefixWord ++ tailWord_4819753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819753).length < 2 ^ (prefixWord ++ tailWord_4819753).sum := by decide
  have hdescent : baseEnd_4819753 < baseStart_4819753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819790 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_4819790 : Nat := 118140960795 + 4819790 * 2 ^ 59
def prefixEnd_4819790 : Nat := 4983230072969 + 3 ^ 40 * 4819790 * 2
def baseEnd_4819790 : Nat := 2474868923733802783159195

theorem tailTrace_4819790 : CollatzResearch.WordTrace tailWord_4819790 prefixEnd_4819790 2474868923733802783159195 := by
  unfold tailWord_4819790
  simp only [CollatzResearch.WordTrace]
  refine ⟨21974022901091432430303103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117194788805820972961616549 21974022901091432430303103)
  ·
    refine ⟨32961034351637148645454655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21974022901091432430303103 32961034351637148645454655)
    ·
      refine ⟨49441551527455722968181983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32961034351637148645454655 49441551527455722968181983)
      ·
        refine ⟨74162327291183584452272975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49441551527455722968181983 74162327291183584452272975)
        ·
          refine ⟨111243490936775376678409463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74162327291183584452272975 111243490936775376678409463)
          ·
            refine ⟨166865236405163065017614195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111243490936775376678409463 166865236405163065017614195)
            ·
              refine ⟨250297854607744597526421293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166865236405163065017614195 250297854607744597526421293)
              ·
                refine ⟨93861695477904224072407985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250297854607744597526421293 93861695477904224072407985)
                ·
                  refine ⟨70396271608428168054305989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93861695477904224072407985 70396271608428168054305989)
                  ·
                    refine ⟨13199300926580281510182373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70396271608428168054305989 13199300926580281510182373)
                    ·
                      refine ⟨2474868923733802783159195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13199300926580281510182373 2474868923733802783159195)
                      ·
                        rfl

theorem cell23_4819790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_4819790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819790 prefixEnd_4819790 := by exact prefixLift 4819790
  have htrace : WordTrace (prefixWord ++ tailWord_4819790) baseStart_4819790 baseEnd_4819790 := by
    simpa [prefixWord, tailWord_4819790, baseEnd_4819790] using wordTrace_append hprefix tailTrace_4819790
  have hstable : (prefixWord ++ tailWord_4819790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819790).length < 2 ^ (prefixWord ++ tailWord_4819790).sum := by decide
  have hdescent : baseEnd_4819790 < baseStart_4819790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819820 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_4819820 : Nat := 118140960795 + 4819820 * 2 ^ 59
def prefixEnd_4819820 : Nat := 4983230072969 + 3 ^ 40 * 4819820 * 2
def baseEnd_4819820 : Nat := 2474884328153437665784057

theorem tailTrace_4819820 : CollatzResearch.WordTrace tailWord_4819820 prefixEnd_4819820 2474884328153437665784057 := by
  unfold tailWord_4819820
  simp only [CollatzResearch.WordTrace]
  refine ⟨87896638699311387283008457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117195518265748516377344609 87896638699311387283008457)
  ·
    refine ⟨65922479024483540462256343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87896638699311387283008457 65922479024483540462256343)
    ·
      refine ⟨98883718536725310693384515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65922479024483540462256343 98883718536725310693384515)
      ·
        refine ⟨148325577805087966040076773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98883718536725310693384515 148325577805087966040076773)
        ·
          refine ⟨27811045838453993632514395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148325577805087966040076773 27811045838453993632514395)
          ·
            refine ⟨41716568757680990448771593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27811045838453993632514395 41716568757680990448771593)
            ·
              refine ⟨31287426568260742836578695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41716568757680990448771593 31287426568260742836578695)
              ·
                refine ⟨46931139852391114254868043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31287426568260742836578695 46931139852391114254868043)
                ·
                  refine ⟨70396709778586671382302065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46931139852391114254868043 70396709778586671382302065)
                  ·
                    refine ⟨52797532333940003536726549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70396709778586671382302065 52797532333940003536726549)
                    ·
                      refine ⟨2474884328153437665784057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52797532333940003536726549 2474884328153437665784057)
                      ·
                        rfl

theorem cell23_4819820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_4819820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819820 prefixEnd_4819820 := by exact prefixLift 4819820
  have htrace : WordTrace (prefixWord ++ tailWord_4819820) baseStart_4819820 baseEnd_4819820 := by
    simpa [prefixWord, tailWord_4819820, baseEnd_4819820] using wordTrace_append hprefix tailTrace_4819820
  have hstable : (prefixWord ++ tailWord_4819820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819820).length < 2 ^ (prefixWord ++ tailWord_4819820).sum := by decide
  have hdescent : baseEnd_4819820 < baseStart_4819820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819847 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 3, 5]
def baseStart_4819847 : Nat := 118140960795 + 4819847 * 2 ^ 59
def prefixEnd_4819847 : Nat := 4983230072969 + 3 ^ 40 * 4819847 * 2
def baseEnd_4819847 : Nat := 824966064043703020048811

theorem tailTrace_4819847 : CollatzResearch.WordTrace tailWord_4819847 prefixEnd_4819847 824966064043703020048811 := by
  unfold tailWord_4819847
  simp only [CollatzResearch.WordTrace]
  refine ⟨175794262169524958177249795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117196174779683305451499863 175794262169524958177249795)
  ·
    refine ⟨263691393254287437265874693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175794262169524958177249795 263691393254287437265874693)
    ·
      refine ⟨49442136235178894487351505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 263691393254287437265874693 49442136235178894487351505)
      ·
        refine ⟨37081602176384170865513629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49442136235178894487351505 37081602176384170865513629)
        ·
          refine ⟨13905600816144064074567611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37081602176384170865513629 13905600816144064074567611)
          ·
            refine ⟨20858401224216096111851417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13905600816144064074567611 20858401224216096111851417)
            ·
              refine ⟨15643800918162072083888563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20858401224216096111851417 15643800918162072083888563)
              ·
                refine ⟨23465701377243108125832845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15643800918162072083888563 23465701377243108125832845)
                ·
                  refine ⟨8799638016466165547187317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23465701377243108125832845 8799638016466165547187317)
                  ·
                    refine ⟨824966064043703020048811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8799638016466165547187317 824966064043703020048811)
                    ·
                      rfl

theorem cell23_4819847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_4819847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819847 prefixEnd_4819847 := by exact prefixLift 4819847
  have htrace : WordTrace (prefixWord ++ tailWord_4819847) baseStart_4819847 baseEnd_4819847 := by
    simpa [prefixWord, tailWord_4819847, baseEnd_4819847] using wordTrace_append hprefix tailTrace_4819847
  have hstable : (prefixWord ++ tailWord_4819847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819847).length < 2 ^ (prefixWord ++ tailWord_4819847).sum := by decide
  have hdescent : baseEnd_4819847 < baseStart_4819847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819861 : List Nat := [1, 3, 2, 1, 1, 4, 1, 5, 1, 1, 3]
def baseStart_4819861 : Nat := 118140960795 + 4819861 * 2 ^ 59
def prefixEnd_4819861 : Nat := 4983230072969 + 3 ^ 40 * 4819861 * 2
def baseEnd_4819861 : Nat := 2474905380860272005371369

theorem tailTrace_4819861 : CollatzResearch.WordTrace tailWord_4819861 prefixEnd_4819861 2474905380860272005371369 := by
  unfold tailWord_4819861
  simp only [CollatzResearch.WordTrace]
  refine ⟨175794772791474238568259437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117196515194316159045506291 175794772791474238568259437)
  ·
    refine ⟨65923039796802839463097289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175794772791474238568259437 65923039796802839463097289)
    ·
      refine ⟨49442279847602129597322967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65923039796802839463097289 49442279847602129597322967)
      ·
        refine ⟨74163419771403194395984451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49442279847602129597322967 74163419771403194395984451)
        ·
          refine ⟨111245129657104791593976677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74163419771403194395984451 111245129657104791593976677)
          ·
            refine ⟨20858461810707148423870627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111245129657104791593976677 20858461810707148423870627)
            ·
              refine ⟨31287692716060722635805941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20858461810707148423870627 31287692716060722635805941)
              ·
                refine ⟨2933221192130692747106807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31287692716060722635805941 2933221192130692747106807)
                ·
                  refine ⟨4399831788196039120660211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933221192130692747106807 4399831788196039120660211)
                  ·
                    refine ⟨6599747682294058680990317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4399831788196039120660211 6599747682294058680990317)
                    ·
                      refine ⟨2474905380860272005371369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6599747682294058680990317 2474905380860272005371369)
                      ·
                        rfl

theorem cell23_4819861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_4819861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819861 prefixEnd_4819861 := by exact prefixLift 4819861
  have htrace : WordTrace (prefixWord ++ tailWord_4819861) baseStart_4819861 baseEnd_4819861 := by
    simpa [prefixWord, tailWord_4819861, baseEnd_4819861] using wordTrace_append hprefix tailTrace_4819861
  have hstable : (prefixWord ++ tailWord_4819861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819861).length < 2 ^ (prefixWord ++ tailWord_4819861).sum := by decide
  have hdescent : baseEnd_4819861 < baseStart_4819861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819884 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 7, 2, 2]
def baseStart_4819884 : Nat := 118140960795 + 4819884 * 2 ^ 59
def prefixEnd_4819884 : Nat := 4983230072969 + 3 ^ 40 * 4819884 * 2
def baseEnd_4819884 : Nat := 2474917190915325415383763

theorem tailTrace_4819884 : CollatzResearch.WordTrace tailWord_4819884 prefixEnd_4819884 2474917190915325415383763 := by
  unfold tailWord_4819884
  simp only [CollatzResearch.WordTrace]
  refine ⟨87897805835195456748173353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117197074446927275664231137 87897805835195456748173353)
  ·
    refine ⟨65923354376396592561130015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87897805835195456748173353 65923354376396592561130015)
    ·
      refine ⟨98885031564594888841695023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65923354376396592561130015 98885031564594888841695023)
      ·
        refine ⟨148327547346892333262542535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98885031564594888841695023 148327547346892333262542535)
        ·
          refine ⟨222491321020338499893813803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148327547346892333262542535 222491321020338499893813803)
          ·
            refine ⟨333736981530507749840720705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222491321020338499893813803 333736981530507749840720705)
            ·
              refine ⟨250302736147880812380540529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333736981530507749840720705 250302736147880812380540529)
              ·
                refine ⟨187727052110910609285405397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250302736147880812380540529 187727052110910609285405397)
                ·
                  refine ⟨4399852783849467405126689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 187727052110910609285405397 4399852783849467405126689)
                  ·
                    refine ⟨3299889587887100553845017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4399852783849467405126689 3299889587887100553845017)
                    ·
                      refine ⟨2474917190915325415383763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3299889587887100553845017 2474917190915325415383763)
                      ·
                        rfl

theorem cell23_4819884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 2, 2].length) (baseStart_4819884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819884 prefixEnd_4819884 := by exact prefixLift 4819884
  have htrace : WordTrace (prefixWord ++ tailWord_4819884) baseStart_4819884 baseEnd_4819884 := by
    simpa [prefixWord, tailWord_4819884, baseEnd_4819884] using wordTrace_append hprefix tailTrace_4819884
  have hstable : (prefixWord ++ tailWord_4819884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819884).length < 2 ^ (prefixWord ++ tailWord_4819884).sum := by decide
  have hdescent : baseEnd_4819884 < baseStart_4819884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819887 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 3]
def baseStart_4819887 : Nat := 118140960795 + 4819887 * 2 ^ 59
def prefixEnd_4819887 : Nat := 4983230072969 + 3 ^ 40 * 4819887 * 2
def baseEnd_4819887 : Nat := 2474918731357288903646249

theorem tailTrace_4819887 : CollatzResearch.WordTrace tailWord_4819887 prefixEnd_4819887 2474918731357288903646249 := by
  unfold tailWord_4819887
  simp only [CollatzResearch.WordTrace]
  refine ⟨175795721089380045008705915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117197147392920030005803943 175795721089380045008705915)
  ·
    refine ⟨263693581634070067513058873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175795721089380045008705915 263693581634070067513058873)
    ·
      refine ⟨197770186225552550634794155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263693581634070067513058873 197770186225552550634794155)
      ·
        refine ⟨296655279338328825952191233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197770186225552550634794155 296655279338328825952191233)
        ·
          refine ⟨222491459503746619464143425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296655279338328825952191233 222491459503746619464143425)
          ·
            refine ⟨166868594627809964598107569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222491459503746619464143425 166868594627809964598107569)
            ·
              refine ⟨125151445970857473448580677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166868594627809964598107569 125151445970857473448580677)
              ·
                refine ⟨23465896119535776271608877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125151445970857473448580677 23465896119535776271608877)
                ·
                  refine ⟨8799711044825916101853329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23465896119535776271608877 8799711044825916101853329)
                  ·
                    refine ⟨6599783283619437076389997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8799711044825916101853329 6599783283619437076389997)
                    ·
                      refine ⟨2474918731357288903646249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6599783283619437076389997 2474918731357288903646249)
                      ·
                        rfl

theorem cell23_4819887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 3].length) (baseStart_4819887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819887 prefixEnd_4819887 := by exact prefixLift 4819887
  have htrace : WordTrace (prefixWord ++ tailWord_4819887) baseStart_4819887 baseEnd_4819887 := by
    simpa [prefixWord, tailWord_4819887, baseEnd_4819887] using wordTrace_append hprefix tailTrace_4819887
  have hstable : (prefixWord ++ tailWord_4819887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819887).length < 2 ^ (prefixWord ++ tailWord_4819887).sum := by decide
  have hdescent : baseEnd_4819887 < baseStart_4819887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819897 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 6]
def baseStart_4819897 : Nat := 118140960795 + 4819897 * 2 ^ 59
def prefixEnd_4819897 : Nat := 4983230072969 + 3 ^ 40 * 4819897 * 2
def baseEnd_4819897 : Nat := 2474923866163833864521203

theorem tailTrace_4819897 : CollatzResearch.WordTrace tailWord_4819897 prefixEnd_4819897 2474923866163833864521203 := by
  unfold tailWord_4819897
  simp only [CollatzResearch.WordTrace]
  refine ⟨175796085819343816716569945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117197390546229211144379963 175796085819343816716569945)
  ·
    refine ⟨131847064364507862537427459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175796085819343816716569945 131847064364507862537427459)
    ·
      refine ⟨197770596546761793806141189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131847064364507862537427459 197770596546761793806141189)
      ·
        refine ⟨37081986852517836338651473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197770596546761793806141189 37081986852517836338651473)
        ·
          refine ⟨27811490139388377253988605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37081986852517836338651473 27811490139388377253988605)
          ·
            refine ⟨10429308802270641470245727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27811490139388377253988605 10429308802270641470245727)
            ·
              refine ⟨15643963203405962205368591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10429308802270641470245727 15643963203405962205368591)
              ·
                refine ⟨23465944805108943308052887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15643963203405962205368591 23465944805108943308052887)
                ·
                  refine ⟨35198917207663414962079331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23465944805108943308052887 35198917207663414962079331)
                  ·
                    refine ⟨52798375811495122443118997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35198917207663414962079331 52798375811495122443118997)
                    ·
                      refine ⟨2474923866163833864521203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52798375811495122443118997 2474923866163833864521203)
                      ·
                        rfl

theorem cell23_4819897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_4819897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819897 prefixEnd_4819897 := by exact prefixLift 4819897
  have htrace : WordTrace (prefixWord ++ tailWord_4819897) baseStart_4819897 baseEnd_4819897 := by
    simpa [prefixWord, tailWord_4819897, baseEnd_4819897] using wordTrace_append hprefix tailTrace_4819897
  have hstable : (prefixWord ++ tailWord_4819897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819897).length < 2 ^ (prefixWord ++ tailWord_4819897).sum := by decide
  have hdescent : baseEnd_4819897 < baseStart_4819897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819901 : List Nat := [1, 4, 1, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_4819901 : Nat := 118140960795 + 4819901 * 2 ^ 59
def prefixEnd_4819901 : Nat := 4983230072969 + 3 ^ 40 * 4819901 * 2
def baseEnd_4819901 : Nat := 2474925920086451848871185

theorem tailTrace_4819901 : CollatzResearch.WordTrace tailWord_4819901 prefixEnd_4819901 2474925920086451848871185 := by
  unfold tailWord_4819901
  simp only [CollatzResearch.WordTrace]
  refine ⟨175796231711329325399715557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117197487807552883599810371 175796231711329325399715557)
  ·
    refine ⟨32961793445874248512446667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175796231711329325399715557 32961793445874248512446667)
    ·
      refine ⟨49442690168811372768670001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32961793445874248512446667 49442690168811372768670001)
      ·
        refine ⟨37082017626608529576502501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49442690168811372768670001 37082017626608529576502501)
        ·
          refine ⟨6952878304989099295594219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37082017626608529576502501 6952878304989099295594219)
          ·
            refine ⟨10429317457483648943391329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6952878304989099295594219 10429317457483648943391329)
            ·
              refine ⟨7821988093112736707543497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10429317457483648943391329 7821988093112736707543497)
              ·
                refine ⟨5866491069834552530657623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7821988093112736707543497 5866491069834552530657623)
                ·
                  refine ⟨8799736604751828795986435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5866491069834552530657623 8799736604751828795986435)
                  ·
                    refine ⟨13199604907127743193979653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8799736604751828795986435 13199604907127743193979653)
                    ·
                      refine ⟨2474925920086451848871185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13199604907127743193979653 2474925920086451848871185)
                      ·
                        rfl

theorem cell23_4819901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_4819901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819901 prefixEnd_4819901 := by exact prefixLift 4819901
  have htrace : WordTrace (prefixWord ++ tailWord_4819901) baseStart_4819901 baseEnd_4819901 := by
    simpa [prefixWord, tailWord_4819901, baseEnd_4819901] using wordTrace_append hprefix tailTrace_4819901
  have hstable : (prefixWord ++ tailWord_4819901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819901).length < 2 ^ (prefixWord ++ tailWord_4819901).sum := by decide
  have hdescent : baseEnd_4819901 < baseStart_4819901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819904 : List Nat := [2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 3]
def baseStart_4819904 : Nat := 118140960795 + 4819904 * 2 ^ 59
def prefixEnd_4819904 : Nat := 4983230072969 + 3 ^ 40 * 4819904 * 2
def baseEnd_4819904 : Nat := 2474927460528415337133671

theorem tailTrace_4819904 : CollatzResearch.WordTrace tailWord_4819904 prefixEnd_4819904 2474927460528415337133671 := by
  unfold tailWord_4819904
  simp only [CollatzResearch.WordTrace]
  refine ⟨87898170565159228456037383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117197560753545637941383177 87898170565159228456037383)
  ·
    refine ⟨131847255847738842684056075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87898170565159228456037383 131847255847738842684056075)
    ·
      refine ⟨197770883771608264026084113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131847255847738842684056075 197770883771608264026084113)
      ·
        refine ⟨148328162828706198019563085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197770883771608264026084113 148328162828706198019563085)
        ·
          refine ⟨55623061060764824257336157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148328162828706198019563085 55623061060764824257336157)
          ·
            refine ⟨20858647897786809096501059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55623061060764824257336157 20858647897786809096501059)
            ·
              refine ⟨31287971846680213644751589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20858647897786809096501059 31287971846680213644751589)
              ·
                refine ⟨5866494721252540058390923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31287971846680213644751589 5866494721252540058390923)
                ·
                  refine ⟨8799742081878810087586385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5866494721252540058390923 8799742081878810087586385)
                  ·
                    refine ⟨6599806561409107565689789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8799742081878810087586385 6599806561409107565689789)
                    ·
                      refine ⟨2474927460528415337133671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6599806561409107565689789 2474927460528415337133671)
                      ·
                        rfl

theorem cell23_4819904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_4819904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819904 prefixEnd_4819904 := by exact prefixLift 4819904
  have htrace : WordTrace (prefixWord ++ tailWord_4819904) baseStart_4819904 baseEnd_4819904 := by
    simpa [prefixWord, tailWord_4819904, baseEnd_4819904] using wordTrace_append hprefix tailTrace_4819904
  have hstable : (prefixWord ++ tailWord_4819904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819904).length < 2 ^ (prefixWord ++ tailWord_4819904).sum := by decide
  have hdescent : baseEnd_4819904 < baseStart_4819904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819920 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 1, 9]
def baseStart_4819920 : Nat := 118140960795 + 4819920 * 2 ^ 59
def prefixEnd_4819920 : Nat := 4983230072969 + 3 ^ 40 * 4819920 * 2
def baseEnd_4819920 : Nat := 824978558739629091511199

theorem tailTrace_4819920 : CollatzResearch.WordTrace tailWord_4819920 prefixEnd_4819920 824978558739629091511199 := by
  unfold tailWord_4819920
  simp only [CollatzResearch.WordTrace]
  refine ⟨87898462349130245822328607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117197949798840327763104809 87898462349130245822328607)
  ·
    refine ⟨131847693523695368733492911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87898462349130245822328607 131847693523695368733492911)
    ·
      refine ⟨197771540285543053100239367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131847693523695368733492911 197771540285543053100239367)
      ·
        refine ⟨296657310428314579650359051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197771540285543053100239367 296657310428314579650359051)
        ·
          refine ⟨444985965642471869475538577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296657310428314579650359051 444985965642471869475538577)
          ·
            refine ⟨333739474231853902106653933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444985965642471869475538577 333739474231853902106653933)
            ·
              refine ⟨125152302836945213289995225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 333739474231853902106653933 125152302836945213289995225)
              ·
                refine ⟨93864227127708909967496419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125152302836945213289995225 93864227127708909967496419)
                ·
                  refine ⟨140796340691563364951244629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93864227127708909967496419 140796340691563364951244629)
                  ·
                    refine ⟨824978558739629091511199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 140796340691563364951244629 824978558739629091511199)
                    ·
                      rfl

theorem cell23_4819920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_4819920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819920 prefixEnd_4819920 := by exact prefixLift 4819920
  have htrace : WordTrace (prefixWord ++ tailWord_4819920) baseStart_4819920 baseEnd_4819920 := by
    simpa [prefixWord, tailWord_4819920, baseEnd_4819920] using wordTrace_append hprefix tailTrace_4819920
  have hstable : (prefixWord ++ tailWord_4819920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819920).length < 2 ^ (prefixWord ++ tailWord_4819920).sum := by decide
  have hdescent : baseEnd_4819920 < baseStart_4819920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819935 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 3, 2, 2]
def baseStart_4819935 : Nat := 118140960795 + 4819935 * 2 ^ 59
def prefixEnd_4819935 : Nat := 4983230072969 + 3 ^ 40 * 4819935 * 2
def baseEnd_4819935 : Nat := 2474943378428704715846029

theorem tailTrace_4819935 : CollatzResearch.WordTrace tailWord_4819935 prefixEnd_4819935 2474943378428704715846029 := by
  unfold tailWord_4819935
  simp only [CollatzResearch.WordTrace]
  refine ⟨175797471793206149206453259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117198314528804099470968839 175797471793206149206453259)
  ·
    refine ⟨263696207689809223809679889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175797471793206149206453259 263696207689809223809679889)
    ·
      refine ⟨197772155767356917857259917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263696207689809223809679889 197772155767356917857259917)
      ·
        refine ⟨74164558412758844196472469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197772155767356917857259917 74164558412758844196472469)
        ·
          refine ⟨3476463675598070821709647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74164558412758844196472469 3476463675598070821709647)
          ·
            refine ⟨5214695513397106232564471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3476463675598070821709647 5214695513397106232564471)
            ·
              refine ⟨7822043270095659348846707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5214695513397106232564471 7822043270095659348846707)
              ·
                refine ⟨11733064905143489023270061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7822043270095659348846707 11733064905143489023270061)
                ·
                  refine ⟨4399899339428808383726273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11733064905143489023270061 4399899339428808383726273)
                  ·
                    refine ⟨3299924504571606287794705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4399899339428808383726273 3299924504571606287794705)
                    ·
                      refine ⟨2474943378428704715846029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3299924504571606287794705 2474943378428704715846029)
                      ·
                        rfl

theorem cell23_4819935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_4819935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819935 prefixEnd_4819935 := by exact prefixLift 4819935
  have htrace : WordTrace (prefixWord ++ tailWord_4819935) baseStart_4819935 baseEnd_4819935 := by
    simpa [prefixWord, tailWord_4819935, baseEnd_4819935] using wordTrace_append hprefix tailTrace_4819935
  have hstable : (prefixWord ++ tailWord_4819935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819935).length < 2 ^ (prefixWord ++ tailWord_4819935).sum := by decide
  have hdescent : baseEnd_4819935 < baseStart_4819935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819951 : List Nat := [1, 1, 2, 1, 4, 4, 1, 3, 2, 1, 3]
def baseStart_4819951 : Nat := 118140960795 + 4819951 * 2 ^ 59
def prefixEnd_4819951 : Nat := 4983230072969 + 3 ^ 40 * 4819951 * 2
def baseEnd_4819951 : Nat := 2474951594119176653245955

theorem tailTrace_4819951 : CollatzResearch.WordTrace tailWord_4819951 prefixEnd_4819951 2474951594119176653245955 := by
  unfold tailWord_4819951
  simp only [CollatzResearch.WordTrace]
  refine ⟨175798055361148183939035707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117198703574098789292690471 175798055361148183939035707)
  ·
    refine ⟨263697083041722275908553561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175798055361148183939035707 263697083041722275908553561)
    ·
      refine ⟨197772812281291706931415171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263697083041722275908553561 197772812281291706931415171)
      ·
        refine ⟨296659218421937560397122757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197772812281291706931415171 296659218421937560397122757)
        ·
          refine ⟨55623603454113292574460517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296659218421937560397122757 55623603454113292574460517)
          ·
            refine ⟨10429425647646242357711347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55623603454113292574460517 10429425647646242357711347)
            ·
              refine ⟨15644138471469363536567021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10429425647646242357711347 15644138471469363536567021)
              ·
                refine ⟨5866551926801011326212633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15644138471469363536567021 5866551926801011326212633)
                ·
                  refine ⟨4399913945100758494659475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5866551926801011326212633 4399913945100758494659475)
                  ·
                    refine ⟨6599870917651137741989213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4399913945100758494659475 6599870917651137741989213)
                    ·
                      refine ⟨2474951594119176653245955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6599870917651137741989213 2474951594119176653245955)
                      ·
                        rfl

theorem cell23_4819951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 1, 3].length) (baseStart_4819951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819951 prefixEnd_4819951 := by exact prefixLift 4819951
  have htrace : WordTrace (prefixWord ++ tailWord_4819951) baseStart_4819951 baseEnd_4819951 := by
    simpa [prefixWord, tailWord_4819951, baseEnd_4819951] using wordTrace_append hprefix tailTrace_4819951
  have hstable : (prefixWord ++ tailWord_4819951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819951).length < 2 ^ (prefixWord ++ tailWord_4819951).sum := by decide
  have hdescent : baseEnd_4819951 < baseStart_4819951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819977 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 4, 4, 3]
def baseStart_4819977 : Nat := 118140960795 + 4819977 * 2 ^ 59
def prefixEnd_4819977 : Nat := 4983230072969 + 3 ^ 40 * 4819977 * 2
def baseEnd_4819977 : Nat := 2474964944616193551520835

theorem tailTrace_4819977 : CollatzResearch.WordTrace tailWord_4819977 prefixEnd_4819977 2474964944616193551520835 := by
  unfold tailWord_4819977
  simp only [CollatzResearch.WordTrace]
  refine ⟨175799003659053990379482185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117199335772702660252988123 175799003659053990379482185)
  ·
    refine ⟨131849252744290492784611639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175799003659053990379482185 131849252744290492784611639)
    ·
      refine ⟨197773879116435739176917459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131849252744290492784611639 197773879116435739176917459)
      ·
        refine ⟨296660818674653608765376189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197773879116435739176917459 296660818674653608765376189)
        ·
          refine ⟨111247807002995103287016071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296660818674653608765376189 111247807002995103287016071)
          ·
            refine ⟨166871710504492654930524107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111247807002995103287016071 166871710504492654930524107)
            ·
              refine ⟨250307565756738982395786161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166871710504492654930524107 250307565756738982395786161)
              ·
                refine ⟨187730674317554236796839621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250307565756738982395786161 187730674317554236796839621)
                ·
                  refine ⟨35199501434541419399407429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187730674317554236796839621 35199501434541419399407429)
                  ·
                    refine ⟨6599906518976516137388893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35199501434541419399407429 6599906518976516137388893)
                    ·
                      refine ⟨2474964944616193551520835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6599906518976516137388893 2474964944616193551520835)
                      ·
                        rfl

theorem cell23_4819977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 4, 3].length) (baseStart_4819977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819977 prefixEnd_4819977 := by exact prefixLift 4819977
  have htrace : WordTrace (prefixWord ++ tailWord_4819977) baseStart_4819977 baseEnd_4819977 := by
    simpa [prefixWord, tailWord_4819977, baseEnd_4819977] using wordTrace_append hprefix tailTrace_4819977
  have hstable : (prefixWord ++ tailWord_4819977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819977).length < 2 ^ (prefixWord ++ tailWord_4819977).sum := by decide
  have hdescent : baseEnd_4819977 < baseStart_4819977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4819987 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 4]
def baseStart_4819987 : Nat := 118140960795 + 4819987 * 2 ^ 59
def prefixEnd_4819987 : Nat := 4983230072969 + 3 ^ 40 * 4819987 * 2
def baseEnd_4819987 : Nat := 2474970079422738512395789

theorem tailTrace_4819987 : CollatzResearch.WordTrace tailWord_4819987 prefixEnd_4819987 2474970079422738512395789 := by
  unfold tailWord_4819987
  simp only [CollatzResearch.WordTrace]
  refine ⟨175799368389017762087346215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117199578926011841391564143 175799368389017762087346215)
  ·
    refine ⟨263699052583526643131019323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175799368389017762087346215 263699052583526643131019323)
    ·
      refine ⟨395548578875289964696528985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263699052583526643131019323 395548578875289964696528985)
      ·
        refine ⟨296661434156467473522396739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395548578875289964696528985 296661434156467473522396739)
        ·
          refine ⟨444992151234701210283595109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296661434156467473522396739 444992151234701210283595109)
          ·
            refine ⟨83436028356506476928174083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 444992151234701210283595109 83436028356506476928174083)
            ·
              refine ⟨125154042534759715392261125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83436028356506476928174083 125154042534759715392261125)
              ·
                refine ⟨23466382975267446636048961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125154042534759715392261125 23466382975267446636048961)
                ·
                  refine ⟨17599787231450584977036721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23466382975267446636048961 17599787231450584977036721)
                  ·
                    refine ⟨13199840423587938732777541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17599787231450584977036721 13199840423587938732777541)
                    ·
                      refine ⟨2474970079422738512395789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13199840423587938732777541 2474970079422738512395789)
                      ·
                        rfl

theorem cell23_4819987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_4819987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4819987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4819987 prefixEnd_4819987 := by exact prefixLift 4819987
  have htrace : WordTrace (prefixWord ++ tailWord_4819987) baseStart_4819987 baseEnd_4819987 := by
    simpa [prefixWord, tailWord_4819987, baseEnd_4819987] using wordTrace_append hprefix tailTrace_4819987
  have hstable : (prefixWord ++ tailWord_4819987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4819987).length < 2 ^ (prefixWord ++ tailWord_4819987).sum := by decide
  have hdescent : baseEnd_4819987 < baseStart_4819987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4819987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820004 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_4820004 : Nat := 118140960795 + 4820004 * 2 ^ 59
def prefixEnd_4820004 : Nat := 4983230072969 + 3 ^ 40 * 4820004 * 2
def baseEnd_4820004 : Nat := 2474978808593864945883211

theorem tailTrace_4820004 : CollatzResearch.WordTrace tailWord_4820004 prefixEnd_4820004 2474978808593864945883211 := by
  unfold tailWord_4820004
  simp only [CollatzResearch.WordTrace]
  refine ⟨87899994214978086995357533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117199992286637449327143377 87899994214978086995357533)
  ·
    refine ⟨32962497830616782623259075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87899994214978086995357533 32962497830616782623259075)
    ·
      refine ⟨49443746745925173934888613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32962497830616782623259075 49443746745925173934888613)
      ·
        refine ⟨9270702514860970112791615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49443746745925173934888613 9270702514860970112791615)
        ·
          refine ⟨13906053772291455169187423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9270702514860970112791615 13906053772291455169187423)
          ·
            refine ⟨20859080658437182753781135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13906053772291455169187423 20859080658437182753781135)
            ·
              refine ⟨31288620987655774130671703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20859080658437182753781135 31288620987655774130671703)
              ·
                refine ⟨46932931481483661196007555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31288620987655774130671703 46932931481483661196007555)
                ·
                  refine ⟨70399397222225491794011333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46932931481483661196007555 70399397222225491794011333)
                  ·
                    refine ⟨13199886979167279711377125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70399397222225491794011333 13199886979167279711377125)
                    ·
                      refine ⟨2474978808593864945883211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13199886979167279711377125 2474978808593864945883211)
                      ·
                        rfl

theorem cell23_4820004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_4820004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820004 prefixEnd_4820004 := by exact prefixLift 4820004
  have htrace : WordTrace (prefixWord ++ tailWord_4820004) baseStart_4820004 baseEnd_4820004 := by
    simpa [prefixWord, tailWord_4820004, baseEnd_4820004] using wordTrace_append hprefix tailTrace_4820004
  have hstable : (prefixWord ++ tailWord_4820004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820004).length < 2 ^ (prefixWord ++ tailWord_4820004).sum := by decide
  have hdescent : baseEnd_4820004 < baseStart_4820004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820014 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 7]
def baseStart_4820014 : Nat := 118140960795 + 4820014 * 2 ^ 59
def prefixEnd_4820014 : Nat := 4983230072969 + 3 ^ 40 * 4820014 * 2
def baseEnd_4820014 : Nat := 274998215933378878528685

theorem tailTrace_4820014 : CollatzResearch.WordTrace tailWord_4820014 prefixEnd_4820014 274998215933378878528685 := by
  unfold tailWord_4820014
  simp only [CollatzResearch.WordTrace]
  refine ⟨21975044144989993212322387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117200235439946630465719397 21975044144989993212322387)
  ·
    refine ⟨32962566217484989818483581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21975044144989993212322387 32962566217484989818483581)
    ·
      refine ⟨12360962331556871181931343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32962566217484989818483581 12360962331556871181931343)
      ·
        refine ⟨18541443497335306772897015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12360962331556871181931343 18541443497335306772897015)
        ·
          refine ⟨27812165246002960159345523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18541443497335306772897015 27812165246002960159345523)
          ·
            refine ⟨41718247869004440239018285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27812165246002960159345523 41718247869004440239018285)
            ·
              refine ⟨15644342950876665089631857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41718247869004440239018285 15644342950876665089631857)
              ·
                refine ⟨11733257213157498817223893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15644342950876665089631857 11733257213157498817223893)
                ·
                  refine ⟨274998215933378878528685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11733257213157498817223893 274998215933378878528685)
                  ·
                    rfl

theorem cell23_4820014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_4820014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820014 prefixEnd_4820014 := by exact prefixLift 4820014
  have htrace : WordTrace (prefixWord ++ tailWord_4820014) baseStart_4820014 baseEnd_4820014 := by
    simpa [prefixWord, tailWord_4820014, baseEnd_4820014] using wordTrace_append hprefix tailTrace_4820014
  have hstable : (prefixWord ++ tailWord_4820014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820014).length < 2 ^ (prefixWord ++ tailWord_4820014).sum := by decide
  have hdescent : baseEnd_4820014 < baseStart_4820014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820037 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_4820037 : Nat := 118140960795 + 4820037 * 2 ^ 59
def prefixEnd_4820037 : Nat := 4983230072969 + 3 ^ 40 * 4820037 * 2
def baseEnd_4820037 : Nat := 2474995753455463316770559

theorem tailTrace_4820037 : CollatzResearch.WordTrace tailWord_4820037 prefixEnd_4820037 2474995753455463316770559 := by
  unfold tailWord_4820037
  simp only [CollatzResearch.WordTrace]
  refine ⟨175801192038836620626666365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117200794692557747084444243 175801192038836620626666365)
  ·
    refine ⟨65925447014563732734999887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175801192038836620626666365 65925447014563732734999887)
    ·
      refine ⟨98888170521845599102499831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65925447014563732734999887 98888170521845599102499831)
      ·
        refine ⟨148332255782768398653749747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98888170521845599102499831 148332255782768398653749747)
        ·
          refine ⟨222498383674152597980624621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148332255782768398653749747 222498383674152597980624621)
          ·
            refine ⟨83436893877807224242734233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222498383674152597980624621 83436893877807224242734233)
            ·
              refine ⟨62577670408355418182050675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83436893877807224242734233 62577670408355418182050675)
              ·
                refine ⟨93866505612533127273076013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62577670408355418182050675 93866505612533127273076013)
                ·
                  refine ⟨35199939604699922727403505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93866505612533127273076013 35199939604699922727403505)
                  ·
                    refine ⟨26399954703524942045552629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35199939604699922727403505 26399954703524942045552629)
                    ·
                      refine ⟨2474995753455463316770559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26399954703524942045552629 2474995753455463316770559)
                      ·
                        rfl

theorem cell23_4820037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_4820037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820037 prefixEnd_4820037 := by exact prefixLift 4820037
  have htrace : WordTrace (prefixWord ++ tailWord_4820037) baseStart_4820037 baseEnd_4820037 := by
    simpa [prefixWord, tailWord_4820037, baseEnd_4820037] using wordTrace_append hprefix tailTrace_4820037
  have hstable : (prefixWord ++ tailWord_4820037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820037).length < 2 ^ (prefixWord ++ tailWord_4820037).sum := by decide
  have hdescent : baseEnd_4820037 < baseStart_4820037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820047 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 4]
def baseStart_4820047 : Nat := 118140960795 + 4820047 * 2 ^ 59
def prefixEnd_4820047 : Nat := 4983230072969 + 3 ^ 40 * 4820047 * 2
def baseEnd_4820047 : Nat := 2475000888262008277645513

theorem tailTrace_4820047 : CollatzResearch.WordTrace tailWord_4820047 prefixEnd_4820047 2475000888262008277645513 := by
  unfold tailWord_4820047
  simp only [CollatzResearch.WordTrace]
  refine ⟨175801556768800392334530395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117201037845866928223020263 175801556768800392334530395)
  ·
    refine ⟨263702335153200588501795593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175801556768800392334530395 263702335153200588501795593)
    ·
      refine ⟨197776751364900441376346695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263702335153200588501795593 197776751364900441376346695)
      ·
        refine ⟨296665127047350662064520043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197776751364900441376346695 296665127047350662064520043)
        ·
          refine ⟨444997690571025993096780065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296665127047350662064520043 444997690571025993096780065)
          ·
            refine ⟨333748267928269494822585049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444997690571025993096780065 333748267928269494822585049)
            ·
              refine ⟨250311200946202121116938787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333748267928269494822585049 250311200946202121116938787)
              ·
                refine ⟨375466801419303181675408181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250311200946202121116938787 375466801419303181675408181)
                ·
                  refine ⟨35200012633059673282069517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 375466801419303181675408181 35200012633059673282069517)
                  ·
                    refine ⟨13200004737397377480776069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35200012633059673282069517 13200004737397377480776069)
                    ·
                      refine ⟨2475000888262008277645513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13200004737397377480776069 2475000888262008277645513)
                      ·
                        rfl

theorem cell23_4820047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_4820047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820047 prefixEnd_4820047 := by exact prefixLift 4820047
  have htrace : WordTrace (prefixWord ++ tailWord_4820047) baseStart_4820047 baseEnd_4820047 := by
    simpa [prefixWord, tailWord_4820047, baseEnd_4820047] using wordTrace_append hprefix tailTrace_4820047
  have hstable : (prefixWord ++ tailWord_4820047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820047).length < 2 ^ (prefixWord ++ tailWord_4820047).sum := by decide
  have hdescent : baseEnd_4820047 < baseStart_4820047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820087 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 10]
def baseStart_4820087 : Nat := 118140960795 + 4820087 * 2 ^ 59
def prefixEnd_4820087 : Nat := 4983230072969 + 3 ^ 40 * 4820087 * 2
def baseEnd_4820087 : Nat := 275002380832020902349481

theorem tailTrace_4820087 : CollatzResearch.WordTrace tailWord_4820087 prefixEnd_4820087 275002380832020902349481 := by
  unfold tailWord_4820087
  simp only [CollatzResearch.WordTrace]
  refine ⟨175803015688655479165986515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117202010459103652777324343 175803015688655479165986515)
  ·
    refine ⟨263704523532983218748979773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175803015688655479165986515 263704523532983218748979773)
    ·
      refine ⟨98889196324868707030867415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263704523532983218748979773 98889196324868707030867415)
      ·
        refine ⟨148333794487303060546301123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98889196324868707030867415 148333794487303060546301123)
        ·
          refine ⟨222500691730954590819451685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148333794487303060546301123 222500691730954590819451685)
          ·
            refine ⟨41718879699553985778647191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222500691730954590819451685 41718879699553985778647191)
            ·
              refine ⟨62578319549330978667970787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41718879699553985778647191 62578319549330978667970787)
              ·
                refine ⟨93867479323996468001956181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62578319549330978667970787 93867479323996468001956181)
                ·
                  refine ⟨275002380832020902349481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 93867479323996468001956181 275002380832020902349481)
                  ·
                    rfl

theorem cell23_4820087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 10].length) (baseStart_4820087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820087 prefixEnd_4820087 := by exact prefixLift 4820087
  have htrace : WordTrace (prefixWord ++ tailWord_4820087) baseStart_4820087 baseEnd_4820087 := by
    simpa [prefixWord, tailWord_4820087, baseEnd_4820087] using wordTrace_append hprefix tailTrace_4820087
  have hstable : (prefixWord ++ tailWord_4820087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820087).length < 2 ^ (prefixWord ++ tailWord_4820087).sum := by decide
  have hdescent : baseEnd_4820087 < baseStart_4820087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820107 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 8]
def baseStart_4820107 : Nat := 118140960795 + 4820107 * 2 ^ 59
def prefixEnd_4820107 : Nat := 4983230072969 + 3 ^ 40 * 4820107 * 2
def baseEnd_4820107 : Nat := 2475031697101278042895237

theorem tailTrace_4820107 : CollatzResearch.WordTrace tailWord_4820107 prefixEnd_4820107 2475031697101278042895237 := by
  unfold tailWord_4820107
  simp only [CollatzResearch.WordTrace]
  refine ⟨175803745148583022581714575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117202496765722015054476383 175803745148583022581714575)
  ·
    refine ⟨263705617722874533872571863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175803745148583022581714575 263705617722874533872571863)
    ·
      refine ⟨395558426584311800808857795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263705617722874533872571863 395558426584311800808857795)
      ·
        refine ⟨593337639876467701213286693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395558426584311800808857795 593337639876467701213286693)
        ·
          refine ⟨111250807476837693977491255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 593337639876467701213286693 111250807476837693977491255)
          ·
            refine ⟨166876211215256540966236883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111250807476837693977491255 166876211215256540966236883)
            ·
              refine ⟨250314316822884811449355325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166876211215256540966236883 250314316822884811449355325)
              ·
                refine ⟨93867868808581804293508247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250314316822884811449355325 93867868808581804293508247)
                ·
                  refine ⟨140801803212872706440262371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93867868808581804293508247 140801803212872706440262371)
                  ·
                    refine ⟨211202704819309059660393557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140801803212872706440262371 211202704819309059660393557)
                    ·
                      refine ⟨2475031697101278042895237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 211202704819309059660393557 2475031697101278042895237)
                      ·
                        rfl

theorem cell23_4820107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_4820107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820107 prefixEnd_4820107 := by exact prefixLift 4820107
  have htrace : WordTrace (prefixWord ++ tailWord_4820107) baseStart_4820107 baseEnd_4820107 := by
    simpa [prefixWord, tailWord_4820107, baseEnd_4820107] using wordTrace_append hprefix tailTrace_4820107
  have hstable : (prefixWord ++ tailWord_4820107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820107).length < 2 ^ (prefixWord ++ tailWord_4820107).sum := by decide
  have hdescent : baseEnd_4820107 < baseStart_4820107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820131 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 3, 1, 3]
def baseStart_4820131 : Nat := 118140960795 + 4820131 * 2 ^ 59
def prefixEnd_4820131 : Nat := 4983230072969 + 3 ^ 40 * 4820131 * 2
def baseEnd_4820131 : Nat := 2475044020636985948995127

theorem tailTrace_4820131 : CollatzResearch.WordTrace tailWord_4820131 prefixEnd_4820131 2475044020636985948995127 := by
  unfold tailWord_4820131
  simp only [CollatzResearch.WordTrace]
  refine ⟨175804620500496074680588247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117203080333664049787058831 175804620500496074680588247)
  ·
    refine ⟨263706930750744112020882371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175804620500496074680588247 263706930750744112020882371)
    ·
      refine ⟨395560396126116168031323557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263706930750744112020882371 395560396126116168031323557)
      ·
        refine ⟨74167574273646781505873167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 395560396126116168031323557 74167574273646781505873167)
        ·
          refine ⟨111251361410470172258809751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74167574273646781505873167 111251361410470172258809751)
          ·
            refine ⟨166877042115705258388214627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111251361410470172258809751 166877042115705258388214627)
            ·
              refine ⟨250315563173557887582321941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166877042115705258388214627 250315563173557887582321941)
              ·
                refine ⟨11733542023760525980421341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 250315563173557887582321941 11733542023760525980421341)
                ·
                  refine ⟨4400078258910197242658003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11733542023760525980421341 4400078258910197242658003)
                  ·
                    refine ⟨6600117388365295863987005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4400078258910197242658003 6600117388365295863987005)
                    ·
                      refine ⟨2475044020636985948995127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6600117388365295863987005 2475044020636985948995127)
                      ·
                        rfl

theorem cell23_4820131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_4820131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820131 prefixEnd_4820131 := by exact prefixLift 4820131
  have htrace : WordTrace (prefixWord ++ tailWord_4820131) baseStart_4820131 baseEnd_4820131 := by
    simpa [prefixWord, tailWord_4820131, baseEnd_4820131] using wordTrace_append hprefix tailTrace_4820131
  have hstable : (prefixWord ++ tailWord_4820131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820131).length < 2 ^ (prefixWord ++ tailWord_4820131).sum := by decide
  have hdescent : baseEnd_4820131 < baseStart_4820131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820181 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 1, 6]
def baseStart_4820181 : Nat := 118140960795 + 4820181 * 2 ^ 59
def prefixEnd_4820181 : Nat := 4983230072969 + 3 ^ 40 * 4820181 * 2
def baseEnd_4820181 : Nat := 825023231556570251123299

theorem tailTrace_4820181 : CollatzResearch.WordTrace tailWord_4820181 prefixEnd_4820181 825023231556570251123299 := by
  unfold tailWord_4820181
  simp only [CollatzResearch.WordTrace]
  refine ⟨175806444150314933219908397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117204296100209955479938931 175806444150314933219908397)
  ·
    refine ⟨65927416556368099957465649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175806444150314933219908397 65927416556368099957465649)
    ·
      refine ⟨49445562417276074968099237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65927416556368099957465649 49445562417276074968099237)
      ·
        refine ⟨9271042953239264056518607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49445562417276074968099237 9271042953239264056518607)
        ·
          refine ⟨13906564429858896084777911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9271042953239264056518607 13906564429858896084777911)
          ·
            refine ⟨20859846644788344127166867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13906564429858896084777911 20859846644788344127166867)
            ·
              refine ⟨31289769967182516190750301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20859846644788344127166867 31289769967182516190750301)
              ·
                refine ⟨11733663737693443571531363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31289769967182516190750301 11733663737693443571531363)
                ·
                  refine ⟨17600495606540165357297045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11733663737693443571531363 17600495606540165357297045)
                  ·
                    refine ⟨825023231556570251123299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17600495606540165357297045 825023231556570251123299)
                    ·
                      rfl

theorem cell23_4820181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_4820181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820181 prefixEnd_4820181 := by exact prefixLift 4820181
  have htrace : WordTrace (prefixWord ++ tailWord_4820181) baseStart_4820181 baseEnd_4820181 := by
    simpa [prefixWord, tailWord_4820181, baseEnd_4820181] using wordTrace_append hprefix tailTrace_4820181
  have hstable : (prefixWord ++ tailWord_4820181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820181).length < 2 ^ (prefixWord ++ tailWord_4820181).sum := by decide
  have hdescent : baseEnd_4820181 < baseStart_4820181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820182 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_4820182 : Nat := 118140960795 + 4820182 * 2 ^ 59
def prefixEnd_4820182 : Nat := 4983230072969 + 3 ^ 40 * 4820182 * 2
def baseEnd_4820182 : Nat := 2475070208150365249457393

theorem tailTrace_4820182 : CollatzResearch.WordTrace tailWord_4820182 prefixEnd_4820182 2475070208150365249457393 := by
  unfold tailWord_4820182
  simp only [CollatzResearch.WordTrace]
  refine ⟨10987905038956956899418425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117204320415540873593796533 10987905038956956899418425)
  ·
    refine ⟨8240928779217717674563819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10987905038956956899418425 8240928779217717674563819)
    ·
      refine ⟨12361393168826576511845729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8240928779217717674563819 12361393168826576511845729)
      ·
        refine ⟨9271044876619932383884297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12361393168826576511845729 9271044876619932383884297)
        ·
          refine ⟨6953283657464949287913223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9271044876619932383884297 6953283657464949287913223)
          ·
            refine ⟨10429925486197423931869835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6953283657464949287913223 10429925486197423931869835)
            ·
              refine ⟨15644888229296135897804753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10429925486197423931869835 15644888229296135897804753)
              ·
                refine ⟨11733666171972101923353565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15644888229296135897804753 11733666171972101923353565)
                ·
                  refine ⟨4400124814489538221257587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11733666171972101923353565 4400124814489538221257587)
                  ·
                    refine ⟨6600187221734307331886381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4400124814489538221257587 6600187221734307331886381)
                    ·
                      refine ⟨2475070208150365249457393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6600187221734307331886381 2475070208150365249457393)
                      ·
                        rfl

theorem cell23_4820182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_4820182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820182 prefixEnd_4820182 := by exact prefixLift 4820182
  have htrace : WordTrace (prefixWord ++ tailWord_4820182) baseStart_4820182 baseEnd_4820182 := by
    simpa [prefixWord, tailWord_4820182, baseEnd_4820182] using wordTrace_append hprefix tailTrace_4820182
  have hstable : (prefixWord ++ tailWord_4820182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820182).length < 2 ^ (prefixWord ++ tailWord_4820182).sum := by decide
  have hdescent : baseEnd_4820182 < baseStart_4820182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820191 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 3]
def baseStart_4820191 : Nat := 118140960795 + 4820191 * 2 ^ 59
def prefixEnd_4820191 : Nat := 4983230072969 + 3 ^ 40 * 4820191 * 2
def baseEnd_4820191 : Nat := 2475074829476255714244851

theorem tailTrace_4820191 : CollatzResearch.WordTrace tailWord_4820191 prefixEnd_4820191 2475074829476255714244851 := by
  unfold tailWord_4820191
  simp only [CollatzResearch.WordTrace]
  refine ⟨175806808880278704927772427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117204539253519136618514951 175806808880278704927772427)
  ·
    refine ⟨263710213320418057391658641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175806808880278704927772427 263710213320418057391658641)
    ·
      refine ⟨197782659990313543043743981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263710213320418057391658641 197782659990313543043743981)
      ·
        refine ⟨74168497496367578641403993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197782659990313543043743981 74168497496367578641403993)
        ·
          refine ⟨55626373122275683981052995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74168497496367578641403993 55626373122275683981052995)
          ·
            refine ⟨83439559683413525971579493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55626373122275683981052995 83439559683413525971579493)
            ·
              refine ⟨15644917440640036119671155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83439559683413525971579493 15644917440640036119671155)
              ·
                refine ⟨23467376160960054179506733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15644917440640036119671155 23467376160960054179506733)
                ·
                  refine ⟨8800266060360020317315025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23467376160960054179506733 8800266060360020317315025)
                  ·
                    refine ⟨6600199545270015237986269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8800266060360020317315025 6600199545270015237986269)
                    ·
                      refine ⟨2475074829476255714244851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6600199545270015237986269 2475074829476255714244851)
                      ·
                        rfl

theorem cell23_4820191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_4820191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820191 prefixEnd_4820191 := by exact prefixLift 4820191
  have htrace : WordTrace (prefixWord ++ tailWord_4820191) baseStart_4820191 baseEnd_4820191 := by
    simpa [prefixWord, tailWord_4820191, baseEnd_4820191] using wordTrace_append hprefix tailTrace_4820191
  have hstable : (prefixWord ++ tailWord_4820191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820191).length < 2 ^ (prefixWord ++ tailWord_4820191).sum := by decide
  have hdescent : baseEnd_4820191 < baseStart_4820191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820205 : List Nat := [1, 5, 1, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_4820205 : Nat := 118140960795 + 4820205 * 2 ^ 59
def prefixEnd_4820205 : Nat := 4983230072969 + 3 ^ 40 * 4820205 * 2
def baseEnd_4820205 : Nat := 2475082018205418659469787

theorem tailTrace_4820205 : CollatzResearch.WordTrace tailWord_4820205 prefixEnd_4820205 2475082018205418659469787 := by
  unfold tailWord_4820205
  simp only [CollatzResearch.WordTrace]
  refine ⟨175807319502227985318782069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117204879668151990212521379 175807319502227985318782069)
  ·
    refine ⟨16481936203333873623635819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175807319502227985318782069 16481936203333873623635819)
    ·
      refine ⟨24722904305000810435453729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16481936203333873623635819 24722904305000810435453729)
      ·
        refine ⟨18542178228750607826590297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24722904305000810435453729 18542178228750607826590297)
        ·
          refine ⟨13906633671562955869942723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18542178228750607826590297 13906633671562955869942723)
          ·
            refine ⟨20859950507344433804914085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13906633671562955869942723 20859950507344433804914085)
            ·
              refine ⟨3911240720127081338421391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20859950507344433804914085 3911240720127081338421391)
              ·
                refine ⟨5866861080190622007632087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3911240720127081338421391 5866861080190622007632087)
                ·
                  refine ⟨8800291620285933011448131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5866861080190622007632087 8800291620285933011448131)
                  ·
                    refine ⟨13200437430428899517172197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8800291620285933011448131 13200437430428899517172197)
                    ·
                      refine ⟨2475082018205418659469787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13200437430428899517172197 2475082018205418659469787)
                      ·
                        rfl

theorem cell23_4820205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_4820205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820205 prefixEnd_4820205 := by exact prefixLift 4820205
  have htrace : WordTrace (prefixWord ++ tailWord_4820205) baseStart_4820205 baseEnd_4820205 := by
    simpa [prefixWord, tailWord_4820205, baseEnd_4820205] using wordTrace_append hprefix tailTrace_4820205
  have hstable : (prefixWord ++ tailWord_4820205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820205).length < 2 ^ (prefixWord ++ tailWord_4820205).sum := by decide
  have hdescent : baseEnd_4820205 < baseStart_4820205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820222 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_4820222 : Nat := 118140960795 + 4820222 * 2 ^ 59
def prefixEnd_4820222 : Nat := 4983230072969 + 3 ^ 40 * 4820222 * 2
def baseEnd_4820222 : Nat := 2475090747376545092957209

theorem tailTrace_4820222 : CollatzResearch.WordTrace tailWord_4820222 prefixEnd_4820222 2475090747376545092957209 := by
  unfold tailWord_4820222
  simp only [CollatzResearch.WordTrace]
  refine ⟨21975992442895799652768865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117205293028777598148100613 21975992442895799652768865)
  ·
    refine ⟨16481994332171849739576649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21975992442895799652768865 16481994332171849739576649)
    ·
      refine ⟨12361495749128887304682487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16481994332171849739576649 12361495749128887304682487)
      ·
        refine ⟨18542243623693330957023731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12361495749128887304682487 18542243623693330957023731)
        ·
          refine ⟨27813365435539996435535597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18542243623693330957023731 27813365435539996435535597)
          ·
            refine ⟨10430012038327498663325849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27813365435539996435535597 10430012038327498663325849)
            ·
              refine ⟨7822509028745623997494387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10430012038327498663325849 7822509028745623997494387)
              ·
                refine ⟨11733763543118435996241581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7822509028745623997494387 11733763543118435996241581)
                ·
                  refine ⟨4400161328669413498590593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11733763543118435996241581 4400161328669413498590593)
                  ·
                    refine ⟨3300120996502060123942945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4400161328669413498590593 3300120996502060123942945)
                    ·
                      refine ⟨2475090747376545092957209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3300120996502060123942945 2475090747376545092957209)
                      ·
                        rfl

theorem cell23_4820222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_4820222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820222 prefixEnd_4820222 := by exact prefixLift 4820222
  have htrace : WordTrace (prefixWord ++ tailWord_4820222) baseStart_4820222 baseEnd_4820222 := by
    simpa [prefixWord, tailWord_4820222, baseEnd_4820222] using wordTrace_append hprefix tailTrace_4820222
  have hstable : (prefixWord ++ tailWord_4820222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820222).length < 2 ^ (prefixWord ++ tailWord_4820222).sum := by decide
  have hdescent : baseEnd_4820222 < baseStart_4820222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820238 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_4820238 : Nat := 118140960795 + 4820238 * 2 ^ 59
def prefixEnd_4820238 : Nat := 4983230072969 + 3 ^ 40 * 4820238 * 2
def baseEnd_4820238 : Nat := 2475098963067017030357135

theorem tailTrace_4820238 : CollatzResearch.WordTrace tailWord_4820238 prefixEnd_4820238 2475098963067017030357135 := by
  unfold tailWord_4820238
  simp only [CollatzResearch.WordTrace]
  refine ⟨21976065388888553994341671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117205682074072287969822245 21976065388888553994341671)
  ·
    refine ⟨32964098083332830991512507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21976065388888553994341671 32964098083332830991512507)
    ·
      refine ⟨49446147124999246487268761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32964098083332830991512507 49446147124999246487268761)
      ·
        refine ⟨37084610343749434865451571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49446147124999246487268761 37084610343749434865451571)
        ·
          refine ⟨55626915515624152298177357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37084610343749434865451571 55626915515624152298177357)
          ·
            refine ⟨20860093318359057111816509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55626915515624152298177357 20860093318359057111816509)
            ·
              refine ⟨7822534994384646416931191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20860093318359057111816509 7822534994384646416931191)
              ·
                refine ⟨11733802491576969625396787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7822534994384646416931191 11733802491576969625396787)
                ·
                  refine ⟨17600703737365454438095181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11733802491576969625396787 17600703737365454438095181)
                  ·
                    refine ⟨6600263901512045414285693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17600703737365454438095181 6600263901512045414285693)
                    ·
                      refine ⟨2475098963067017030357135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6600263901512045414285693 2475098963067017030357135)
                      ·
                        rfl

theorem cell23_4820238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_4820238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820238 prefixEnd_4820238 := by exact prefixLift 4820238
  have htrace : WordTrace (prefixWord ++ tailWord_4820238) baseStart_4820238 baseEnd_4820238 := by
    simpa [prefixWord, tailWord_4820238, baseEnd_4820238] using wordTrace_append hprefix tailTrace_4820238
  have hstable : (prefixWord ++ tailWord_4820238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820238).length < 2 ^ (prefixWord ++ tailWord_4820238).sum := by decide
  have hdescent : baseEnd_4820238 < baseStart_4820238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820256 : List Nat := [2, 1, 1, 5, 4, 1, 1, 3, 1, 2, 2]
def baseStart_4820256 : Nat := 118140960795 + 4820256 * 2 ^ 59
def prefixEnd_4820256 : Nat := 4983230072969 + 3 ^ 40 * 4820256 * 2
def baseEnd_4820256 : Nat := 2475108205718797959932053

theorem tailTrace_4820256 : CollatzResearch.WordTrace tailWord_4820256 prefixEnd_4820256 2475108205718797959932053 := by
  unfold tailWord_4820256
  simp only [CollatzResearch.WordTrace]
  refine ⟨87904589812521610514444311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117206119750028814019259081 87904589812521610514444311)
  ·
    refine ⟨131856884718782415771666467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87904589812521610514444311 131856884718782415771666467)
    ·
      refine ⟨197785327078173623657499701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131856884718782415771666467 197785327078173623657499701)
      ·
        refine ⟨18542374413578777217890597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197785327078173623657499701 18542374413578777217890597)
        ·
          refine ⟨3476695202546020728354487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18542374413578777217890597 3476695202546020728354487)
          ·
            refine ⟨5215042803819031092531731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3476695202546020728354487 5215042803819031092531731)
            ·
              refine ⟨7822564205728546638797597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5215042803819031092531731 7822564205728546638797597)
              ·
                refine ⟨2933461577148204989549099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7822564205728546638797597 2933461577148204989549099)
                ·
                  refine ⟨4400192365722307484323649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933461577148204989549099 4400192365722307484323649)
                  ·
                    refine ⟨3300144274291730613242737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4400192365722307484323649 3300144274291730613242737)
                    ·
                      refine ⟨2475108205718797959932053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3300144274291730613242737 2475108205718797959932053)
                      ·
                        rfl

theorem cell23_4820256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_4820256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820256 prefixEnd_4820256 := by exact prefixLift 4820256
  have htrace : WordTrace (prefixWord ++ tailWord_4820256) baseStart_4820256 baseEnd_4820256 := by
    simpa [prefixWord, tailWord_4820256, baseEnd_4820256] using wordTrace_append hprefix tailTrace_4820256
  have hstable : (prefixWord ++ tailWord_4820256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820256).length < 2 ^ (prefixWord ++ tailWord_4820256).sum := by decide
  have hdescent : baseEnd_4820256 < baseStart_4820256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820289 : List Nat := [1, 2, 5, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_4820289 : Nat := 118140960795 + 4820289 * 2 ^ 59
def prefixEnd_4820289 : Nat := 4983230072969 + 3 ^ 40 * 4820289 * 2
def baseEnd_4820289 : Nat := 2475125150580396330819401

theorem tailTrace_4820289 : CollatzResearch.WordTrace tailWord_4820289 prefixEnd_4820289 2475125150580396330819401 := by
  unfold tailWord_4820289
  simp only [CollatzResearch.WordTrace]
  refine ⟨175810383233923667664839921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117206922155949111776559947 175810383233923667664839921)
  ·
    refine ⟨131857787425442750748629941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175810383233923667664839921 131857787425442750748629941)
    ·
      refine ⟨12361667571135257882684057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131857787425442750748629941 12361667571135257882684057)
      ·
        refine ⟨9271250678351443412013043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12361667571135257882684057 9271250678351443412013043)
        ·
          refine ⟨13906876017527165118019565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9271250678351443412013043 13906876017527165118019565)
          ·
            refine ⟨5215078506572686919257337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13906876017527165118019565 5215078506572686919257337)
            ·
              refine ⟨3911308879929515189443003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5215078506572686919257337 3911308879929515189443003)
              ·
                refine ⟨5866963319894272784164505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3911308879929515189443003 5866963319894272784164505)
                ·
                  refine ⟨4400222489920704588123379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5866963319894272784164505 4400222489920704588123379)
                  ·
                    refine ⟨6600333734881056882185069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4400222489920704588123379 6600333734881056882185069)
                    ·
                      refine ⟨2475125150580396330819401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6600333734881056882185069 2475125150580396330819401)
                      ·
                        rfl

theorem cell23_4820289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_4820289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820289 prefixEnd_4820289 := by exact prefixLift 4820289
  have htrace : WordTrace (prefixWord ++ tailWord_4820289) baseStart_4820289 baseEnd_4820289 := by
    simpa [prefixWord, tailWord_4820289, baseEnd_4820289] using wordTrace_append hprefix tailTrace_4820289
  have hstable : (prefixWord ++ tailWord_4820289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820289).length < 2 ^ (prefixWord ++ tailWord_4820289).sum := by decide
  have hdescent : baseEnd_4820289 < baseStart_4820289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820338 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 1, 7, 2]
def baseStart_4820338 : Nat := 118140960795 + 4820338 * 2 ^ 59
def prefixEnd_4820338 : Nat := 4983230072969 + 3 ^ 40 * 4820338 * 2
def baseEnd_4820338 : Nat := 2475150311132466639106675

theorem tailTrace_4820338 : CollatzResearch.WordTrace tailWord_4820338 prefixEnd_4820338 2475150311132466639106675 := by
  unfold tailWord_4820338
  simp only [CollatzResearch.WordTrace]
  refine ⟨43953042602686537258343417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117208113607164099355582445 43953042602686537258343417)
  ·
    refine ⟨32964781952014902943757563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43953042602686537258343417 32964781952014902943757563)
    ·
      refine ⟨49447172928022354415636345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32964781952014902943757563 49447172928022354415636345)
      ·
        refine ⟨37085379696016765811727259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49447172928022354415636345 37085379696016765811727259)
        ·
          refine ⟨55628069544025148717590889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37085379696016765811727259 55628069544025148717590889)
          ·
            refine ⟨41721052158018861538193167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55628069544025148717590889 41721052158018861538193167)
            ·
              refine ⟨62581578237028292307289751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41721052158018861538193167 62581578237028292307289751)
              ·
                refine ⟨93872367355542438460934627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62581578237028292307289751 93872367355542438460934627)
                ·
                  refine ⟨140808551033313657691401941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93872367355542438460934627 140808551033313657691401941)
                  ·
                    refine ⟨3300200414843288852142233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 140808551033313657691401941 3300200414843288852142233)
                    ·
                      refine ⟨2475150311132466639106675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3300200414843288852142233 2475150311132466639106675)
                      ·
                        rfl

theorem cell23_4820338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_4820338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820338 prefixEnd_4820338 := by exact prefixLift 4820338
  have htrace : WordTrace (prefixWord ++ tailWord_4820338) baseStart_4820338 baseEnd_4820338 := by
    simpa [prefixWord, tailWord_4820338, baseEnd_4820338] using wordTrace_append hprefix tailTrace_4820338
  have hstable : (prefixWord ++ tailWord_4820338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820338).length < 2 ^ (prefixWord ++ tailWord_4820338).sum := by decide
  have hdescent : baseEnd_4820338 < baseStart_4820338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820378 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 5, 4]
def baseStart_4820378 : Nat := 118140960795 + 4820378 * 2 ^ 59
def prefixEnd_4820378 : Nat := 4983230072969 + 3 ^ 40 * 4820378 * 2
def baseEnd_4820378 : Nat := 825056950119548827535497

theorem tailTrace_4820378 : CollatzResearch.WordTrace tailWord_4820378 prefixEnd_4820378 825056950119548827535497 := by
  unfold tailWord_4820378
  simp only [CollatzResearch.WordTrace]
  refine ⟨43953407332650308966207447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117209086220400823909886525 43953407332650308966207447)
  ·
    refine ⟨65930110998975463449311171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43953407332650308966207447 65930110998975463449311171)
    ·
      refine ⟨98895166498463195173966757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65930110998975463449311171 98895166498463195173966757)
      ·
        refine ⟨18542843718461849095118767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98895166498463195173966757 18542843718461849095118767)
        ·
          refine ⟨27814265577692773642678151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18542843718461849095118767 27814265577692773642678151)
          ·
            refine ⟨41721398366539160464017227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27814265577692773642678151 41721398366539160464017227)
            ·
              refine ⟨62582097549808740696025841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41721398366539160464017227 62582097549808740696025841)
              ·
                refine ⟨46936573162356555522019381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62582097549808740696025841 46936573162356555522019381)
                ·
                  refine ⟨4400303733970927080189317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46936573162356555522019381 4400303733970927080189317)
                  ·
                    refine ⟨825056950119548827535497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4400303733970927080189317 825056950119548827535497)
                    ·
                      rfl

theorem cell23_4820378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_4820378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820378 prefixEnd_4820378 := by exact prefixLift 4820378
  have htrace : WordTrace (prefixWord ++ tailWord_4820378) baseStart_4820378 baseEnd_4820378 := by
    simpa [prefixWord, tailWord_4820378, baseEnd_4820378] using wordTrace_append hprefix tailTrace_4820378
  have hstable : (prefixWord ++ tailWord_4820378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820378).length < 2 ^ (prefixWord ++ tailWord_4820378).sum := by decide
  have hdescent : baseEnd_4820378 < baseStart_4820378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820388 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_4820388 : Nat := 118140960795 + 4820388 * 2 ^ 59
def prefixEnd_4820388 : Nat := 4983230072969 + 3 ^ 40 * 4820388 * 2
def baseEnd_4820388 : Nat := 2475175985165191443481445

theorem tailTrace_4820388 : CollatzResearch.WordTrace tailWord_4820388 prefixEnd_4820388 2475175985165191443481445 := by
  unfold tailWord_4820388
  simp only [CollatzResearch.WordTrace]
  refine ⟨87906997030282503786346909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117209329373710005048462545 87906997030282503786346909)
  ·
    refine ⟨32965123886355938919880091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87906997030282503786346909 32965123886355938919880091)
    ·
      refine ⟨49447685829533908379820137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32965123886355938919880091 49447685829533908379820137)
      ·
        refine ⟨37085764372150431284865103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49447685829533908379820137 37085764372150431284865103)
        ·
          refine ⟨55628646558225646927297655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37085764372150431284865103 55628646558225646927297655)
          ·
            refine ⟨83442969837338470390946483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55628646558225646927297655 83442969837338470390946483)
            ·
              refine ⟨125164454756007705586419725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83442969837338470390946483 125164454756007705586419725)
              ·
                refine ⟨46936670533502889594907397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125164454756007705586419725 46936670533502889594907397)
                ·
                  refine ⟨8800625725031791799045137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46936670533502889594907397 8800625725031791799045137)
                  ·
                    refine ⟨6600469293773843849283853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8800625725031791799045137 6600469293773843849283853)
                    ·
                      refine ⟨2475175985165191443481445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6600469293773843849283853 2475175985165191443481445)
                      ·
                        rfl

theorem cell23_4820388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_4820388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820388 prefixEnd_4820388 := by exact prefixLift 4820388
  have htrace : WordTrace (prefixWord ++ tailWord_4820388) baseStart_4820388 baseEnd_4820388 := by
    simpa [prefixWord, tailWord_4820388, baseEnd_4820388] using wordTrace_append hprefix tailTrace_4820388
  have hstable : (prefixWord ++ tailWord_4820388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820388).length < 2 ^ (prefixWord ++ tailWord_4820388).sum := by decide
  have hdescent : baseEnd_4820388 < baseStart_4820388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820452 : List Nat := [2, 3, 1, 1, 1, 1, 1, 8, 1, 1, 3]
def baseStart_4820452 : Nat := 118140960795 + 4820452 * 2 ^ 59
def prefixEnd_4820452 : Nat := 4983230072969 + 3 ^ 40 * 4820452 * 2
def baseEnd_4820452 : Nat := 2475208847927079193081151

theorem tailTrace_4820452 : CollatzResearch.WordTrace tailWord_4820452 prefixEnd_4820452 2475208847927079193081151 := by
  unfold tailWord_4820452
  simp only [CollatzResearch.WordTrace]
  refine ⟨87908164166166573251511805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117210885554888764335349073 87908164166166573251511805)
  ·
    refine ⟨32965561562312464969316927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87908164166166573251511805 32965561562312464969316927)
    ·
      refine ⟨49448342343468697453975391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32965561562312464969316927 49448342343468697453975391)
      ·
        refine ⟨74172513515203046180963087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49448342343468697453975391 74172513515203046180963087)
        ·
          refine ⟨111258770272804569271444631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74172513515203046180963087 111258770272804569271444631)
          ·
            refine ⟨166888155409206853907166947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111258770272804569271444631 166888155409206853907166947)
            ·
              refine ⟨250332233113810280860750421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166888155409206853907166947 250332233113810280860750421)
              ·
                refine ⟨2933580856802464228836919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 250332233113810280860750421 2933580856802464228836919)
                ·
                  refine ⟨4400371285203696343255379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933580856802464228836919 4400371285203696343255379)
                  ·
                    refine ⟨6600556927805544514883069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4400371285203696343255379 6600556927805544514883069)
                    ·
                      refine ⟨2475208847927079193081151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6600556927805544514883069 2475208847927079193081151)
                      ·
                        rfl

theorem cell23_4820452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_4820452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820452 prefixEnd_4820452 := by exact prefixLift 4820452
  have htrace : WordTrace (prefixWord ++ tailWord_4820452) baseStart_4820452 baseEnd_4820452 := by
    simpa [prefixWord, tailWord_4820452, baseEnd_4820452] using wordTrace_append hprefix tailTrace_4820452
  have hstable : (prefixWord ++ tailWord_4820452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820452).length < 2 ^ (prefixWord ++ tailWord_4820452).sum := by decide
  have hdescent : baseEnd_4820452 < baseStart_4820452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820488 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_4820488 : Nat := 118140960795 + 4820488 * 2 ^ 59
def prefixEnd_4820488 : Nat := 4983230072969 + 3 ^ 40 * 4820488 * 2
def baseEnd_4820488 : Nat := 2475227333230641052230985

theorem tailTrace_4820488 : CollatzResearch.WordTrace tailWord_4820488 prefixEnd_4820488 2475227333230641052230985 := by
  unfold tailWord_4820488
  simp only [CollatzResearch.WordTrace]
  refine ⟨87908820680101362325667059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117211760906801816434222745 87908820680101362325667059)
  ·
    refine ⟨131863231020152043488500589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87908820680101362325667059 131863231020152043488500589)
    ·
      refine ⟨49448711632557016308187721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131863231020152043488500589 49448711632557016308187721)
      ·
        refine ⟨37086533724417762231140791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49448711632557016308187721 37086533724417762231140791)
        ·
          refine ⟨55629800586626643346711187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37086533724417762231140791 55629800586626643346711187)
          ·
            refine ⟨83444700879939965020066781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55629800586626643346711187 83444700879939965020066781)
            ·
              refine ⟨31291762829977486882525043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83444700879939965020066781 31291762829977486882525043)
              ·
                refine ⟨46937644244966230323787565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31291762829977486882525043 46937644244966230323787565)
                ·
                  refine ⟨17601616591862336371420337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46937644244966230323787565 17601616591862336371420337)
                  ·
                    refine ⟨13201212443896752278565253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17601616591862336371420337 13201212443896752278565253)
                    ·
                      refine ⟨2475227333230641052230985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13201212443896752278565253 2475227333230641052230985)
                      ·
                        rfl

theorem cell23_4820488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_4820488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820488 prefixEnd_4820488 := by exact prefixLift 4820488
  have htrace : WordTrace (prefixWord ++ tailWord_4820488) baseStart_4820488 baseEnd_4820488 := by
    simpa [prefixWord, tailWord_4820488, baseEnd_4820488] using wordTrace_append hprefix tailTrace_4820488
  have hstable : (prefixWord ++ tailWord_4820488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820488).length < 2 ^ (prefixWord ++ tailWord_4820488).sum := by decide
  have hdescent : baseEnd_4820488 < baseStart_4820488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820515 : List Nat := [1, 1, 1, 4, 5, 2, 1, 8]
def baseStart_4820515 : Nat := 118140960795 + 4820515 * 2 ^ 59
def prefixEnd_4820515 : Nat := 4983230072969 + 3 ^ 40 * 4820515 * 2
def baseEnd_4820515 : Nat := 91675599896604164688643

theorem tailTrace_4820515 : CollatzResearch.WordTrace tailWord_4820515 prefixEnd_4820515 91675599896604164688643 := by
  unfold tailWord_4820515
  simp only [CollatzResearch.WordTrace]
  refine ⟨175818626131104908262566999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117212417420736605508377999 175818626131104908262566999)
  ·
    refine ⟨263727939196657362393850499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175818626131104908262566999 263727939196657362393850499)
    ·
      refine ⟨395591908794986043590775749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263727939196657362393850499 395591908794986043590775749)
      ·
        refine ⟨74173482899059883173270453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 395591908794986043590775749 74173482899059883173270453)
        ·
          refine ⟨6953764021786864047494105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74173482899059883173270453 6953764021786864047494105)
          ·
            refine ⟨5215323016340148035620579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6953764021786864047494105 5215323016340148035620579)
            ·
              refine ⟨7822984524510222053430869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5215323016340148035620579 7822984524510222053430869)
              ·
                refine ⟨91675599896604164688643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7822984524510222053430869 91675599896604164688643)
                ·
                  rfl

theorem cell23_4820515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 8].length) (baseStart_4820515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820515 prefixEnd_4820515 := by exact prefixLift 4820515
  have htrace : WordTrace (prefixWord ++ tailWord_4820515) baseStart_4820515 baseEnd_4820515 := by
    simpa [prefixWord, tailWord_4820515, baseEnd_4820515] using wordTrace_append hprefix tailTrace_4820515
  have hstable : (prefixWord ++ tailWord_4820515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820515).length < 2 ^ (prefixWord ++ tailWord_4820515).sum := by decide
  have hdescent : baseEnd_4820515 < baseStart_4820515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820538 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_4820538 : Nat := 118140960795 + 4820538 * 2 ^ 59
def prefixEnd_4820538 : Nat := 4983230072969 + 3 ^ 40 * 4820538 * 2
def baseEnd_4820538 : Nat := 2475253007263365856605755

theorem tailTrace_4820538 : CollatzResearch.WordTrace tailWord_4820538 prefixEnd_4820538 2475253007263365856605755 := by
  unfold tailWord_4820538
  simp only [CollatzResearch.WordTrace]
  refine ⟨43954866252505395797663567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117212976673347722127102845 43954866252505395797663567)
  ·
    refine ⟨65932299378758093696495351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43954866252505395797663567 65932299378758093696495351)
    ·
      refine ⟨98898449068137140544743027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65932299378758093696495351 98898449068137140544743027)
      ·
        refine ⟨148347673602205710817114541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98898449068137140544743027 148347673602205710817114541)
        ·
          refine ⟨55630377600827141556417953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148347673602205710817114541 55630377600827141556417953)
          ·
            refine ⟨41722783200620356167313465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55630377600827141556417953 41722783200620356167313465)
            ·
              refine ⟨31292087400465267125485099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41722783200620356167313465 31292087400465267125485099)
              ·
                refine ⟨46938131100697900688227649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31292087400465267125485099 46938131100697900688227649)
                ·
                  refine ⟨35203598325523425516170737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46938131100697900688227649 35203598325523425516170737)
                  ·
                    refine ⟨26402698744142569137128053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35203598325523425516170737 26402698744142569137128053)
                    ·
                      refine ⟨2475253007263365856605755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26402698744142569137128053 2475253007263365856605755)
                      ·
                        rfl

theorem cell23_4820538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_4820538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820538 prefixEnd_4820538 := by exact prefixLift 4820538
  have htrace : WordTrace (prefixWord ++ tailWord_4820538) baseStart_4820538 baseEnd_4820538 := by
    simpa [prefixWord, tailWord_4820538, baseEnd_4820538] using wordTrace_append hprefix tailTrace_4820538
  have hstable : (prefixWord ++ tailWord_4820538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820538).length < 2 ^ (prefixWord ++ tailWord_4820538).sum := by decide
  have hdescent : baseEnd_4820538 < baseStart_4820538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820568 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_4820568 : Nat := 118140960795 + 4820568 * 2 ^ 59
def prefixEnd_4820568 : Nat := 4983230072969 + 3 ^ 40 * 4820568 * 2
def baseEnd_4820568 : Nat := 2475268411683000739230617

theorem tailTrace_4820568 : CollatzResearch.WordTrace tailWord_4820568 prefixEnd_4820568 2475268411683000739230617 := by
  unfold tailWord_4820568
  simp only [CollatzResearch.WordTrace]
  refine ⟨87910279599956449157123179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117213706133275265542830905 87910279599956449157123179)
  ·
    refine ⟨131865419399934673735684769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87910279599956449157123179 131865419399934673735684769)
    ·
      refine ⟨98899064549951005301763577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131865419399934673735684769 98899064549951005301763577)
      ·
        refine ⟨74174298412463253976322683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98899064549951005301763577 74174298412463253976322683)
        ·
          refine ⟨111261447618694880964484025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74174298412463253976322683 111261447618694880964484025)
          ·
            refine ⟨83446085714021160723363019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111261447618694880964484025 83446085714021160723363019)
            ·
              refine ⟨125169128571031741085044529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83446085714021160723363019 125169128571031741085044529)
              ·
                refine ⟨93876846428273805813783397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125169128571031741085044529 93876846428273805813783397)
                ·
                  refine ⟨17601908705301338590084387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93876846428273805813783397 17601908705301338590084387)
                  ·
                    refine ⟨26402863057952007885126581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17601908705301338590084387 26402863057952007885126581)
                    ·
                      refine ⟨2475268411683000739230617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26402863057952007885126581 2475268411683000739230617)
                      ·
                        rfl

theorem cell23_4820568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_4820568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820568 prefixEnd_4820568 := by exact prefixLift 4820568
  have htrace : WordTrace (prefixWord ++ tailWord_4820568) baseStart_4820568 baseEnd_4820568 := by
    simpa [prefixWord, tailWord_4820568, baseEnd_4820568] using wordTrace_append hprefix tailTrace_4820568
  have hstable : (prefixWord ++ tailWord_4820568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820568).length < 2 ^ (prefixWord ++ tailWord_4820568).sum := by decide
  have hdescent : baseEnd_4820568 < baseStart_4820568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820622 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 7]
def baseStart_4820622 : Nat := 118140960795 + 4820622 * 2 ^ 59
def prefixEnd_4820622 : Nat := 4983230072969 + 3 ^ 40 * 4820622 * 2
def baseEnd_4820622 : Nat := 275032904404260391995041

theorem tailTrace_4820622 : CollatzResearch.WordTrace tailWord_4820622 prefixEnd_4820622 275032904404260391995041 := by
  unfold tailWord_4820622
  simp only [CollatzResearch.WordTrace]
  refine ⟨21977816092714658192089015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117215019161144843691141413 21977816092714658192089015)
  ·
    refine ⟨32966724139071987288133523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21977816092714658192089015 32966724139071987288133523)
    ·
      refine ⟨49450086208607980932200285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32966724139071987288133523 49450086208607980932200285)
      ·
        refine ⟨18543782328227992849575107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49450086208607980932200285 18543782328227992849575107)
        ·
          refine ⟨27815673492341989274362661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18543782328227992849575107 27815673492341989274362661)
          ·
            refine ⟨5215438779814122988942999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27815673492341989274362661 5215438779814122988942999)
            ·
              refine ⟨7823158169721184483414499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5215438779814122988942999 7823158169721184483414499)
              ·
                refine ⟨11734737254581776725121749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7823158169721184483414499 11734737254581776725121749)
                ·
                  refine ⟨275032904404260391995041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11734737254581776725121749 275032904404260391995041)
                  ·
                    rfl

theorem cell23_4820622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_4820622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820622 prefixEnd_4820622 := by exact prefixLift 4820622
  have htrace : WordTrace (prefixWord ++ tailWord_4820622) baseStart_4820622 baseEnd_4820622 := by
    simpa [prefixWord, tailWord_4820622, baseEnd_4820622] using wordTrace_append hprefix tailTrace_4820622
  have hstable : (prefixWord ++ tailWord_4820622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820622).length < 2 ^ (prefixWord ++ tailWord_4820622).sum := by decide
  have hdescent : baseEnd_4820622 < baseStart_4820622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820672 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 2, 4, 2]
def baseStart_4820672 : Nat := 118140960795 + 4820672 * 2 ^ 59
def prefixEnd_4820672 : Nat := 4983230072969 + 3 ^ 40 * 4820672 * 2
def baseEnd_4820672 : Nat := 2475321813671068332330139

theorem tailTrace_4820672 : CollatzResearch.WordTrace tailWord_4820672 prefixEnd_4820672 2475321813671068332330139 := by
  unfold tailWord_4820672
  simp only [CollatzResearch.WordTrace]
  refine ⟨87912176195768062038016135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117216234927690749384021513 87912176195768062038016135)
  ·
    refine ⟨131868264293652093057024203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87912176195768062038016135 131868264293652093057024203)
    ·
      refine ⟨197802396440478139585536305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131868264293652093057024203 197802396440478139585536305)
      ·
        refine ⟨148351797330358604689152229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197802396440478139585536305 148351797330358604689152229)
        ·
          refine ⟨27815961999442238379216043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148351797330358604689152229 27815961999442238379216043)
          ·
            refine ⟨41723942999163357568824065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27815961999442238379216043 41723942999163357568824065)
            ·
              refine ⟨31292957249372518176618049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41723942999163357568824065 31292957249372518176618049)
              ·
                refine ⟨23469717937029388632463537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31292957249372518176618049 23469717937029388632463537)
                ·
                  refine ⟨17602288452772041474347653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23469717937029388632463537 17602288452772041474347653)
                  ·
                    refine ⟨3300429084894757776440185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17602288452772041474347653 3300429084894757776440185)
                    ·
                      refine ⟨2475321813671068332330139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3300429084894757776440185 2475321813671068332330139)
                      ·
                        rfl

theorem cell23_4820672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 4, 2].length) (baseStart_4820672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820672 prefixEnd_4820672 := by exact prefixLift 4820672
  have htrace : WordTrace (prefixWord ++ tailWord_4820672) baseStart_4820672 baseEnd_4820672 := by
    simpa [prefixWord, tailWord_4820672, baseEnd_4820672] using wordTrace_append hprefix tailTrace_4820672
  have hstable : (prefixWord ++ tailWord_4820672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820672).length < 2 ^ (prefixWord ++ tailWord_4820672).sum := by decide
  have hdescent : baseEnd_4820672 < baseStart_4820672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820695 : List Nat := [1, 1, 3, 2, 1, 3, 1, 5, 6]
def baseStart_4820695 : Nat := 118140960795 + 4820695 * 2 ^ 59
def prefixEnd_4820695 : Nat := 4983230072969 + 3 ^ 40 * 4820695 * 2
def baseEnd_4820695 : Nat := 275037069302902415815837

theorem tailTrace_4820695 : CollatzResearch.WordTrace tailWord_4820695 prefixEnd_4820695 275037069302902415815837 := by
  unfold tailWord_4820695
  simp only [CollatzResearch.WordTrace]
  refine ⟨175825191270452799004119539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117216794180301866002746359 175825191270452799004119539)
  ·
    refine ⟨263737786905679198506179309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175825191270452799004119539 263737786905679198506179309)
    ·
      refine ⟨98901670089629699439817241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263737786905679198506179309 98901670089629699439817241)
      ·
        refine ⟨74176252567222274579862931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98901670089629699439817241 74176252567222274579862931)
        ·
          refine ⟨111264378850833411869794397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74176252567222274579862931 111264378850833411869794397)
          ·
            refine ⟨41724142069062529451172899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111264378850833411869794397 41724142069062529451172899)
            ·
              refine ⟨62586213103593794176759349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41724142069062529451172899 62586213103593794176759349)
              ·
                refine ⟨5867457478461918204071189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62586213103593794176759349 5867457478461918204071189)
                ·
                  refine ⟨275037069302902415815837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5867457478461918204071189 275037069302902415815837)
                  ·
                    rfl

theorem cell23_4820695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 6].length) (baseStart_4820695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820695 prefixEnd_4820695 := by exact prefixLift 4820695
  have htrace : WordTrace (prefixWord ++ tailWord_4820695) baseStart_4820695 baseEnd_4820695 := by
    simpa [prefixWord, tailWord_4820695, baseEnd_4820695] using wordTrace_append hprefix tailTrace_4820695
  have hstable : (prefixWord ++ tailWord_4820695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820695).length < 2 ^ (prefixWord ++ tailWord_4820695).sum := by decide
  have hdescent : baseEnd_4820695 < baseStart_4820695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820755 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 1, 6]
def baseStart_4820755 : Nat := 118140960795 + 4820755 * 2 ^ 59
def prefixEnd_4820755 : Nat := 4983230072969 + 3 ^ 40 * 4820755 * 2
def baseEnd_4820755 : Nat := 825121477521797169197419

theorem tailTrace_4820755 : CollatzResearch.WordTrace tailWord_4820755 prefixEnd_4820755 825121477521797169197419 := by
  unfold tailWord_4820755
  simp only [CollatzResearch.WordTrace]
  refine ⟨175827379650235429251303719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117218253100156952834202479 175827379650235429251303719)
  ·
    refine ⟨263741069475353143876955579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175827379650235429251303719 263741069475353143876955579)
    ·
      refine ⟨395611604213029715815433369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263741069475353143876955579 395611604213029715815433369)
      ·
        refine ⟨296708703159772286861575027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395611604213029715815433369 296708703159772286861575027)
        ·
          refine ⟨445063054739658430292362541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296708703159772286861575027 445063054739658430292362541)
          ·
            refine ⟨166898645527371911359635953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 445063054739658430292362541 166898645527371911359635953)
            ·
              refine ⟨125173984145528933519726965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166898645527371911359635953 125173984145528933519726965)
              ·
                refine ⟨11735061013643337517474403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125173984145528933519726965 11735061013643337517474403)
                ·
                  refine ⟨17602591520465006276211605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11735061013643337517474403 17602591520465006276211605)
                  ·
                    refine ⟨825121477521797169197419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17602591520465006276211605 825121477521797169197419)
                    ·
                      rfl

theorem cell23_4820755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 6].length) (baseStart_4820755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820755 prefixEnd_4820755 := by exact prefixLift 4820755
  have htrace : WordTrace (prefixWord ++ tailWord_4820755) baseStart_4820755 baseEnd_4820755 := by
    simpa [prefixWord, tailWord_4820755, baseEnd_4820755] using wordTrace_append hprefix tailTrace_4820755
  have hstable : (prefixWord ++ tailWord_4820755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820755).length < 2 ^ (prefixWord ++ tailWord_4820755).sum := by decide
  have hdescent : baseEnd_4820755 < baseStart_4820755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820759 : List Nat := [1, 1, 3, 4, 2, 2, 2, 2, 1, 5]
def baseStart_4820759 : Nat := 118140960795 + 4820759 * 2 ^ 59
def prefixEnd_4820759 : Nat := 4983230072969 + 3 ^ 40 * 4820759 * 2
def baseEnd_4820759 : Nat := 825122162162669830647413

theorem tailTrace_4820759 : CollatzResearch.WordTrace tailWord_4820759 prefixEnd_4820759 825122162162669830647413 := by
  unfold tailWord_4820759
  simp only [CollatzResearch.WordTrace]
  refine ⟨175827525542220937934449331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117218350361480625289632887 175827525542220937934449331)
  ·
    refine ⟨263741288313331406901673997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175827525542220937934449331 263741288313331406901673997)
    ·
      refine ⟨98902983117499277588127749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263741288313331406901673997 98902983117499277588127749)
      ·
        refine ⟨18544309334531114547773953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98902983117499277588127749 18544309334531114547773953)
        ·
          refine ⟨13908232000898335910830465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18544309334531114547773953 13908232000898335910830465)
          ·
            refine ⟨10431174000673751933122849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13908232000898335910830465 10431174000673751933122849)
            ·
              refine ⟨7823380500505313949842137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10431174000673751933122849 7823380500505313949842137)
              ·
                refine ⟨5867535375378985462381603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7823380500505313949842137 5867535375378985462381603)
                ·
                  refine ⟨8801303063068478193572405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5867535375378985462381603 8801303063068478193572405)
                  ·
                    refine ⟨825122162162669830647413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8801303063068478193572405 825122162162669830647413)
                    ·
                      rfl

theorem cell23_4820759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_4820759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820759 prefixEnd_4820759 := by exact prefixLift 4820759
  have htrace : WordTrace (prefixWord ++ tailWord_4820759) baseStart_4820759 baseEnd_4820759 := by
    simpa [prefixWord, tailWord_4820759, baseEnd_4820759] using wordTrace_append hprefix tailTrace_4820759
  have hstable : (prefixWord ++ tailWord_4820759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820759).length < 2 ^ (prefixWord ++ tailWord_4820759).sum := by decide
  have hdescent : baseEnd_4820759 < baseStart_4820759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820773 : List Nat := [1, 3, 1, 2, 3, 4, 1, 3, 1, 1, 3]
def baseStart_4820773 : Nat := 118140960795 + 4820773 * 2 ^ 59
def prefixEnd_4820773 : Nat := 4983230072969 + 3 ^ 40 * 4820773 * 2
def baseEnd_4820773 : Nat := 2475373675217172437167175

theorem tailTrace_4820773 : CollatzResearch.WordTrace tailWord_4820773 prefixEnd_4820773 2475373675217172437167175 := by
  unfold tailWord_4820773
  simp only [CollatzResearch.WordTrace]
  refine ⟨175828036164170218325458973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117218690776113478883639315 175828036164170218325458973)
  ·
    refine ⟨65935513561563831872047115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175828036164170218325458973 65935513561563831872047115)
    ·
      refine ⟨98903270342345747808070673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65935513561563831872047115 98903270342345747808070673)
      ·
        refine ⟨74177452756759310856053005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98903270342345747808070673 74177452756759310856053005)
        ·
          refine ⟨27816544783784741571019877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74177452756759310856053005 27816544783784741571019877)
          ·
            refine ⟨5215602146959639044566227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27816544783784741571019877 5215602146959639044566227)
            ·
              refine ⟨7823403220439458566849341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5215602146959639044566227 7823403220439458566849341)
              ·
                refine ⟨2933776207664796962568503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7823403220439458566849341 2933776207664796962568503)
                ·
                  refine ⟨4400664311497195443852755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933776207664796962568503 4400664311497195443852755)
                  ·
                    refine ⟨6600996467245793165779133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4400664311497195443852755 6600996467245793165779133)
                    ·
                      refine ⟨2475373675217172437167175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6600996467245793165779133 2475373675217172437167175)
                      ·
                        rfl

theorem cell23_4820773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_4820773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820773 prefixEnd_4820773 := by exact prefixLift 4820773
  have htrace : WordTrace (prefixWord ++ tailWord_4820773) baseStart_4820773 baseEnd_4820773 := by
    simpa [prefixWord, tailWord_4820773, baseEnd_4820773] using wordTrace_append hprefix tailTrace_4820773
  have hstable : (prefixWord ++ tailWord_4820773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820773).length < 2 ^ (prefixWord ++ tailWord_4820773).sum := by decide
  have hdescent : baseEnd_4820773 < baseStart_4820773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820785 : List Nat := [1, 2, 2, 3, 2, 2, 11]
def baseStart_4820785 : Nat := 118140960795 + 4820785 * 2 ^ 59
def prefixEnd_4820785 : Nat := 4983230072969 + 3 ^ 40 * 4820785 * 2
def baseEnd_4820785 : Nat := 30560244901049708521199

theorem tailTrace_4820785 : CollatzResearch.WordTrace tailWord_4820785 prefixEnd_4820785 30560244901049708521199 := by
  unfold tailWord_4820785
  simp only [CollatzResearch.WordTrace]
  refine ⟨175828473840126744374895809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117218982560084496249930539 175828473840126744374895809)
  ·
    refine ⟨131871355380095058281171857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175828473840126744374895809 131871355380095058281171857)
    ·
      refine ⟨98903516535071293710878893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131871355380095058281171857 98903516535071293710878893)
      ·
        refine ⟨37088818700651735141579585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98903516535071293710878893 37088818700651735141579585)
        ·
          refine ⟨27816614025488801356184689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37088818700651735141579585 27816614025488801356184689)
          ·
            refine ⟨20862460519116601017138517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27816614025488801356184689 20862460519116601017138517)
            ·
              refine ⟨30560244901049708521199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20862460519116601017138517 30560244901049708521199)
              ·
                rfl

theorem cell23_4820785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 11].length) (baseStart_4820785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820785 prefixEnd_4820785 := by exact prefixLift 4820785
  have htrace : WordTrace (prefixWord ++ tailWord_4820785) baseStart_4820785 baseEnd_4820785 := by
    simpa [prefixWord, tailWord_4820785, baseEnd_4820785] using wordTrace_append hprefix tailTrace_4820785
  have hstable : (prefixWord ++ tailWord_4820785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820785).length < 2 ^ (prefixWord ++ tailWord_4820785).sum := by decide
  have hdescent : baseEnd_4820785 < baseStart_4820785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820796 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 3, 2, 2]
def baseStart_4820796 : Nat := 118140960795 + 4820796 * 2 ^ 59
def prefixEnd_4820796 : Nat := 4983230072969 + 3 ^ 40 * 4820796 * 2
def baseEnd_4820796 : Nat := 2475385485272225847179569

theorem tailTrace_4820796 : CollatzResearch.WordTrace tailWord_4820796 prefixEnd_4820796 2475385485272225847179569 := by
  unfold tailWord_4820796
  simp only [CollatzResearch.WordTrace]
  refine ⟨87914437521543446626773121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117219250028724595502364161 87914437521543446626773121)
  ·
    refine ⟨65935828141157584970079841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87914437521543446626773121 65935828141157584970079841)
    ·
      refine ⟨49451871105868188727559881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65935828141157584970079841 49451871105868188727559881)
      ·
        refine ⟨37088903329401141545669911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49451871105868188727559881 37088903329401141545669911)
        ·
          refine ⟨55633354994101712318504867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37088903329401141545669911 55633354994101712318504867)
          ·
            refine ⟨83450032491152568477757301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55633354994101712318504867 83450032491152568477757301)
            ·
              refine ⟨7823440546045553294789747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83450032491152568477757301 7823440546045553294789747)
              ·
                refine ⟨11735160819068329942184621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7823440546045553294789747 11735160819068329942184621)
                ·
                  refine ⟨4400685307150623728319233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11735160819068329942184621 4400685307150623728319233)
                  ·
                    refine ⟨3300513980362967796239425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4400685307150623728319233 3300513980362967796239425)
                    ·
                      refine ⟨2475385485272225847179569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3300513980362967796239425 2475385485272225847179569)
                      ·
                        rfl

theorem cell23_4820796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_4820796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820796 prefixEnd_4820796 := by exact prefixLift 4820796
  have htrace : WordTrace (prefixWord ++ tailWord_4820796) baseStart_4820796 baseEnd_4820796 := by
    simpa [prefixWord, tailWord_4820796, baseEnd_4820796] using wordTrace_append hprefix tailTrace_4820796
  have hstable : (prefixWord ++ tailWord_4820796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820796).length < 2 ^ (prefixWord ++ tailWord_4820796).sum := by decide
  have hdescent : baseEnd_4820796 < baseStart_4820796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820805 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_4820805 : Nat := 118140960795 + 4820805 * 2 ^ 59
def prefixEnd_4820805 : Nat := 4983230072969 + 3 ^ 40 * 4820805 * 2
def baseEnd_4820805 : Nat := 2475390106598116311967027

theorem tailTrace_4820805 : CollatzResearch.WordTrace tailWord_4820805 prefixEnd_4820805 2475390106598116311967027 := by
  unfold tailWord_4820805
  simp only [CollatzResearch.WordTrace]
  refine ⟨175829203300054287790623869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117219468866702858527082579 175829203300054287790623869)
  ·
    refine ⟨65935951237520357921483951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175829203300054287790623869 65935951237520357921483951)
    ·
      refine ⟨98903926856280536882225927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65935951237520357921483951 98903926856280536882225927)
      ·
        refine ⟨148355890284420805323338891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98903926856280536882225927 148355890284420805323338891)
        ·
          refine ⟨222533835426631207985008337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148355890284420805323338891 222533835426631207985008337)
          ·
            refine ⟨166900376569973405988756253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222533835426631207985008337 166900376569973405988756253)
            ·
              refine ⟨62587641213740027245783595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166900376569973405988756253 62587641213740027245783595)
              ·
                refine ⟨93881461820610040868675393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62587641213740027245783595 93881461820610040868675393)
                ·
                  refine ⟨70411096365457530651506545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93881461820610040868675393 70411096365457530651506545)
                  ·
                    refine ⟨52808322274093147988629909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70411096365457530651506545 52808322274093147988629909)
                    ·
                      refine ⟨2475390106598116311967027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52808322274093147988629909 2475390106598116311967027)
                      ·
                        rfl

theorem cell23_4820805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_4820805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820805 prefixEnd_4820805 := by exact prefixLift 4820805
  have htrace : WordTrace (prefixWord ++ tailWord_4820805) baseStart_4820805 baseEnd_4820805 := by
    simpa [prefixWord, tailWord_4820805, baseEnd_4820805] using wordTrace_append hprefix tailTrace_4820805
  have hstable : (prefixWord ++ tailWord_4820805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820805).length < 2 ^ (prefixWord ++ tailWord_4820805).sum := by decide
  have hdescent : baseEnd_4820805 < baseStart_4820805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820813 : List Nat := [1, 6, 1, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_4820813 : Nat := 118140960795 + 4820813 * 2 ^ 59
def prefixEnd_4820813 : Nat := 4983230072969 + 3 ^ 40 * 4820813 * 2
def baseEnd_4820813 : Nat := 2475394214443352280666991

theorem tailTrace_4820813 : CollatzResearch.WordTrace tailWord_4820813 prefixEnd_4820813 2475394214443352280666991 := by
  unfold tailWord_4820813
  simp only [CollatzResearch.WordTrace]
  refine ⟨175829495084025305156915093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117219663389350203437943395 175829495084025305156915093)
  ·
    refine ⟨8242007582063686179230395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 175829495084025305156915093 8242007582063686179230395)
    ·
      refine ⟨12363011373095529268845593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8242007582063686179230395 12363011373095529268845593)
      ·
        refine ⟨9272258529821646951634195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12363011373095529268845593 9272258529821646951634195)
        ·
          refine ⟨13908387794732470427451293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9272258529821646951634195 13908387794732470427451293)
          ·
            refine ⟨5215645423024676410294235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13908387794732470427451293 5215645423024676410294235)
            ·
              refine ⟨7823468134537014615441353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5215645423024676410294235 7823468134537014615441353)
              ·
                refine ⟨5867601100902760961581015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7823468134537014615441353 5867601100902760961581015)
                ·
                  refine ⟨8801401651354141442371523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5867601100902760961581015 8801401651354141442371523)
                  ·
                    refine ⟨13202102477031212163557285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8801401651354141442371523 13202102477031212163557285)
                    ·
                      refine ⟨2475394214443352280666991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13202102477031212163557285 2475394214443352280666991)
                      ·
                        rfl

theorem cell23_4820813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_4820813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820813 prefixEnd_4820813 := by exact prefixLift 4820813
  have htrace : WordTrace (prefixWord ++ tailWord_4820813) baseStart_4820813 baseEnd_4820813 := by
    simpa [prefixWord, tailWord_4820813, baseEnd_4820813] using wordTrace_append hprefix tailTrace_4820813
  have hstable : (prefixWord ++ tailWord_4820813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820813).length < 2 ^ (prefixWord ++ tailWord_4820813).sum := by decide
  have hdescent : baseEnd_4820813 < baseStart_4820813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820890 : List Nat := [3, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2]
def baseStart_4820890 : Nat := 118140960795 + 4820890 * 2 ^ 59
def prefixEnd_4820890 : Nat := 4983230072969 + 3 ^ 40 * 4820890 * 2
def baseEnd_4820890 : Nat := 2475433752453748479404137

theorem tailTrace_4820890 : CollatzResearch.WordTrace tailWord_4820890 prefixEnd_4820890 2475433752453748479404137 := by
  unfold tailWord_4820890
  simp only [CollatzResearch.WordTrace]
  refine ⟨43958075876186586826867031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117221535669830898204978749 43958075876186586826867031)
  ·
    refine ⟨65937113814279880240300547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43958075876186586826867031 65937113814279880240300547)
    ·
      refine ⟨98905670721419820360450821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65937113814279880240300547 98905670721419820360450821)
      ·
        refine ⟨18544813260266216317584529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98905670721419820360450821 18544813260266216317584529)
        ·
          refine ⟨13908609945199662238188397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18544813260266216317584529 13908609945199662238188397)
          ·
            refine ⟨5215728729449873339320649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13908609945199662238188397 5215728729449873339320649)
            ·
              refine ⟨3911796547087405004490487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5215728729449873339320649 3911796547087405004490487)
              ·
                refine ⟨5867694820631107506735731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3911796547087405004490487 5867694820631107506735731)
                ·
                  refine ⟨8801542230946661260103597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5867694820631107506735731 8801542230946661260103597)
                  ·
                    refine ⟨3300578336604997972538849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8801542230946661260103597 3300578336604997972538849)
                    ·
                      refine ⟨2475433752453748479404137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3300578336604997972538849 2475433752453748479404137)
                      ·
                        rfl

theorem cell23_4820890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_4820890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820890 prefixEnd_4820890 := by exact prefixLift 4820890
  have htrace : WordTrace (prefixWord ++ tailWord_4820890) baseStart_4820890 baseEnd_4820890 := by
    simpa [prefixWord, tailWord_4820890, baseEnd_4820890] using wordTrace_append hprefix tailTrace_4820890
  have hstable : (prefixWord ++ tailWord_4820890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820890).length < 2 ^ (prefixWord ++ tailWord_4820890).sum := by decide
  have hdescent : baseEnd_4820890 < baseStart_4820890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820903 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_4820903 : Nat := 118140960795 + 4820903 * 2 ^ 59
def prefixEnd_4820903 : Nat := 4983230072969 + 3 ^ 40 * 4820903 * 2
def baseEnd_4820903 : Nat := 2475440427702256928541577

theorem tailTrace_4820903 : CollatzResearch.WordTrace tailWord_4820903 prefixEnd_4820903 2475440427702256928541577 := by
  unfold tailWord_4820903
  simp only [CollatzResearch.WordTrace]
  refine ⟨175832777653699250527691363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117221851769132833685127575 175832777653699250527691363)
  ·
    refine ⟨263749166480548875791537045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175832777653699250527691363 263749166480548875791537045)
    ·
      refine ⟨12363242178775728552728299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 263749166480548875791537045 12363242178775728552728299)
      ·
        refine ⟨18544863268163592829092449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12363242178775728552728299 18544863268163592829092449)
        ·
          refine ⟨13908647451122694621819337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18544863268163592829092449 13908647451122694621819337)
          ·
            refine ⟨10431485588342020966364503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13908647451122694621819337 10431485588342020966364503)
            ·
              refine ⟨15647228382513031449546755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10431485588342020966364503 15647228382513031449546755)
              ·
                refine ⟨23470842573769547174320133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15647228382513031449546755 23470842573769547174320133)
                ·
                  refine ⟨4400782982581790095185025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23470842573769547174320133 4400782982581790095185025)
                  ·
                    refine ⟨3300587236936342571388769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4400782982581790095185025 3300587236936342571388769)
                    ·
                      refine ⟨2475440427702256928541577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3300587236936342571388769 2475440427702256928541577)
                      ·
                        rfl

theorem cell23_4820903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_4820903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820903 prefixEnd_4820903 := by exact prefixLift 4820903
  have htrace : WordTrace (prefixWord ++ tailWord_4820903) baseStart_4820903 baseEnd_4820903 := by
    simpa [prefixWord, tailWord_4820903, baseEnd_4820903] using wordTrace_append hprefix tailTrace_4820903
  have hstable : (prefixWord ++ tailWord_4820903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820903).length < 2 ^ (prefixWord ++ tailWord_4820903).sum := by decide
  have hdescent : baseEnd_4820903 < baseStart_4820903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820922 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 6, 5]
def baseStart_4820922 : Nat := 118140960795 + 4820922 * 2 ^ 59
def prefixEnd_4820922 : Nat := 4983230072969 + 3 ^ 40 * 4820922 * 2
def baseEnd_4820922 : Nat := 825150061278230784734663

theorem tailTrace_4820922 : CollatzResearch.WordTrace tailWord_4820922 prefixEnd_4820922 825150061278230784734663 := by
  unfold tailWord_4820922
  simp only [CollatzResearch.WordTrace]
  refine ⟨43958367660157604193158255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117222313760420277848422013 43958367660157604193158255)
  ·
    refine ⟨65937551490236406289737383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43958367660157604193158255 65937551490236406289737383)
    ·
      refine ⟨98906327235354609434606075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65937551490236406289737383 98906327235354609434606075)
      ·
        refine ⟨148359490853031914151909113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98906327235354609434606075 148359490853031914151909113)
        ·
          refine ⟨111269618139773935613931835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148359490853031914151909113 111269618139773935613931835)
          ·
            refine ⟨166904427209660903420897753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111269618139773935613931835 166904427209660903420897753)
            ·
              refine ⟨125178320407245677565673315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166904427209660903420897753 125178320407245677565673315)
              ·
                refine ⟨187767480610868516348509973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125178320407245677565673315 187767480610868516348509973)
                ·
                  refine ⟨8801600653634461703836405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 187767480610868516348509973 8801600653634461703836405)
                  ·
                    refine ⟨825150061278230784734663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8801600653634461703836405 825150061278230784734663)
                    ·
                      rfl

theorem cell23_4820922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_4820922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820922 prefixEnd_4820922 := by exact prefixLift 4820922
  have htrace : WordTrace (prefixWord ++ tailWord_4820922) baseStart_4820922 baseEnd_4820922 := by
    simpa [prefixWord, tailWord_4820922, baseEnd_4820922] using wordTrace_append hprefix tailTrace_4820922
  have hstable : (prefixWord ++ tailWord_4820922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820922).length < 2 ^ (prefixWord ++ tailWord_4820922).sum := by decide
  have hdescent : baseEnd_4820922 < baseStart_4820922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820959 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 4]
def baseStart_4820959 : Nat := 118140960795 + 4820959 * 2 ^ 59
def prefixEnd_4820959 : Nat := 4983230072969 + 3 ^ 40 * 4820959 * 2
def baseEnd_4820959 : Nat := 2475469182618908709441319

theorem tailTrace_4820959 : CollatzResearch.WordTrace tailWord_4820959 prefixEnd_4820959 2475469182618908709441319 := by
  unfold tailWord_4820959
  simp only [CollatzResearch.WordTrace]
  refine ⟨175834820141496372091729931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117223213427664248061153287 175834820141496372091729931)
  ·
    refine ⟨263752230212244558137594897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175834820141496372091729931 263752230212244558137594897)
    ·
      refine ⟨197814172659183418603196173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263752230212244558137594897 197814172659183418603196173)
      ·
        refine ⟨74180314747193781976198565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197814172659183418603196173 74180314747193781976198565)
        ·
          refine ⟨13908809015098834120537231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74180314747193781976198565 13908809015098834120537231)
          ·
            refine ⟨20863213522648251180805847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13908809015098834120537231 20863213522648251180805847)
            ·
              refine ⟨31294820283972376771208771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20863213522648251180805847 31294820283972376771208771)
              ·
                refine ⟨46942230425958565156813157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31294820283972376771208771 46942230425958565156813157)
                ·
                  refine ⟨8801668204867230966902467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46942230425958565156813157 8801668204867230966902467)
                  ·
                    refine ⟨13202502307300846450353701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8801668204867230966902467 13202502307300846450353701)
                    ·
                      refine ⟨2475469182618908709441319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13202502307300846450353701 2475469182618908709441319)
                      ·
                        rfl

theorem cell23_4820959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_4820959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820959 prefixEnd_4820959 := by exact prefixLift 4820959
  have htrace : WordTrace (prefixWord ++ tailWord_4820959) baseStart_4820959 baseEnd_4820959 := by
    simpa [prefixWord, tailWord_4820959, baseEnd_4820959] using wordTrace_append hprefix tailTrace_4820959
  have hstable : (prefixWord ++ tailWord_4820959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820959).length < 2 ^ (prefixWord ++ tailWord_4820959).sum := by decide
  have hdescent : baseEnd_4820959 < baseStart_4820959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4820972 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_4820972 : Nat := 118140960795 + 4820972 * 2 ^ 59
def prefixEnd_4820972 : Nat := 4983230072969 + 3 ^ 40 * 4820972 * 2
def baseEnd_4820972 : Nat := 2475475857867417158578759

theorem tailTrace_4820972 : CollatzResearch.WordTrace tailWord_4820972 prefixEnd_4820972 2475475857867417158578759 := by
  unfold tailWord_4820972
  simp only [CollatzResearch.WordTrace]
  refine ⟨87917647145224637655976585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117223529526966183541302113 87917647145224637655976585)
  ·
    refine ⟨65938235358918478241982439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87917647145224637655976585 65938235358918478241982439)
    ·
      refine ⟨98907353038377717362973659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65938235358918478241982439 98907353038377717362973659)
      ·
        refine ⟨148361029557566576044460489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98907353038377717362973659 148361029557566576044460489)
        ·
          refine ⟨111270772168174932033345367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148361029557566576044460489 111270772168174932033345367)
          ·
            refine ⟨166906158252262398050018051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111270772168174932033345367 166906158252262398050018051)
            ·
              refine ⟨250359237378393597075027077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166906158252262398050018051 250359237378393597075027077)
              ·
                refine ⟨46942357008448799451567577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250359237378393597075027077 46942357008448799451567577)
                ·
                  refine ⟨35206767756336599588675683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46942357008448799451567577 35206767756336599588675683)
                  ·
                    refine ⟨52810151634504899383013525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35206767756336599588675683 52810151634504899383013525)
                    ·
                      refine ⟨2475475857867417158578759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52810151634504899383013525 2475475857867417158578759)
                      ·
                        rfl

theorem cell23_4820972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_4820972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4820972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4820972 prefixEnd_4820972 := by exact prefixLift 4820972
  have htrace : WordTrace (prefixWord ++ tailWord_4820972) baseStart_4820972 baseEnd_4820972 := by
    simpa [prefixWord, tailWord_4820972, baseEnd_4820972] using wordTrace_append hprefix tailTrace_4820972
  have hstable : (prefixWord ++ tailWord_4820972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4820972).length < 2 ^ (prefixWord ++ tailWord_4820972).sum := by decide
  have hdescent : baseEnd_4820972 < baseStart_4820972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4820972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821020 : List Nat := [2, 2, 3, 1, 3, 1, 4, 2, 1, 4]
def baseStart_4821020 : Nat := 118140960795 + 4821020 * 2 ^ 59
def prefixEnd_4821020 : Nat := 4983230072969 + 3 ^ 40 * 4821020 * 2
def baseEnd_4821020 : Nat := 825166834979610990259513

theorem tailTrace_4821020 : CollatzResearch.WordTrace tailWord_4821020 prefixEnd_4821020 825166834979610990259513 := by
  unfold tailWord_4821020
  simp only [CollatzResearch.WordTrace]
  refine ⟨87918522497137689754850257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117224696662850253006467009 87918522497137689754850257)
  ·
    refine ⟨65938891872853267316137693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87918522497137689754850257 65938891872853267316137693)
    ·
      refine ⟨24727084452319975243551635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65938891872853267316137693 24727084452319975243551635)
      ·
        refine ⟨37090626678479962865327453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24727084452319975243551635 37090626678479962865327453)
        ·
          refine ⟨13908985004429986074497795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37090626678479962865327453 13908985004429986074497795)
          ·
            refine ⟨20863477506644979111746693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13908985004429986074497795 20863477506644979111746693)
            ·
              refine ⟨3911902032495933583452505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20863477506644979111746693 3911902032495933583452505)
              ·
                refine ⟨2933926524371950187589379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3911902032495933583452505 2933926524371950187589379)
                ·
                  refine ⟨4400889786557925281384069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933926524371950187589379 4400889786557925281384069)
                  ·
                    refine ⟨825166834979610990259513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4400889786557925281384069 825166834979610990259513)
                    ·
                      rfl

theorem cell23_4821020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_4821020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821020 prefixEnd_4821020 := by exact prefixLift 4821020
  have htrace : WordTrace (prefixWord ++ tailWord_4821020) baseStart_4821020 baseEnd_4821020 := by
    simpa [prefixWord, tailWord_4821020, baseEnd_4821020] using wordTrace_append hprefix tailTrace_4821020
  have hstable : (prefixWord ++ tailWord_4821020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821020).length < 2 ^ (prefixWord ++ tailWord_4821020).sum := by decide
  have hdescent : baseEnd_4821020 < baseStart_4821020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821029 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 3, 5]
def baseStart_4821029 : Nat := 118140960795 + 4821029 * 2 ^ 59
def prefixEnd_4821029 : Nat := 4983230072969 + 3 ^ 40 * 4821029 * 2
def baseEnd_4821029 : Nat := 825168375421574478521999

theorem tailTrace_4821029 : CollatzResearch.WordTrace tailWord_4821029 prefixEnd_4821029 825168375421574478521999 := by
  unfold tailWord_4821029
  simp only [CollatzResearch.WordTrace]
  refine ⟨175837373251242774046778141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117224915500828516031185427 175837373251242774046778141)
  ·
    refine ⟨65939014969216040267541803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175837373251242774046778141 65939014969216040267541803)
    ·
      refine ⟨98908522453824060401312705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65939014969216040267541803 98908522453824060401312705)
      ·
        refine ⟨74181391840368045300984529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98908522453824060401312705 74181391840368045300984529)
        ·
          refine ⟨55636043880276033975738397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74181391840368045300984529 55636043880276033975738397)
          ·
            refine ⟨20863516455103512740901899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55636043880276033975738397 20863516455103512740901899)
            ·
              refine ⟨31295274682655269111352849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20863516455103512740901899 31295274682655269111352849)
              ·
                refine ⟨23471456011991451833514637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31295274682655269111352849 23471456011991451833514637)
                ·
                  refine ⟨8801796004496794437567989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23471456011991451833514637 8801796004496794437567989)
                  ·
                    refine ⟨825168375421574478521999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8801796004496794437567989 825168375421574478521999)
                    ·
                      rfl

theorem cell23_4821029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_4821029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821029 prefixEnd_4821029 := by exact prefixLift 4821029
  have htrace : WordTrace (prefixWord ++ tailWord_4821029) baseStart_4821029 baseEnd_4821029 := by
    simpa [prefixWord, tailWord_4821029, baseEnd_4821029] using wordTrace_append hprefix tailTrace_4821029
  have hstable : (prefixWord ++ tailWord_4821029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821029).length < 2 ^ (prefixWord ++ tailWord_4821029).sum := by decide
  have hdescent : baseEnd_4821029 < baseStart_4821029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821046 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_4821046 : Nat := 118140960795 + 4821046 * 2 ^ 59
def prefixEnd_4821046 : Nat := 4983230072969 + 3 ^ 40 * 4821046 * 2
def baseEnd_4821046 : Nat := 825171285145283289684473

theorem tailTrace_4821046 : CollatzResearch.WordTrace tailWord_4821046 prefixEnd_4821046 825171285145283289684473 := by
  unfold tailWord_4821046
  simp only [CollatzResearch.WordTrace]
  refine ⟨10989874580761324121884187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117225328861454123966764661 10989874580761324121884187)
  ·
    refine ⟨16484811871141986182826281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10989874580761324121884187 16484811871141986182826281)
    ·
      refine ⟨12363608903356489637119711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16484811871141986182826281 12363608903356489637119711)
      ·
        refine ⟨18545413355034734455679567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12363608903356489637119711 18545413355034734455679567)
        ·
          refine ⟨27818120032552101683519351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18545413355034734455679567 27818120032552101683519351)
          ·
            refine ⟨41727180048828152525279027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27818120032552101683519351 41727180048828152525279027)
            ·
              refine ⟨62590770073242228787918541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41727180048828152525279027 62590770073242228787918541)
              ·
                refine ⟨23471538777465835795469453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62590770073242228787918541 23471538777465835795469453)
                ·
                  refine ⟨8801827041549688423301045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23471538777465835795469453 8801827041549688423301045)
                  ·
                    refine ⟨825171285145283289684473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8801827041549688423301045 825171285145283289684473)
                    ·
                      rfl

theorem cell23_4821046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_4821046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821046 prefixEnd_4821046 := by exact prefixLift 4821046
  have htrace : WordTrace (prefixWord ++ tailWord_4821046) baseStart_4821046 baseEnd_4821046 := by
    simpa [prefixWord, tailWord_4821046, baseEnd_4821046] using wordTrace_append hprefix tailTrace_4821046
  have hstable : (prefixWord ++ tailWord_4821046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821046).length < 2 ^ (prefixWord ++ tailWord_4821046).sum := by decide
  have hdescent : baseEnd_4821046 < baseStart_4821046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821079 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_4821079 : Nat := 118140960795 + 4821079 * 2 ^ 59
def prefixEnd_4821079 : Nat := 4983230072969 + 3 ^ 40 * 4821079 * 2
def baseEnd_4821079 : Nat := 2475530800297448239940767

theorem tailTrace_4821079 : CollatzResearch.WordTrace tailWord_4821079 prefixEnd_4821079 2475530800297448239940767 := by
  unfold tailWord_4821079
  simp only [CollatzResearch.WordTrace]
  refine ⟨175839196901061632586098291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117226131267374421724065527 175839196901061632586098291)
  ·
    refine ⟨263758795351592448879147437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175839196901061632586098291 263758795351592448879147437)
    ·
      refine ⟨98909548256847168329680289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263758795351592448879147437 98909548256847168329680289)
      ·
        refine ⟨74182161192635376247260217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98909548256847168329680289 74182161192635376247260217)
        ·
          refine ⟨55636620894476532185445163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74182161192635376247260217 55636620894476532185445163)
          ·
            refine ⟨83454931341714798278167745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55636620894476532185445163 83454931341714798278167745)
            ·
              refine ⟨62591198506286098708625809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83454931341714798278167745 62591198506286098708625809)
              ·
                refine ⟨46943398879714574031469357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62591198506286098708625809 46943398879714574031469357)
                ·
                  refine ⟨17603774579892965261801009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46943398879714574031469357 17603774579892965261801009)
                  ·
                    refine ⟨13202830934919723946350757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17603774579892965261801009 13202830934919723946350757)
                    ·
                      refine ⟨2475530800297448239940767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13202830934919723946350757 2475530800297448239940767)
                      ·
                        rfl

theorem cell23_4821079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_4821079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821079 prefixEnd_4821079 := by exact prefixLift 4821079
  have htrace : WordTrace (prefixWord ++ tailWord_4821079) baseStart_4821079 baseEnd_4821079 := by
    simpa [prefixWord, tailWord_4821079, baseEnd_4821079] using wordTrace_append hprefix tailTrace_4821079
  have hstable : (prefixWord ++ tailWord_4821079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821079).length < 2 ^ (prefixWord ++ tailWord_4821079).sum := by decide
  have hdescent : baseEnd_4821079 < baseStart_4821079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821103 : List Nat := [1, 1, 2, 1, 3, 5, 2, 2, 1, 2, 3]
def baseStart_4821103 : Nat := 118140960795 + 4821103 * 2 ^ 59
def prefixEnd_4821103 : Nat := 4983230072969 + 3 ^ 40 * 4821103 * 2
def baseEnd_4821103 : Nat := 2475543123833156146040657

theorem tailTrace_4821103 : CollatzResearch.WordTrace tailWord_4821103 prefixEnd_4821103 2475543123833156146040657 := by
  unfold tailWord_4821103
  simp only [CollatzResearch.WordTrace]
  refine ⟨175840072252974684684971963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117226714835316456456647975 175840072252974684684971963)
  ·
    refine ⟨263760108379462027027457945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175840072252974684684971963 263760108379462027027457945)
    ·
      refine ⟨197820081284596520270593459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263760108379462027027457945 197820081284596520270593459)
      ·
        refine ⟨296730121926894780405890189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197820081284596520270593459 296730121926894780405890189)
        ·
          refine ⟨111273795722585542652208821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296730121926894780405890189 111273795722585542652208821)
          ·
            refine ⟨10431918348992394623644577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111273795722585542652208821 10431918348992394623644577)
            ·
              refine ⟨7823938761744295967733433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10431918348992394623644577 7823938761744295967733433)
              ·
                refine ⟨5867954071308221975800075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7823938761744295967733433 5867954071308221975800075)
                ·
                  refine ⟨8801931106962332963700113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5867954071308221975800075 8801931106962332963700113)
                  ·
                    refine ⟨6601448330221749722775085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8801931106962332963700113 6601448330221749722775085)
                    ·
                      refine ⟨2475543123833156146040657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6601448330221749722775085 2475543123833156146040657)
                      ·
                        rfl

theorem cell23_4821103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 2, 3].length) (baseStart_4821103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821103 prefixEnd_4821103 := by exact prefixLift 4821103
  have htrace : WordTrace (prefixWord ++ tailWord_4821103) baseStart_4821103 baseEnd_4821103 := by
    simpa [prefixWord, tailWord_4821103, baseEnd_4821103] using wordTrace_append hprefix tailTrace_4821103
  have hstable : (prefixWord ++ tailWord_4821103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821103).length < 2 ^ (prefixWord ++ tailWord_4821103).sum := by decide
  have hdescent : baseEnd_4821103 < baseStart_4821103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821106 : List Nat := [3, 2, 1, 2, 2, 2, 4, 7]
def baseStart_4821106 : Nat := 118140960795 + 4821106 * 2 ^ 59
def prefixEnd_4821106 : Nat := 4983230072969 + 3 ^ 40 * 4821106 * 2
def baseEnd_4821106 : Nat := 91686839417597023492709

theorem tailTrace_4821106 : CollatzResearch.WordTrace tailWord_4821106 prefixEnd_4821106 91686839417597023492709 := by
  unfold tailWord_4821106
  simp only [CollatzResearch.WordTrace]
  refine ⟨43960045417990954049332793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117226787781309210798220781 43960045417990954049332793)
  ·
    refine ⟨32970034063493215536999595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43960045417990954049332793 32970034063493215536999595)
    ·
      refine ⟨49455051095239823305499393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32970034063493215536999595 49455051095239823305499393)
      ·
        refine ⟨37091288321429867479124545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49455051095239823305499393 37091288321429867479124545)
        ·
          refine ⟨27818466241072400609343409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37091288321429867479124545 27818466241072400609343409)
          ·
            refine ⟨20863849680804300457007557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27818466241072400609343409 20863849680804300457007557)
            ·
              refine ⟨3911971815150806335688917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20863849680804300457007557 3911971815150806335688917)
              ·
                refine ⟨91686839417597023492709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3911971815150806335688917 91686839417597023492709)
                ·
                  rfl

theorem cell23_4821106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 7].length) (baseStart_4821106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821106 prefixEnd_4821106 := by exact prefixLift 4821106
  have htrace : WordTrace (prefixWord ++ tailWord_4821106) baseStart_4821106 baseEnd_4821106 := by
    simpa [prefixWord, tailWord_4821106, baseEnd_4821106] using wordTrace_append hprefix tailTrace_4821106
  have hstable : (prefixWord ++ tailWord_4821106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821106).length < 2 ^ (prefixWord ++ tailWord_4821106).sum := by decide
  have hdescent : baseEnd_4821106 < baseStart_4821106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821117 : List Nat := [1, 4, 1, 1, 3, 2, 3, 3, 1, 2, 2]
def baseStart_4821117 : Nat := 118140960795 + 4821117 * 2 ^ 59
def prefixEnd_4821117 : Nat := 4983230072969 + 3 ^ 40 * 4821117 * 2
def baseEnd_4821117 : Nat := 2475550312562319091265593

theorem tailTrace_4821117 : CollatzResearch.WordTrace tailWord_4821117 prefixEnd_4821117 2475550312562319091265593 := by
  unfold tailWord_4821117
  simp only [CollatzResearch.WordTrace]
  refine ⟨175840582874923965075981605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117227055249949310050654403 175840582874923965075981605)
  ·
    refine ⟨32970109289048243451746551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175840582874923965075981605 32970109289048243451746551)
    ·
      refine ⟨49455163933572365177619827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32970109289048243451746551 49455163933572365177619827)
      ·
        refine ⟨74182745900358547766429741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49455163933572365177619827 74182745900358547766429741)
        ·
          refine ⟨27818529712634455412411153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74182745900358547766429741 27818529712634455412411153)
          ·
            refine ⟨20863897284475841559308365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27818529712634455412411153 20863897284475841559308365)
            ·
              refine ⟨7823961481678440584740637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20863897284475841559308365 7823961481678440584740637)
              ·
                refine ⟨2933985555629415219277739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7823961481678440584740637 2933985555629415219277739)
                ·
                  refine ⟨4400978333444122828916609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933985555629415219277739 4400978333444122828916609)
                  ·
                    refine ⟨3300733750083092121687457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4400978333444122828916609 3300733750083092121687457)
                    ·
                      refine ⟨2475550312562319091265593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3300733750083092121687457 2475550312562319091265593)
                      ·
                        rfl

theorem cell23_4821117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_4821117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821117 prefixEnd_4821117 := by exact prefixLift 4821117
  have htrace : WordTrace (prefixWord ++ tailWord_4821117) baseStart_4821117 baseEnd_4821117 := by
    simpa [prefixWord, tailWord_4821117, baseEnd_4821117] using wordTrace_append hprefix tailTrace_4821117
  have hstable : (prefixWord ++ tailWord_4821117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821117).length < 2 ^ (prefixWord ++ tailWord_4821117).sum := by decide
  have hdescent : baseEnd_4821117 < baseStart_4821117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821129 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 5]
def baseStart_4821129 : Nat := 118140960795 + 4821129 * 2 ^ 59
def prefixEnd_4821129 : Nat := 4983230072969 + 3 ^ 40 * 4821129 * 2
def baseEnd_4821129 : Nat := 2475556474330173044315537

theorem tailTrace_4821129 : CollatzResearch.WordTrace tailWord_4821129 prefixEnd_4821129 2475556474330173044315537 := by
  unfold tailWord_4821129
  simp only [CollatzResearch.WordTrace]
  refine ⟨175841020550880491125418441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117227347033920327416945627 175841020550880491125418441)
  ·
    refine ⟨131880765413160368344063831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175841020550880491125418441 131880765413160368344063831)
    ·
      refine ⟨197821148119740552516095747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131880765413160368344063831 197821148119740552516095747)
      ·
        refine ⟨296731722179610828774143621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197821148119740552516095747 296731722179610828774143621)
        ·
          refine ⟨55637197908677030395151929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296731722179610828774143621 55637197908677030395151929)
          ·
            refine ⟨41727898431507772796363947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55637197908677030395151929 41727898431507772796363947)
            ·
              refine ⟨62591847647261659194545921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41727898431507772796363947 62591847647261659194545921)
              ·
                refine ⟨46943885735446244395909441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62591847647261659194545921 46943885735446244395909441)
                ·
                  refine ⟨35207914301584683296932081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46943885735446244395909441 35207914301584683296932081)
                  ·
                    refine ⟨26405935726188512472699061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35207914301584683296932081 26405935726188512472699061)
                    ·
                      refine ⟨2475556474330173044315537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26405935726188512472699061 2475556474330173044315537)
                      ·
                        rfl

theorem cell23_4821129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_4821129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821129 prefixEnd_4821129 := by exact prefixLift 4821129
  have htrace : WordTrace (prefixWord ++ tailWord_4821129) baseStart_4821129 baseEnd_4821129 := by
    simpa [prefixWord, tailWord_4821129, baseEnd_4821129] using wordTrace_append hprefix tailTrace_4821129
  have hstable : (prefixWord ++ tailWord_4821129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821129).length < 2 ^ (prefixWord ++ tailWord_4821129).sum := by decide
  have hdescent : baseEnd_4821129 < baseStart_4821129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821134 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2]
def baseStart_4821134 : Nat := 118140960795 + 4821134 * 2 ^ 59
def prefixEnd_4821134 : Nat := 4983230072969 + 3 ^ 40 * 4821134 * 2
def baseEnd_4821134 : Nat := 2475559041733445524753015

theorem tailTrace_4821134 : CollatzResearch.WordTrace tailWord_4821134 prefixEnd_4821134 2475559041733445524753015 := by
  unfold tailWord_4821134
  simp only [CollatzResearch.WordTrace]
  refine ⟨21980150364482797122418807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117227468610574917986233637 21980150364482797122418807)
  ·
    refine ⟨32970225546724195683628211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21980150364482797122418807 32970225546724195683628211)
    ·
      refine ⟨49455338320086293525442317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32970225546724195683628211 49455338320086293525442317)
      ·
        refine ⟨18545751870032360072040869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49455338320086293525442317 18545751870032360072040869)
        ·
          refine ⟨3477328475631067513507663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18545751870032360072040869 3477328475631067513507663)
          ·
            refine ⟨5215992713446601270261495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477328475631067513507663 5215992713446601270261495)
            ·
              refine ⟨7823989070169901905392243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5215992713446601270261495 7823989070169901905392243)
              ·
                refine ⟨11735983605254852858088365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7823989070169901905392243 11735983605254852858088365)
                ·
                  refine ⟨4400993851970569821783137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11735983605254852858088365 4400993851970569821783137)
                  ·
                    refine ⟨3300745388977927366337353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4400993851970569821783137 3300745388977927366337353)
                    ·
                      refine ⟨2475559041733445524753015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3300745388977927366337353 2475559041733445524753015)
                      ·
                        rfl

theorem cell23_4821134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_4821134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821134 prefixEnd_4821134 := by exact prefixLift 4821134
  have htrace : WordTrace (prefixWord ++ tailWord_4821134) baseStart_4821134 baseEnd_4821134 := by
    simpa [prefixWord, tailWord_4821134, baseEnd_4821134] using wordTrace_append hprefix tailTrace_4821134
  have hstable : (prefixWord ++ tailWord_4821134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821134).length < 2 ^ (prefixWord ++ tailWord_4821134).sum := by decide
  have hdescent : baseEnd_4821134 < baseStart_4821134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821139 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 4]
def baseStart_4821139 : Nat := 118140960795 + 4821139 * 2 ^ 59
def prefixEnd_4821139 : Nat := 4983230072969 + 3 ^ 40 * 4821139 * 2
def baseEnd_4821139 : Nat := 2475561609136718005190491

theorem tailTrace_4821139 : CollatzResearch.WordTrace tailWord_4821139 prefixEnd_4821139 2475561609136718005190491 := by
  unfold tailWord_4821139
  simp only [CollatzResearch.WordTrace]
  refine ⟨175841385280844262833282471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117227590187229508555521647 175841385280844262833282471)
  ·
    refine ⟨263762077921266394249923707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175841385280844262833282471 263762077921266394249923707)
    ·
      refine ⟨395643116881899591374885561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263762077921266394249923707 395643116881899591374885561)
      ·
        refine ⟨296732337661424693531164171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395643116881899591374885561 296732337661424693531164171)
        ·
          refine ⟨445098506492137040296746257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296732337661424693531164171 445098506492137040296746257)
          ·
            refine ⟨333823879869102780222559693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 445098506492137040296746257 333823879869102780222559693)
            ·
              refine ⟨125183954950913542583459885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 333823879869102780222559693 125183954950913542583459885)
              ·
                refine ⟨46943983106592578468797457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125183954950913542583459885 46943983106592578468797457)
                ·
                  refine ⟨35207987329944433851598093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46943983106592578468797457 35207987329944433851598093)
                  ·
                    refine ⟨13202995248729162694349285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35207987329944433851598093 13202995248729162694349285)
                    ·
                      refine ⟨2475561609136718005190491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13202995248729162694349285 2475561609136718005190491)
                      ·
                        rfl

theorem cell23_4821139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_4821139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821139 prefixEnd_4821139 := by exact prefixLift 4821139
  have htrace : WordTrace (prefixWord ++ tailWord_4821139) baseStart_4821139 baseEnd_4821139 := by
    simpa [prefixWord, tailWord_4821139, baseEnd_4821139] using wordTrace_append hprefix tailTrace_4821139
  have hstable : (prefixWord ++ tailWord_4821139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821139).length < 2 ^ (prefixWord ++ tailWord_4821139).sum := by decide
  have hdescent : baseEnd_4821139 < baseStart_4821139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821189 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_4821189 : Nat := 118140960795 + 4821189 * 2 ^ 59
def prefixEnd_4821189 : Nat := 4983230072969 + 3 ^ 40 * 4821189 * 2
def baseEnd_4821189 : Nat := 2475587283169442809565261

theorem tailTrace_4821189 : CollatzResearch.WordTrace tailWord_4821189 prefixEnd_4821189 2475587283169442809565261 := by
  unfold tailWord_4821189
  simp only [CollatzResearch.WordTrace]
  refine ⟨175843208930663121372602621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117228805953775414248401747 175843208930663121372602621)
  ·
    refine ⟨65941203348998670514725983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175843208930663121372602621 65941203348998670514725983)
    ·
      refine ⟨98911805023498005772088975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65941203348998670514725983 98911805023498005772088975)
      ·
        refine ⟨148367707535247008658133463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98911805023498005772088975 148367707535247008658133463)
        ·
          refine ⟨222551561302870512987200195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148367707535247008658133463 222551561302870512987200195)
          ·
            refine ⟨333827341954305769480800293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222551561302870512987200195 333827341954305769480800293)
            ·
              refine ⟨62592626616432331777650055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 333827341954305769480800293 62592626616432331777650055)
              ·
                refine ⟨93888939924648497666475083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62592626616432331777650055 93888939924648497666475083)
                ·
                  refine ⟨140833409886972746499712625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93888939924648497666475083 140833409886972746499712625)
                  ·
                    refine ⟨105625057415229559874784469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 140833409886972746499712625 105625057415229559874784469)
                    ·
                      refine ⟨2475587283169442809565261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105625057415229559874784469 2475587283169442809565261)
                      ·
                        rfl

theorem cell23_4821189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_4821189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821189 prefixEnd_4821189 := by exact prefixLift 4821189
  have htrace : WordTrace (prefixWord ++ tailWord_4821189) baseStart_4821189 baseEnd_4821189 := by
    simpa [prefixWord, tailWord_4821189, baseEnd_4821189] using wordTrace_append hprefix tailTrace_4821189
  have hstable : (prefixWord ++ tailWord_4821189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821189).length < 2 ^ (prefixWord ++ tailWord_4821189).sum := by decide
  have hdescent : baseEnd_4821189 < baseStart_4821189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821213 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 7]
def baseStart_4821213 : Nat := 118140960795 + 4821213 * 2 ^ 59
def prefixEnd_4821213 : Nat := 4983230072969 + 3 ^ 40 * 4821213 * 2
def baseEnd_4821213 : Nat := 275066622967238968407239

theorem tailTrace_4821213 : CollatzResearch.WordTrace tailWord_4821213 prefixEnd_4821213 275066622967238968407239 := by
  unfold tailWord_4821213
  simp only [CollatzResearch.WordTrace]
  refine ⟨175844084282576173471476293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117229389521717448980984195 175844084282576173471476293)
  ·
    refine ⟨32970765802983032525901805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175844084282576173471476293 32970765802983032525901805)
    ·
      refine ⟨12364037176118637197213177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32970765802983032525901805 12364037176118637197213177)
      ·
        refine ⟨9273027882088977897909883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12364037176118637197213177 9273027882088977897909883)
        ·
          refine ⟨13909541823133466846864825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9273027882088977897909883 13909541823133466846864825)
          ·
            refine ⟨10432156367350100135148619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13909541823133466846864825 10432156367350100135148619)
            ·
              refine ⟨15648234551025150202722929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10432156367350100135148619 15648234551025150202722929)
              ·
                refine ⟨11736175913268862652042197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15648234551025150202722929 11736175913268862652042197)
                ·
                  refine ⟨275066622967238968407239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11736175913268862652042197 275066622967238968407239)
                  ·
                    rfl

theorem cell23_4821213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_4821213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821213 prefixEnd_4821213 := by exact prefixLift 4821213
  have htrace : WordTrace (prefixWord ++ tailWord_4821213) baseStart_4821213 baseEnd_4821213 := by
    simpa [prefixWord, tailWord_4821213, baseEnd_4821213] using wordTrace_append hprefix tailTrace_4821213
  have hstable : (prefixWord ++ tailWord_4821213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821213).length < 2 ^ (prefixWord ++ tailWord_4821213).sum := by decide
  have hdescent : baseEnd_4821213 < baseStart_4821213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821226 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 1, 7]
def baseStart_4821226 : Nat := 118140960795 + 4821226 * 2 ^ 59
def prefixEnd_4821226 : Nat := 4983230072969 + 3 ^ 40 * 4821226 * 2
def baseEnd_4821226 : Nat := 825202093984553054934197

theorem tailTrace_4821226 : CollatzResearch.WordTrace tailWord_4821226 prefixEnd_4821226 825202093984553054934197 := by
  unfold tailWord_4821226
  simp only [CollatzResearch.WordTrace]
  refine ⟨43961139607882269172924883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117229705621019384461133021 43961139607882269172924883)
  ·
    refine ⟨65941709411823403759387325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43961139607882269172924883 65941709411823403759387325)
    ·
      refine ⟨24728141029433776409770247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65941709411823403759387325 24728141029433776409770247)
      ·
        refine ⟨37092211544150664614655371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24728141029433776409770247 37092211544150664614655371)
        ·
          refine ⟨55638317316225996921983057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37092211544150664614655371 55638317316225996921983057)
          ·
            refine ⟨41728737987169497691487293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55638317316225996921983057 41728737987169497691487293)
            ·
              refine ⟨15648276745188561634307735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41728737987169497691487293 15648276745188561634307735)
              ·
                refine ⟨23472415117782842451461603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15648276745188561634307735 23472415117782842451461603)
                ·
                  refine ⟨35208622676674263677192405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23472415117782842451461603 35208622676674263677192405)
                  ·
                    refine ⟨825202093984553054934197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35208622676674263677192405 825202093984553054934197)
                    ·
                      rfl

theorem cell23_4821226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_4821226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821226 prefixEnd_4821226 := by exact prefixLift 4821226
  have htrace : WordTrace (prefixWord ++ tailWord_4821226) baseStart_4821226 baseEnd_4821226 := by
    simpa [prefixWord, tailWord_4821226, baseEnd_4821226] using wordTrace_append hprefix tailTrace_4821226
  have hstable : (prefixWord ++ tailWord_4821226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821226).length < 2 ^ (prefixWord ++ tailWord_4821226).sum := by decide
  have hdescent : baseEnd_4821226 < baseStart_4821226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821276 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_4821276 : Nat := 118140960795 + 4821276 * 2 ^ 59
def prefixEnd_4821276 : Nat := 4983230072969 + 3 ^ 40 * 4821276 * 2
def baseEnd_4821276 : Nat := 2475631955986383969177361

theorem tailTrace_4821276 : CollatzResearch.WordTrace tailWord_4821276 prefixEnd_4821276 2475631955986383969177361 := by
  unfold tailWord_4821276
  simp only [CollatzResearch.WordTrace]
  refine ⟨87923191040673967615509841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117230921387565290154013121 87923191040673967615509841)
  ·
    refine ⟨65942393280505475711632381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87923191040673967615509841 65942393280505475711632381)
    ·
      refine ⟨24728397480189553391862143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65942393280505475711632381 24728397480189553391862143)
      ·
        refine ⟨37092596220284330087793215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24728397480189553391862143 37092596220284330087793215)
        ·
          refine ⟨55638894330426495131689823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37092596220284330087793215 55638894330426495131689823)
          ·
            refine ⟨83458341495639742697534735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55638894330426495131689823 83458341495639742697534735)
            ·
              refine ⟨125187512243459614046302103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83458341495639742697534735 125187512243459614046302103)
              ·
                refine ⟨187781268365189421069453155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125187512243459614046302103 187781268365189421069453155)
                ·
                  refine ⟨281671902547784131604179733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187781268365189421069453155 281671902547784131604179733)
                  ·
                    refine ⟨13203370431927381168945925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 281671902547784131604179733 13203370431927381168945925)
                    ·
                      refine ⟨2475631955986383969177361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13203370431927381168945925 2475631955986383969177361)
                      ·
                        rfl

theorem cell23_4821276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_4821276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821276 prefixEnd_4821276 := by exact prefixLift 4821276
  have htrace : WordTrace (prefixWord ++ tailWord_4821276) baseStart_4821276 baseEnd_4821276 := by
    simpa [prefixWord, tailWord_4821276, baseEnd_4821276] using wordTrace_append hprefix tailTrace_4821276
  have hstable : (prefixWord ++ tailWord_4821276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821276).length < 2 ^ (prefixWord ++ tailWord_4821276).sum := by decide
  have hdescent : baseEnd_4821276 < baseStart_4821276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821283 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 3]
def baseStart_4821283 : Nat := 118140960795 + 4821283 * 2 ^ 59
def prefixEnd_4821283 : Nat := 4983230072969 + 3 ^ 40 * 4821283 * 2
def baseEnd_4821283 : Nat := 2475635550350965441789829

theorem tailTrace_4821283 : CollatzResearch.WordTrace tailWord_4821283 prefixEnd_4821283 2475635550350965441789829 := by
  unfold tailWord_4821283
  simp only [CollatzResearch.WordTrace]
  refine ⟨175846637392322575426524503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117231091594881716951016335 175846637392322575426524503)
  ·
    refine ⟨263769956088483863139786755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175846637392322575426524503 263769956088483863139786755)
    ·
      refine ⟨395654934132725794709680133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263769956088483863139786755 395654934132725794709680133)
      ·
        refine ⟨74185300149886086508065025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 395654934132725794709680133 74185300149886086508065025)
        ·
          refine ⟨55638975112414564881048769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74185300149886086508065025 55638975112414564881048769)
          ·
            refine ⟨41729231334310923660786577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55638975112414564881048769 41729231334310923660786577)
            ·
              refine ⟨31296923500733192745589933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41729231334310923660786577 31296923500733192745589933)
              ·
                refine ⟨11736346312774947279596225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31296923500733192745589933 11736346312774947279596225)
                ·
                  refine ⟨8802259734581210459697169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11736346312774947279596225 8802259734581210459697169)
                  ·
                    refine ⟨6601694800935907844772877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8802259734581210459697169 6601694800935907844772877)
                    ·
                      refine ⟨2475635550350965441789829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6601694800935907844772877 2475635550350965441789829)
                      ·
                        rfl

theorem cell23_4821283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_4821283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821283 prefixEnd_4821283 := by exact prefixLift 4821283
  have htrace : WordTrace (prefixWord ++ tailWord_4821283) baseStart_4821283 baseEnd_4821283 := by
    simpa [prefixWord, tailWord_4821283, baseEnd_4821283] using wordTrace_append hprefix tailTrace_4821283
  have hstable : (prefixWord ++ tailWord_4821283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821283).length < 2 ^ (prefixWord ++ tailWord_4821283).sum := by decide
  have hdescent : baseEnd_4821283 < baseStart_4821283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821300 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_4821300 : Nat := 118140960795 + 4821300 * 2 ^ 59
def prefixEnd_4821300 : Nat := 4983230072969 + 3 ^ 40 * 4821300 * 2
def baseEnd_4821300 : Nat := 2475644279522091875277251

theorem tailTrace_4821300 : CollatzResearch.WordTrace tailWord_4821300 prefixEnd_4821300 2475644279522091875277251 := by
  unfold tailWord_4821300
  simp only [CollatzResearch.WordTrace]
  refine ⟨87923628716630493664946677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117231504955507324886595569 87923628716630493664946677)
  ·
    refine ⟨8242840192184108781088751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87923628716630493664946677 8242840192184108781088751)
    ·
      refine ⟨12364260288276163171633127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8242840192184108781088751 12364260288276163171633127)
      ·
        refine ⟨18546390432414244757449691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12364260288276163171633127 18546390432414244757449691)
        ·
          refine ⟨27819585648621367136174537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18546390432414244757449691 27819585648621367136174537)
          ·
            refine ⟨20864689236466025352130903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27819585648621367136174537 20864689236466025352130903)
            ·
              refine ⟨31297033854699038028196355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20864689236466025352130903 31297033854699038028196355)
              ·
                refine ⟨46945550782048557042294533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31297033854699038028196355 46945550782048557042294533)
                ·
                  refine ⟨8802290771634104445430225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46945550782048557042294533 8802290771634104445430225)
                  ·
                    refine ⟨6601718078725578334072669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8802290771634104445430225 6601718078725578334072669)
                    ·
                      refine ⟨2475644279522091875277251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6601718078725578334072669 2475644279522091875277251)
                      ·
                        rfl

theorem cell23_4821300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_4821300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821300 prefixEnd_4821300 := by exact prefixLift 4821300
  have htrace : WordTrace (prefixWord ++ tailWord_4821300) baseStart_4821300 baseEnd_4821300 := by
    simpa [prefixWord, tailWord_4821300, baseEnd_4821300] using wordTrace_append hprefix tailTrace_4821300
  have hstable : (prefixWord ++ tailWord_4821300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821300).length < 2 ^ (prefixWord ++ tailWord_4821300).sum := by decide
  have hdescent : baseEnd_4821300 < baseStart_4821300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821323 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 1, 5, 2]
def baseStart_4821323 : Nat := 118140960795 + 4821323 * 2 ^ 59
def prefixEnd_4821323 : Nat := 4983230072969 + 3 ^ 40 * 4821323 * 2
def baseEnd_4821323 : Nat := 2475656089577145285289645

theorem tailTrace_4821323 : CollatzResearch.WordTrace tailWord_4821323 prefixEnd_4821323 2475656089577145285289645 := by
  unfold tailWord_4821323
  simp only [CollatzResearch.WordTrace]
  refine ⟨175848096312177662257980623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117232064208118441505320415 175848096312177662257980623)
  ·
    refine ⟨263772144468266493386970935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175848096312177662257980623 263772144468266493386970935)
    ·
      refine ⟨395658216702399740080456403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263772144468266493386970935 395658216702399740080456403)
      ·
        refine ⟨593487325053599610120684605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395658216702399740080456403 593487325053599610120684605)
        ·
          refine ⟨222557746895099853795256727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 593487325053599610120684605 222557746895099853795256727)
          ·
            refine ⟨333836620342649780692885091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222557746895099853795256727 333836620342649780692885091)
            ·
              refine ⟨500754930513974671039327637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333836620342649780692885091 500754930513974671039327637)
              ·
                refine ⟨23472887367842562704968483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 500754930513974671039327637 23472887367842562704968483)
                ·
                  refine ⟨35209331051763844057452725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23472887367842562704968483 35209331051763844057452725)
                  ·
                    refine ⟨3300874786102860380386193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35209331051763844057452725 3300874786102860380386193)
                    ·
                      refine ⟨2475656089577145285289645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3300874786102860380386193 2475656089577145285289645)
                      ·
                        rfl

theorem cell23_4821323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 5, 2].length) (baseStart_4821323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821323 prefixEnd_4821323 := by exact prefixLift 4821323
  have htrace : WordTrace (prefixWord ++ tailWord_4821323) baseStart_4821323 baseEnd_4821323 := by
    simpa [prefixWord, tailWord_4821323, baseEnd_4821323] using wordTrace_append hprefix tailTrace_4821323
  have hstable : (prefixWord ++ tailWord_4821323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821323).length < 2 ^ (prefixWord ++ tailWord_4821323).sum := by decide
  have hdescent : baseEnd_4821323 < baseStart_4821323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821326 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_4821326 : Nat := 118140960795 + 4821326 * 2 ^ 59
def prefixEnd_4821326 : Nat := 4983230072969 + 3 ^ 40 * 4821326 * 2
def baseEnd_4821326 : Nat := 2475657630019108773552131

theorem tailTrace_4821326 : CollatzResearch.WordTrace tailWord_4821326 prefixEnd_4821326 2475657630019108773552131 := by
  unfold tailWord_4821326
  simp only [CollatzResearch.WordTrace]
  refine ⟨21981025716395849221292479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117232137154111195846893221 21981025716395849221292479)
  ·
    refine ⟨32971538574593773831938719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21981025716395849221292479 32971538574593773831938719)
    ·
      refine ⟨49457307861890660747908079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32971538574593773831938719 49457307861890660747908079)
      ·
        refine ⟨74185961792835991121862119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49457307861890660747908079 74185961792835991121862119)
        ·
          refine ⟨111278942689253986682793179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74185961792835991121862119 111278942689253986682793179)
          ·
            refine ⟨166918414033880980024189769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111278942689253986682793179 166918414033880980024189769)
            ·
              refine ⟨125188810525410735018142327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166918414033880980024189769 125188810525410735018142327)
              ·
                refine ⟨187783215788116102527213491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125188810525410735018142327 187783215788116102527213491)
                ·
                  refine ⟨281674823682174153790820237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187783215788116102527213491 281674823682174153790820237)
                  ·
                    refine ⟨105628058880815307671557589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 281674823682174153790820237 105628058880815307671557589)
                    ·
                      refine ⟨2475657630019108773552131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105628058880815307671557589 2475657630019108773552131)
                      ·
                        rfl

theorem cell23_4821326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_4821326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821326 prefixEnd_4821326 := by exact prefixLift 4821326
  have htrace : WordTrace (prefixWord ++ tailWord_4821326) baseStart_4821326 baseEnd_4821326 := by
    simpa [prefixWord, tailWord_4821326, baseEnd_4821326] using wordTrace_append hprefix tailTrace_4821326
  have hstable : (prefixWord ++ tailWord_4821326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821326).length < 2 ^ (prefixWord ++ tailWord_4821326).sum := by decide
  have hdescent : baseEnd_4821326 < baseStart_4821326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821330 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_4821330 : Nat := 118140960795 + 4821330 * 2 ^ 59
def prefixEnd_4821330 : Nat := 4983230072969 + 3 ^ 40 * 4821330 * 2
def baseEnd_4821330 : Nat := 2475659683941726757902113

theorem tailTrace_4821330 : CollatzResearch.WordTrace tailWord_4821330 prefixEnd_4821330 2475659683941726757902113 := by
  unfold tailWord_4821330
  simp only [CollatzResearch.WordTrace]
  refine ⟨43962087905788075613371361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117232234415434868302323629 43962087905788075613371361)
  ·
    refine ⟨32971565929341056710028521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43962087905788075613371361 32971565929341056710028521)
    ·
      refine ⟨24728674447005792532521391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32971565929341056710028521 24728674447005792532521391)
      ·
        refine ⟨37093011670508688798782087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24728674447005792532521391 37093011670508688798782087)
        ·
          refine ⟨55639517505763033198173131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37093011670508688798782087 55639517505763033198173131)
          ·
            refine ⟨83459276258644549797259697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55639517505763033198173131 83459276258644549797259697)
            ·
              refine ⟨62594457193983412347944773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83459276258644549797259697 62594457193983412347944773)
              ·
                refine ⟨11736460723871889815239645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62594457193983412347944773 11736460723871889815239645)
                ·
                  refine ⟨4401172771451958680714867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11736460723871889815239645 4401172771451958680714867)
                  ·
                    refine ⟨6601759157177938021072301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4401172771451958680714867 6601759157177938021072301)
                    ·
                      refine ⟨2475659683941726757902113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6601759157177938021072301 2475659683941726757902113)
                      ·
                        rfl

theorem cell23_4821330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_4821330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821330 prefixEnd_4821330 := by exact prefixLift 4821330
  have htrace : WordTrace (prefixWord ++ tailWord_4821330) baseStart_4821330 baseEnd_4821330 := by
    simpa [prefixWord, tailWord_4821330, baseEnd_4821330] using wordTrace_append hprefix tailTrace_4821330
  have hstable : (prefixWord ++ tailWord_4821330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821330).length < 2 ^ (prefixWord ++ tailWord_4821330).sum := by decide
  have hdescent : baseEnd_4821330 < baseStart_4821330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821347 : List Nat := [1, 1, 1, 5, 2, 1, 2, 5, 1, 1, 3]
def baseStart_4821347 : Nat := 118140960795 + 4821347 * 2 ^ 59
def prefixEnd_4821347 : Nat := 4983230072969 + 3 ^ 40 * 4821347 * 2
def baseEnd_4821347 : Nat := 2475668413112853191389535

theorem tailTrace_4821347 : CollatzResearch.WordTrace tailWord_4821347 prefixEnd_4821347 2475668413112853191389535 := by
  unfold tailWord_4821347
  simp only [CollatzResearch.WordTrace]
  refine ⟨175848971664090714356854295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117232647776060476237902863 175848971664090714356854295)
  ·
    refine ⟨263773457496136071535281443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175848971664090714356854295 263773457496136071535281443)
    ·
      refine ⟨395660186244204107302922165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263773457496136071535281443 395660186244204107302922165)
      ·
        refine ⟨37093142460394135059648953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 395660186244204107302922165 37093142460394135059648953)
        ·
          refine ⟨27819856845295601294736715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37093142460394135059648953 27819856845295601294736715)
          ·
            refine ⟨41729785267943401942105073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27819856845295601294736715 41729785267943401942105073)
            ·
              refine ⟨31297338950957551456578805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41729785267943401942105073 31297338950957551456578805)
              ·
                refine ⟨2934125526652270449054263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31297338950957551456578805 2934125526652270449054263)
                ·
                  refine ⟨4401188289978405673581395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2934125526652270449054263 4401188289978405673581395)
                  ·
                    refine ⟨6601782434967608510372093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4401188289978405673581395 6601782434967608510372093)
                    ·
                      refine ⟨2475668413112853191389535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6601782434967608510372093 2475668413112853191389535)
                      ·
                        rfl

theorem cell23_4821347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_4821347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821347 prefixEnd_4821347 := by exact prefixLift 4821347
  have htrace : WordTrace (prefixWord ++ tailWord_4821347) baseStart_4821347 baseEnd_4821347 := by
    simpa [prefixWord, tailWord_4821347, baseEnd_4821347] using wordTrace_append hprefix tailTrace_4821347
  have hstable : (prefixWord ++ tailWord_4821347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821347).length < 2 ^ (prefixWord ++ tailWord_4821347).sum := by decide
  have hdescent : baseEnd_4821347 < baseStart_4821347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821380 : List Nat := [2, 3, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_4821380 : Nat := 118140960795 + 4821380 * 2 ^ 59
def prefixEnd_4821380 : Nat := 4983230072969 + 3 ^ 40 * 4821380 * 2
def baseEnd_4821380 : Nat := 825228452658150520758961

theorem tailTrace_4821380 : CollatzResearch.WordTrace tailWord_4821380 prefixEnd_4821380 825228452658150520758961 := by
  unfold tailWord_4821380
  simp only [CollatzResearch.WordTrace]
  refine ⟨87925087636485580496402797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117233450181980773995203729 87925087636485580496402797)
  ·
    refine ⟨32971907863682092686151049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87925087636485580496402797 32971907863682092686151049)
    ·
      refine ⟨24728930897761569514613287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32971907863682092686151049 24728930897761569514613287)
      ·
        refine ⟨37093396346642354271919931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24728930897761569514613287 37093396346642354271919931)
        ·
          refine ⟨55640094519963531407879897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37093396346642354271919931 55640094519963531407879897)
          ·
            refine ⟨41730070889972648555909923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55640094519963531407879897 41730070889972648555909923)
            ·
              refine ⟨62595106334958972833864885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41730070889972648555909923 62595106334958972833864885)
              ·
                refine ⟨5868291218902403703174833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62595106334958972833864885 5868291218902403703174833)
                ·
                  refine ⟨4401218414176802777381125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5868291218902403703174833 4401218414176802777381125)
                  ·
                    refine ⟨825228452658150520758961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4401218414176802777381125 825228452658150520758961)
                    ·
                      rfl

theorem cell23_4821380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_4821380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821380 prefixEnd_4821380 := by exact prefixLift 4821380
  have htrace : WordTrace (prefixWord ++ tailWord_4821380) baseStart_4821380 baseEnd_4821380 := by
    simpa [prefixWord, tailWord_4821380, baseEnd_4821380] using wordTrace_append hprefix tailTrace_4821380
  have hstable : (prefixWord ++ tailWord_4821380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821380).length < 2 ^ (prefixWord ++ tailWord_4821380).sum := by decide
  have hdescent : baseEnd_4821380 < baseStart_4821380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821387 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 3, 2, 2]
def baseStart_4821387 : Nat := 118140960795 + 4821387 * 2 ^ 59
def prefixEnd_4821387 : Nat := 4983230072969 + 3 ^ 40 * 4821387 * 2
def baseEnd_4821387 : Nat := 2475688952339033034889351

theorem tailTrace_4821387 : CollatzResearch.WordTrace tailWord_4821387 prefixEnd_4821387 2475688952339033034889351 := by
  unfold tailWord_4821387
  simp only [CollatzResearch.WordTrace]
  refine ⟨175850430583945801188310415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117233620389297200792206943 175850430583945801188310415)
  ·
    refine ⟨263775645875918701782465623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175850430583945801188310415 263775645875918701782465623)
    ·
      refine ⟨395663468813878052673698435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263775645875918701782465623 395663468813878052673698435)
      ·
        refine ⟨593495203220817079010547653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395663468813878052673698435 593495203220817079010547653)
        ·
          refine ⟨111280350603903202314477685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 593495203220817079010547653 111280350603903202314477685)
          ·
            refine ⟨10432532869115925216982283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111280350603903202314477685 10432532869115925216982283)
            ·
              refine ⟨15648799303673887825473425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10432532869115925216982283 15648799303673887825473425)
              ·
                refine ⟨11736599477755415869105069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15648799303673887825473425 11736599477755415869105069)
                ·
                  refine ⟨4401224804158280950914401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11736599477755415869105069 4401224804158280950914401)
                  ·
                    refine ⟨3300918603118710713185801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4401224804158280950914401 3300918603118710713185801)
                    ·
                      refine ⟨2475688952339033034889351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3300918603118710713185801 2475688952339033034889351)
                      ·
                        rfl

theorem cell23_4821387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 2, 2].length) (baseStart_4821387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821387 prefixEnd_4821387 := by exact prefixLift 4821387
  have htrace : WordTrace (prefixWord ++ tailWord_4821387) baseStart_4821387 baseEnd_4821387 := by
    simpa [prefixWord, tailWord_4821387, baseEnd_4821387] using wordTrace_append hprefix tailTrace_4821387
  have hstable : (prefixWord ++ tailWord_4821387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821387).length < 2 ^ (prefixWord ++ tailWord_4821387).sum := by decide
  have hdescent : baseEnd_4821387 < baseStart_4821387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821400 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_4821400 : Nat := 118140960795 + 4821400 * 2 ^ 59
def prefixEnd_4821400 : Nat := 4983230072969 + 3 ^ 40 * 4821400 * 2
def baseEnd_4821400 : Nat := 2475695627587541484026791

theorem tailTrace_4821400 : CollatzResearch.WordTrace tailWord_4821400 prefixEnd_4821400 2475695627587541484026791 := by
  unfold tailWord_4821400
  simp only [CollatzResearch.WordTrace]
  refine ⟨87925452366449352204266827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117233936488599136272355769 87925452366449352204266827)
  ·
    refine ⟨131888178549674028306400241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87925452366449352204266827 131888178549674028306400241)
    ·
      refine ⟨98916133912255521229800181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131888178549674028306400241 98916133912255521229800181)
      ·
        refine ⟨9273387554273955115293767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98916133912255521229800181 9273387554273955115293767)
        ·
          refine ⟨13910081331410932672940651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9273387554273955115293767 13910081331410932672940651)
          ·
            refine ⟨20865121997116399009410977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13910081331410932672940651 20865121997116399009410977)
            ·
              refine ⟨15648841497837299257058233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20865121997116399009410977 15648841497837299257058233)
              ·
                refine ⟨11736631123377974442793675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15648841497837299257058233 11736631123377974442793675)
                ·
                  refine ⟨17604946685066961664190513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11736631123377974442793675 17604946685066961664190513)
                  ·
                    refine ⟨13203710013800221248142885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17604946685066961664190513 13203710013800221248142885)
                    ·
                      refine ⟨2475695627587541484026791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13203710013800221248142885 2475695627587541484026791)
                      ·
                        rfl

theorem cell23_4821400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_4821400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821400 prefixEnd_4821400 := by exact prefixLift 4821400
  have htrace : WordTrace (prefixWord ++ tailWord_4821400) baseStart_4821400 baseEnd_4821400 := by
    simpa [prefixWord, tailWord_4821400, baseEnd_4821400] using wordTrace_append hprefix tailTrace_4821400
  have hstable : (prefixWord ++ tailWord_4821400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821400).length < 2 ^ (prefixWord ++ tailWord_4821400).sum := by decide
  have hdescent : baseEnd_4821400 < baseStart_4821400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821421 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_4821421 : Nat := 118140960795 + 4821421 * 2 ^ 59
def prefixEnd_4821421 : Nat := 4983230072969 + 3 ^ 40 * 4821421 * 2
def baseEnd_4821421 : Nat := 2475706410681285901864195

theorem tailTrace_4821421 : CollatzResearch.WordTrace tailWord_4821421 prefixEnd_4821421 2475706410681285901864195 := by
  unfold tailWord_4821421
  simp only [CollatzResearch.WordTrace]
  refine ⟨175851670665822624995048117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117234447110548416663365411 175851670665822624995048117)
  ·
    refine ⟨16486094124920871093285761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175851670665822624995048117 16486094124920871093285761)
    ·
      refine ⟨12364570593690653319964321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16486094124920871093285761 12364570593690653319964321)
      ·
        refine ⟨9273427945267989989973241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12364570593690653319964321 9273427945267989989973241)
        ·
          refine ⟨6955070958950992492479931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9273427945267989989973241 6955070958950992492479931)
          ·
            refine ⟨10432606438426488738719897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6955070958950992492479931 10432606438426488738719897)
            ·
              refine ⟨7824454828819866554039923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10432606438426488738719897 7824454828819866554039923)
              ·
                refine ⟨11736682243229799831059885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7824454828819866554039923 11736682243229799831059885)
                ·
                  refine ⟨4401255841211174936647457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11736682243229799831059885 4401255841211174936647457)
                  ·
                    refine ⟨3300941880908381202485593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4401255841211174936647457 3300941880908381202485593)
                    ·
                      refine ⟨2475706410681285901864195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3300941880908381202485593 2475706410681285901864195)
                      ·
                        rfl

theorem cell23_4821421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_4821421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821421 prefixEnd_4821421 := by exact prefixLift 4821421
  have htrace : WordTrace (prefixWord ++ tailWord_4821421) baseStart_4821421 baseEnd_4821421 := by
    simpa [prefixWord, tailWord_4821421, baseEnd_4821421] using wordTrace_append hprefix tailTrace_4821421
  have hstable : (prefixWord ++ tailWord_4821421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821421).length < 2 ^ (prefixWord ++ tailWord_4821421).sum := by decide
  have hdescent : baseEnd_4821421 < baseStart_4821421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821437 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_4821437 : Nat := 118140960795 + 4821437 * 2 ^ 59
def prefixEnd_4821437 : Nat := 4983230072969 + 3 ^ 40 * 4821437 * 2
def baseEnd_4821437 : Nat := 2475714626371757839264121

theorem tailTrace_4821437 : CollatzResearch.WordTrace tailWord_4821437 prefixEnd_4821437 2475714626371757839264121 := by
  unfold tailWord_4821437
  simp only [CollatzResearch.WordTrace]
  refine ⟨175852254233764659727630565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117234836155843106485087043 175852254233764659727630565)
  ·
    refine ⟨32972297668830873698930731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175852254233764659727630565 32972297668830873698930731)
    ·
      refine ⟨49458446503246310548396097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32972297668830873698930731 49458446503246310548396097)
      ·
        refine ⟨37093834877434732911297073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49458446503246310548396097 37093834877434732911297073)
        ·
          refine ⟨27820376158076049683472805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37093834877434732911297073 27820376158076049683472805)
          ·
            refine ⟨5216320529639259315651151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27820376158076049683472805 5216320529639259315651151)
            ·
              refine ⟨7824480794458888973476727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5216320529639259315651151 7824480794458888973476727)
              ·
                refine ⟨11736721191688333460215091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7824480794458888973476727 11736721191688333460215091)
                ·
                  refine ⟨17605081787532500190322637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11736721191688333460215091 17605081787532500190322637)
                  ·
                    refine ⟨6601905670324687571370989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17605081787532500190322637 6601905670324687571370989)
                    ·
                      refine ⟨2475714626371757839264121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6601905670324687571370989 2475714626371757839264121)
                      ·
                        rfl

theorem cell23_4821437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_4821437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821437 prefixEnd_4821437 := by exact prefixLift 4821437
  have htrace : WordTrace (prefixWord ++ tailWord_4821437) baseStart_4821437 baseEnd_4821437 := by
    simpa [prefixWord, tailWord_4821437, baseEnd_4821437] using wordTrace_append hprefix tailTrace_4821437
  have hstable : (prefixWord ++ tailWord_4821437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821437).length < 2 ^ (prefixWord ++ tailWord_4821437).sum := by decide
  have hdescent : baseEnd_4821437 < baseStart_4821437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821444 : List Nat := [2, 3, 3, 2, 3, 1, 2, 7]
def baseStart_4821444 : Nat := 118140960795 + 4821444 * 2 ^ 59
def prefixEnd_4821444 : Nat := 4983230072969 + 3 ^ 40 * 4821444 * 2
def baseEnd_4821444 : Nat := 91693267434679233773207

theorem tailTrace_4821444 : CollatzResearch.WordTrace tailWord_4821444 prefixEnd_4821444 91693267434679233773207 := by
  unfold tailWord_4821444
  simp only [CollatzResearch.WordTrace]
  refine ⟨87926254772369649961567693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117235006363159533282090257 87926254772369649961567693)
  ·
    refine ⟨32972345539638618735587885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87926254772369649961567693 32972345539638618735587885)
    ·
      refine ⟨12364629577364482025845457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32972345539638618735587885 12364629577364482025845457)
      ·
        refine ⟨9273472183023361519384093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12364629577364482025845457 9273472183023361519384093)
        ·
          refine ⟨3477552068633760569769035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9273472183023361519384093 3477552068633760569769035)
          ·
            refine ⟨5216328102950640854653553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477552068633760569769035 5216328102950640854653553)
            ·
              refine ⟨3912246077212980640990165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5216328102950640854653553 3912246077212980640990165)
              ·
                refine ⟨91693267434679233773207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3912246077212980640990165 91693267434679233773207)
                ·
                  rfl

theorem cell23_4821444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 7].length) (baseStart_4821444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821444 prefixEnd_4821444 := by exact prefixLift 4821444
  have htrace : WordTrace (prefixWord ++ tailWord_4821444) baseStart_4821444 baseEnd_4821444 := by
    simpa [prefixWord, tailWord_4821444, baseEnd_4821444] using wordTrace_append hprefix tailTrace_4821444
  have hstable : (prefixWord ++ tailWord_4821444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821444).length < 2 ^ (prefixWord ++ tailWord_4821444).sum := by decide
  have hdescent : baseEnd_4821444 < baseStart_4821444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821447 : List Nat := [1, 1, 4, 1, 1, 4, 1, 4, 1, 3, 2]
def baseStart_4821447 : Nat := 118140960795 + 4821447 * 2 ^ 59
def prefixEnd_4821447 : Nat := 4983230072969 + 3 ^ 40 * 4821447 * 2
def baseEnd_4821447 : Nat := 2475719761178302800139075

theorem tailTrace_4821447 : CollatzResearch.WordTrace tailWord_4821447 prefixEnd_4821447 2475719761178302800139075 := by
  unfold tailWord_4821447
  simp only [CollatzResearch.WordTrace]
  refine ⟨175852618963728431435494595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117235079309152287623663063 175852618963728431435494595)
  ·
    refine ⟨263778928445592647153241893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175852618963728431435494595 263778928445592647153241893)
    ·
      refine ⟨49458549083548621341232855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 263778928445592647153241893 49458549083548621341232855)
      ·
        refine ⟨74187823625322932011849283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49458549083548621341232855 74187823625322932011849283)
        ·
          refine ⟨111281735437984398017773925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74187823625322932011849283 111281735437984398017773925)
          ·
            refine ⟨20865325394622074628332611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111281735437984398017773925 20865325394622074628332611)
            ·
              refine ⟨31297988091933111942498917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20865325394622074628332611 31297988091933111942498917)
              ·
                refine ⟨5868372767237458489218547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31297988091933111942498917 5868372767237458489218547)
                ·
                  refine ⟨8802559150856187733827821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5868372767237458489218547 8802559150856187733827821)
                  ·
                    refine ⟨3300959681571070400185433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8802559150856187733827821 3300959681571070400185433)
                    ·
                      refine ⟨2475719761178302800139075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3300959681571070400185433 2475719761178302800139075)
                      ·
                        rfl

theorem cell23_4821447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_4821447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821447 prefixEnd_4821447 := by exact prefixLift 4821447
  have htrace : WordTrace (prefixWord ++ tailWord_4821447) baseStart_4821447 baseEnd_4821447 := by
    simpa [prefixWord, tailWord_4821447, baseEnd_4821447] using wordTrace_append hprefix tailTrace_4821447
  have hstable : (prefixWord ++ tailWord_4821447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821447).length < 2 ^ (prefixWord ++ tailWord_4821447).sum := by decide
  have hdescent : baseEnd_4821447 < baseStart_4821447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821463 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 3]
def baseStart_4821463 : Nat := 118140960795 + 4821463 * 2 ^ 59
def prefixEnd_4821463 : Nat := 4983230072969 + 3 ^ 40 * 4821463 * 2
def baseEnd_4821463 : Nat := 2475727976868774737539001

theorem tailTrace_4821463 : CollatzResearch.WordTrace tailWord_4821463 prefixEnd_4821463 2475727976868774737539001 := by
  unfold tailWord_4821463
  simp only [CollatzResearch.WordTrace]
  refine ⟨175853202531670466168077043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117235468354446977445384695 175853202531670466168077043)
  ·
    refine ⟨263779803797505699252115565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175853202531670466168077043 263779803797505699252115565)
    ·
      refine ⟨98917426424064637219543337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263779803797505699252115565 98917426424064637219543337)
      ·
        refine ⟨74188069818048477914657503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98917426424064637219543337 74188069818048477914657503)
        ·
          refine ⟨111282104727072716871986255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74188069818048477914657503 111282104727072716871986255)
          ·
            refine ⟨166923157090609075307979383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111282104727072716871986255 166923157090609075307979383)
            ·
              refine ⟨250384735635913612961969075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166923157090609075307979383 250384735635913612961969075)
              ·
                refine ⟨375577103453870419442953613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250384735635913612961969075 375577103453870419442953613)
                ·
                  refine ⟨140841413795201407291107605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375577103453870419442953613 140841413795201407291107605)
                  ·
                    refine ⟨6601941271650065966770669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 140841413795201407291107605 6601941271650065966770669)
                    ·
                      refine ⟨2475727976868774737539001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6601941271650065966770669 2475727976868774737539001)
                      ·
                        rfl

theorem cell23_4821463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_4821463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821463 prefixEnd_4821463 := by exact prefixLift 4821463
  have htrace : WordTrace (prefixWord ++ tailWord_4821463) baseStart_4821463 baseEnd_4821463 := by
    simpa [prefixWord, tailWord_4821463, baseEnd_4821463] using wordTrace_append hprefix tailTrace_4821463
  have hstable : (prefixWord ++ tailWord_4821463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821463).length < 2 ^ (prefixWord ++ tailWord_4821463).sum := by decide
  have hdescent : baseEnd_4821463 < baseStart_4821463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821523 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 5]
def baseStart_4821523 : Nat := 118140960795 + 4821523 * 2 ^ 59
def prefixEnd_4821523 : Nat := 4983230072969 + 3 ^ 40 * 4821523 * 2
def baseEnd_4821523 : Nat := 2475758785708044502788725

theorem tailTrace_4821523 : CollatzResearch.WordTrace tailWord_4821523 prefixEnd_4821523 2475758785708044502788725 := by
  unfold tailWord_4821523
  simp only [CollatzResearch.WordTrace]
  refine ⟨175855390911453096415261223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117236927274302064276840815 175855390911453096415261223)
  ·
    refine ⟨263783086367179644622891835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175855390911453096415261223 263783086367179644622891835)
    ·
      refine ⟨395674629550769466934337753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263783086367179644622891835 395674629550769466934337753)
      ·
        refine ⟨296755972163077100200753315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395674629550769466934337753 296755972163077100200753315)
        ·
          refine ⟨445133958244615650301129973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296755972163077100200753315 445133958244615650301129973)
          ·
            refine ⟨41731308585432717215730935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 445133958244615650301129973 41731308585432717215730935)
            ·
              refine ⟨62596962878149075823596403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41731308585432717215730935 62596962878149075823596403)
              ·
                refine ⟨93895444317223613735394605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62596962878149075823596403 93895444317223613735394605)
                ·
                  refine ⟨35210791618958855150772977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93895444317223613735394605 35210791618958855150772977)
                  ·
                    refine ⟨26408093714219141363079733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35210791618958855150772977 26408093714219141363079733)
                    ·
                      refine ⟨2475758785708044502788725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26408093714219141363079733 2475758785708044502788725)
                      ·
                        rfl

theorem cell23_4821523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_4821523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821523 prefixEnd_4821523 := by exact prefixLift 4821523
  have htrace : WordTrace (prefixWord ++ tailWord_4821523) baseStart_4821523 baseEnd_4821523 := by
    simpa [prefixWord, tailWord_4821523, baseEnd_4821523] using wordTrace_append hprefix tailTrace_4821523
  have hstable : (prefixWord ++ tailWord_4821523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821523).length < 2 ^ (prefixWord ++ tailWord_4821523).sum := by decide
  have hdescent : baseEnd_4821523 < baseStart_4821523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821530 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 2, 5]
def baseStart_4821530 : Nat := 118140960795 + 4821530 * 2 ^ 59
def prefixEnd_4821530 : Nat := 4983230072969 + 3 ^ 40 * 4821530 * 2
def baseEnd_4821530 : Nat := 825254126690875325133731

theorem tailTrace_4821530 : CollatzResearch.WordTrace tailWord_4821530 prefixEnd_4821530 825254126690875325133731 := by
  unfold tailWord_4821530
  simp only [CollatzResearch.WordTrace]
  refine ⟨43963911555606934152691511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117237097481618491073844029 43963911555606934152691511)
  ·
    refine ⟨65945867333410401229037267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43963911555606934152691511 65945867333410401229037267)
    ·
      refine ⟨98918801000115601843555901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65945867333410401229037267 98918801000115601843555901)
      ·
        refine ⟨37094550375043350691333463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98918801000115601843555901 37094550375043350691333463)
        ·
          refine ⟨55641825562565026037000195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37094550375043350691333463 55641825562565026037000195)
          ·
            refine ⟨83462738343847539055500293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55641825562565026037000195 83462738343847539055500293)
            ·
              refine ⟨15649263439471413572906305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83462738343847539055500293 15649263439471413572906305)
              ·
                refine ⟨11736947579603560179679729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15649263439471413572906305 11736947579603560179679729)
                ·
                  refine ⟨8802710684702670134759797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11736947579603560179679729 8802710684702670134759797)
                  ·
                    refine ⟨825254126690875325133731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8802710684702670134759797 825254126690875325133731)
                    ·
                      rfl

theorem cell23_4821530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_4821530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821530 prefixEnd_4821530 := by exact prefixLift 4821530
  have htrace : WordTrace (prefixWord ++ tailWord_4821530) baseStart_4821530 baseEnd_4821530 := by
    simpa [prefixWord, tailWord_4821530, baseEnd_4821530] using wordTrace_append hprefix tailTrace_4821530
  have hstable : (prefixWord ++ tailWord_4821530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821530).length < 2 ^ (prefixWord ++ tailWord_4821530).sum := by decide
  have hdescent : baseEnd_4821530 < baseStart_4821530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821610 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_4821610 : Nat := 118140960795 + 4821610 * 2 ^ 59
def prefixEnd_4821610 : Nat := 4983230072969 + 3 ^ 40 * 4821610 * 2
def baseEnd_4821610 : Nat := 2475803458524985662400825

theorem tailTrace_4821610 : CollatzResearch.WordTrace tailWord_4821610 prefixEnd_4821610 2475803458524985662400825 := by
  unfold tailWord_4821610
  simp only [CollatzResearch.WordTrace]
  refine ⟨43964641015534477568419571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117239042708091940182452189 43964641015534477568419571)
  ·
    refine ⟨65946961523301716352629357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43964641015534477568419571 65946961523301716352629357)
    ·
      refine ⟨24730110571238143632236009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65946961523301716352629357 24730110571238143632236009)
      ·
        refine ⟨18547582928428607724177007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24730110571238143632236009 18547582928428607724177007)
        ·
          refine ⟨27821374392642911586265511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18547582928428607724177007 27821374392642911586265511)
          ·
            refine ⟨41732061588964367379398267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27821374392642911586265511 41732061588964367379398267)
            ·
              refine ⟨62598092383446551069097401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41732061588964367379398267 62598092383446551069097401)
              ·
                refine ⟨46948569287584913301823051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62598092383446551069097401 46948569287584913301823051)
                ·
                  refine ⟨70422853931377369952734577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46948569287584913301823051 70422853931377369952734577)
                  ·
                    refine ⟨52817140448533027464550933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70422853931377369952734577 52817140448533027464550933)
                    ·
                      refine ⟨2475803458524985662400825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52817140448533027464550933 2475803458524985662400825)
                      ·
                        rfl

theorem cell23_4821610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_4821610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821610 prefixEnd_4821610 := by exact prefixLift 4821610
  have htrace : WordTrace (prefixWord ++ tailWord_4821610) baseStart_4821610 baseEnd_4821610 := by
    simpa [prefixWord, tailWord_4821610, baseEnd_4821610] using wordTrace_append hprefix tailTrace_4821610
  have hstable : (prefixWord ++ tailWord_4821610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821610).length < 2 ^ (prefixWord ++ tailWord_4821610).sum := by decide
  have hdescent : baseEnd_4821610 < baseStart_4821610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821637 : List Nat := [1, 3, 1, 1, 4, 2, 2, 3, 1, 5]
def baseStart_4821637 : Nat := 118140960795 + 4821637 * 2 ^ 59
def prefixEnd_4821637 : Nat := 4983230072969 + 3 ^ 40 * 4821637 * 2
def baseEnd_4821637 : Nat := 825272440834219018921067

theorem tailTrace_4821637 : CollatzResearch.WordTrace tailWord_4821637 prefixEnd_4821637 825272440834219018921067 := by
  unfold tailWord_4821637
  simp only [CollatzResearch.WordTrace]
  refine ⟨175859548833040093884911165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117239699222026729256607443 175859548833040093884911165)
  ·
    refine ⟨65947330812390035206841687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175859548833040093884911165 65947330812390035206841687)
    ·
      refine ⟨98920996218585052810262531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65947330812390035206841687 98920996218585052810262531)
      ·
        refine ⟨148381494327877579215393797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98920996218585052810262531 148381494327877579215393797)
        ·
          refine ⟨27821530186477046102886337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148381494327877579215393797 27821530186477046102886337)
          ·
            refine ⟨20866147639857784577164753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27821530186477046102886337 20866147639857784577164753)
            ·
              refine ⟨15649610729893338432873565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20866147639857784577164753 15649610729893338432873565)
              ·
                refine ⟨5868604023710001912327587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15649610729893338432873565 5868604023710001912327587)
                ·
                  refine ⟨8802906035565002868491381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5868604023710001912327587 8802906035565002868491381)
                  ·
                    refine ⟨825272440834219018921067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8802906035565002868491381 825272440834219018921067)
                    ·
                      rfl

theorem cell23_4821637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_4821637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821637 prefixEnd_4821637 := by exact prefixLift 4821637
  have htrace : WordTrace (prefixWord ++ tailWord_4821637) baseStart_4821637 baseEnd_4821637 := by
    simpa [prefixWord, tailWord_4821637, baseEnd_4821637] using wordTrace_append hprefix tailTrace_4821637
  have hstable : (prefixWord ++ tailWord_4821637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821637).length < 2 ^ (prefixWord ++ tailWord_4821637).sum := by decide
  have hdescent : baseEnd_4821637 < baseStart_4821637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821658 : List Nat := [3, 1, 1, 6, 2, 1, 2, 1, 6]
def baseStart_4821658 : Nat := 118140960795 + 4821658 * 2 ^ 59
def prefixEnd_4821658 : Nat := 4983230072969 + 3 ^ 40 * 4821658 * 2
def baseEnd_4821658 : Nat := 275092011732933497177845

theorem tailTrace_4821658 : CollatzResearch.WordTrace tailWord_4821658 prefixEnd_4821658 275092011732933497177845 := by
  unfold tailWord_4821658
  simp only [CollatzResearch.WordTrace]
  refine ⟨43965078691491003617856407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117240209843976009647617085 43965078691491003617856407)
  ·
    refine ⟨65947618037236505426784611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43965078691491003617856407 65947618037236505426784611)
    ·
      refine ⟨98921427055854758140176917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65947618037236505426784611 98921427055854758140176917)
      ·
        refine ⟨4636941893243191787820793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98921427055854758140176917 4636941893243191787820793)
        ·
          refine ⟨3477706419932393840865595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4636941893243191787820793 3477706419932393840865595)
          ·
            refine ⟨5216559629898590761298393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477706419932393840865595 5216559629898590761298393)
            ·
              refine ⟨3912419722423943070973795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5216559629898590761298393 3912419722423943070973795)
              ·
                refine ⟨5868629583635914606460693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3912419722423943070973795 5868629583635914606460693)
                ·
                  refine ⟨275092011732933497177845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5868629583635914606460693 275092011732933497177845)
                  ·
                    rfl

theorem cell23_4821658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 6].length) (baseStart_4821658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821658 prefixEnd_4821658 := by exact prefixLift 4821658
  have htrace : WordTrace (prefixWord ++ tailWord_4821658) baseStart_4821658 baseEnd_4821658 := by
    simpa [prefixWord, tailWord_4821658, baseEnd_4821658] using wordTrace_append hprefix tailTrace_4821658
  have hstable : (prefixWord ++ tailWord_4821658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821658).length < 2 ^ (prefixWord ++ tailWord_4821658).sum := by decide
  have hdescent : baseEnd_4821658 < baseStart_4821658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821678 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_4821678 : Nat := 118140960795 + 4821678 * 2 ^ 59
def prefixEnd_4821678 : Nat := 4983230072969 + 3 ^ 40 * 4821678 * 2
def baseEnd_4821678 : Nat := 2475838375209491396350513

theorem tailTrace_4821678 : CollatzResearch.WordTrace tailWord_4821678 prefixEnd_4821678 2475838375209491396350513 := by
  unfold tailWord_4821678
  simp only [CollatzResearch.WordTrace]
  refine ⟨21982630528236444735894211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117240696150594371924769125 21982630528236444735894211)
  ·
    refine ⟨32973945792354667103841317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21982630528236444735894211 32973945792354667103841317)
    ·
      refine ⟨6182614836066500081970247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32973945792354667103841317 6182614836066500081970247)
      ·
        refine ⟨9273922254099750122955371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6182614836066500081970247 9273922254099750122955371)
        ·
          refine ⟨13910883381149625184433057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9273922254099750122955371 13910883381149625184433057)
          ·
            refine ⟨10433162535862218888324793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13910883381149625184433057 10433162535862218888324793)
            ·
              refine ⟨7824871901896664166243595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10433162535862218888324793 7824871901896664166243595)
              ·
                refine ⟨11737307852844996249365393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7824871901896664166243595 11737307852844996249365393)
                ·
                  refine ⟨8802980889633747187024045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11737307852844996249365393 8802980889633747187024045)
                  ·
                    refine ⟨3301117833612655195134017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8802980889633747187024045 3301117833612655195134017)
                    ·
                      refine ⟨2475838375209491396350513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3301117833612655195134017 2475838375209491396350513)
                      ·
                        rfl

theorem cell23_4821678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_4821678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821678 prefixEnd_4821678 := by exact prefixLift 4821678
  have htrace : WordTrace (prefixWord ++ tailWord_4821678) baseStart_4821678 baseEnd_4821678 := by
    simpa [prefixWord, tailWord_4821678, baseEnd_4821678] using wordTrace_append hprefix tailTrace_4821678
  have hstable : (prefixWord ++ tailWord_4821678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821678).length < 2 ^ (prefixWord ++ tailWord_4821678).sum := by decide
  have hdescent : baseEnd_4821678 < baseStart_4821678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821697 : List Nat := [1, 2, 6, 2, 12]
def baseStart_4821697 : Nat := 118140960795 + 4821697 * 2 ^ 59
def prefixEnd_4821697 : Nat := 4983230072969 + 3 ^ 40 * 4821697 * 2
def baseEnd_4821697 : Nat := 3396225145873699344325

theorem tailTrace_4821697 : CollatzResearch.WordTrace tailWord_4821697 prefixEnd_4821697 3396225145873699344325 := by
  unfold tailWord_4821697
  simp only [CollatzResearch.WordTrace]
  refine ⟨175861737212822724132095345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117241158141881816088063563 175861737212822724132095345)
  ·
    refine ⟨131896302909617043099071509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175861737212822724132095345 131896302909617043099071509)
    ·
      refine ⟨6182639198888298895268977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 131896302909617043099071509 6182639198888298895268977)
      ·
        refine ⟨4636979399166224171451733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6182639198888298895268977 4636979399166224171451733)
        ·
          refine ⟨3396225145873699344325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4636979399166224171451733 3396225145873699344325)
          ·
            rfl

theorem cell23_4821697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 12].length) (baseStart_4821697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821697 prefixEnd_4821697 := by exact prefixLift 4821697
  have htrace : WordTrace (prefixWord ++ tailWord_4821697) baseStart_4821697 baseEnd_4821697 := by
    simpa [prefixWord, tailWord_4821697, baseEnd_4821697] using wordTrace_append hprefix tailTrace_4821697
  have hstable : (prefixWord ++ tailWord_4821697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821697).length < 2 ^ (prefixWord ++ tailWord_4821697).sum := by decide
  have hdescent : baseEnd_4821697 < baseStart_4821697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
