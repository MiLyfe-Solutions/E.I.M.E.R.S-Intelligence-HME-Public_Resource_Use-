import V185TrunkScan23Chunk0641

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3795951 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 1, 6]
def baseStart_3795951 : Nat := 118140960795 + 3795951 * 2 ^ 59
def prefixEnd_3795951 : Nat := 4983230072969 + 3 ^ 40 * 3795951 * 2
def baseEnd_3795951 : Nat := 649715801305061019318415

theorem tailTrace_3795951 : CollatzResearch.WordTrace tailWord_3795951 prefixEnd_3795951 649715801305061019318415 := by
  unfold tailWord_3795951
  simp only [CollatzResearch.WordTrace]
  refine ⟨138449707070925298662363707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92299804713950199108242471 138449707070925298662363707)
  ·
    refine ⟨207674560606387947993545561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138449707070925298662363707 207674560606387947993545561)
    ·
      refine ⟨155755920454790960995159171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207674560606387947993545561 155755920454790960995159171)
      ·
        refine ⟨233633880682186441492738757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155755920454790960995159171 233633880682186441492738757)
        ·
          refine ⟨43806352627909957779888517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233633880682186441492738757 43806352627909957779888517)
          ·
            refine ⟨8213691117733117083729097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43806352627909957779888517 8213691117733117083729097)
            ·
              refine ⟨6160268338299837812796823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8213691117733117083729097 6160268338299837812796823)
              ·
                refine ⟨9240402507449756719195235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6160268338299837812796823 9240402507449756719195235)
                ·
                  refine ⟨13860603761174635078792853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9240402507449756719195235 13860603761174635078792853)
                  ·
                    refine ⟨649715801305061019318415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13860603761174635078792853 649715801305061019318415)
                    ·
                      rfl

theorem cell23_3795951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 6].length) (baseStart_3795951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795951 prefixEnd_3795951 := by exact prefixLift 3795951
  have htrace : WordTrace (prefixWord ++ tailWord_3795951) baseStart_3795951 baseEnd_3795951 := by
    simpa [prefixWord, tailWord_3795951, baseEnd_3795951] using wordTrace_append hprefix tailTrace_3795951
  have hstable : (prefixWord ++ tailWord_3795951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795951).length < 2 ^ (prefixWord ++ tailWord_3795951).sum := by decide
  have hdescent : baseEnd_3795951 < baseStart_3795951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795956 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3795956 : Nat := 118140960795 + 3795956 * 2 ^ 59
def prefixEnd_3795956 : Nat := 4983230072969 + 3 ^ 40 * 3795956 * 2
def baseEnd_3795956 : Nat := 1949149971318455538392723

theorem tailTrace_3795956 : CollatzResearch.WordTrace tailWord_3795956 prefixEnd_3795956 1949149971318455538392723 := by
  unfold tailWord_3795956
  simp only [CollatzResearch.WordTrace]
  refine ⟨69224944717953592258147861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92299926290604789677530481 69224944717953592258147861)
  ·
    refine ⟨3244919283654074637100681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69224944717953592258147861 3244919283654074637100681)
    ·
      refine ⟨2433689462740555977825511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3244919283654074637100681 2433689462740555977825511)
      ·
        refine ⟨3650534194110833966738267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433689462740555977825511 3650534194110833966738267)
        ·
          refine ⟨5475801291166250950107401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3650534194110833966738267 5475801291166250950107401)
          ·
            refine ⟨4106850968374688212580551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5475801291166250950107401 4106850968374688212580551)
            ·
              refine ⟨6160276452562032318870827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4106850968374688212580551 6160276452562032318870827)
              ·
                refine ⟨9240414678843048478306241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6160276452562032318870827 9240414678843048478306241)
                ·
                  refine ⟨6930311009132286358729681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9240414678843048478306241 6930311009132286358729681)
                  ·
                    refine ⟨5197733256849214769047261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6930311009132286358729681 5197733256849214769047261)
                    ·
                      refine ⟨1949149971318455538392723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5197733256849214769047261 1949149971318455538392723)
                      ·
                        rfl

theorem cell23_3795956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3795956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795956 prefixEnd_3795956 := by exact prefixLift 3795956
  have htrace : WordTrace (prefixWord ++ tailWord_3795956) baseStart_3795956 baseEnd_3795956 := by
    simpa [prefixWord, tailWord_3795956, baseEnd_3795956] using wordTrace_append hprefix tailTrace_3795956
  have hstable : (prefixWord ++ tailWord_3795956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795956).length < 2 ^ (prefixWord ++ tailWord_3795956).sum := by decide
  have hdescent : baseEnd_3795956 < baseStart_3795956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795958 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_3795958 : Nat := 118140960795 + 3795958 * 2 ^ 59
def prefixEnd_3795958 : Nat := 4983230072969 + 3 ^ 40 * 3795958 * 2
def baseEnd_3795958 : Nat := 1949150998279764530567713

theorem tailTrace_3795958 : CollatzResearch.WordTrace tailWord_3795958 prefixEnd_3795958 1949150998279764530567713 := by
  unfold tailWord_3795958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653122648868746178616783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92299974921266625905245685 8653122648868746178616783)
  ·
    refine ⟨12979683973303119267925175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8653122648868746178616783 12979683973303119267925175)
    ·
      refine ⟨19469525959954678901887763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12979683973303119267925175 19469525959954678901887763)
      ·
        refine ⟨29204288939932018352831645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19469525959954678901887763 29204288939932018352831645)
        ·
          refine ⟨10951608352474506882311867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29204288939932018352831645 10951608352474506882311867)
          ·
            refine ⟨16427412528711760323467801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10951608352474506882311867 16427412528711760323467801)
            ·
              refine ⟨12320559396533820242600851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16427412528711760323467801 12320559396533820242600851)
              ·
                refine ⟨18480839094800730363901277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12320559396533820242600851 18480839094800730363901277)
                ·
                  refine ⟨6930314660550273886462979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18480839094800730363901277 6930314660550273886462979)
                  ·
                    refine ⟨10395471990825410829694469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6930314660550273886462979 10395471990825410829694469)
                    ·
                      refine ⟨1949150998279764530567713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10395471990825410829694469 1949150998279764530567713)
                      ·
                        rfl

theorem cell23_3795958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_3795958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795958 prefixEnd_3795958 := by exact prefixLift 3795958
  have htrace : WordTrace (prefixWord ++ tailWord_3795958) baseStart_3795958 baseEnd_3795958 := by
    simpa [prefixWord, tailWord_3795958, baseEnd_3795958] using wordTrace_append hprefix tailTrace_3795958
  have hstable : (prefixWord ++ tailWord_3795958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795958).length < 2 ^ (prefixWord ++ tailWord_3795958).sum := by decide
  have hdescent : baseEnd_3795958 < baseStart_3795958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795961 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 3, 2, 3]
def baseStart_3795961 : Nat := 118140960795 + 3795961 * 2 ^ 59
def prefixEnd_3795961 : Nat := 4983230072969 + 3 ^ 40 * 3795961 * 2
def baseEnd_3795961 : Nat := 1949152538721728018830199

theorem tailTrace_3795961 : CollatzResearch.WordTrace tailWord_3795961 prefixEnd_3795961 1949152538721728018830199 := by
  unfold tailWord_3795961
  simp only [CollatzResearch.WordTrace]
  refine ⟨138450071800889070370227737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92300047867259380246818491 138450071800889070370227737)
  ·
    refine ⟨103837553850666802777670803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138450071800889070370227737 103837553850666802777670803)
    ·
      refine ⟨155756330776000204166506205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103837553850666802777670803 155756330776000204166506205)
      ·
        refine ⟨58408624041000076562439827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155756330776000204166506205 58408624041000076562439827)
        ·
          refine ⟨87612936061500114843659741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58408624041000076562439827 87612936061500114843659741)
          ·
            refine ⟨32854851023062543066372403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87612936061500114843659741 32854851023062543066372403)
            ·
              refine ⟨49282276534593814599558605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32854851023062543066372403 49282276534593814599558605)
              ·
                refine ⟨18480853700472680474834477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49282276534593814599558605 18480853700472680474834477)
                ·
                  refine ⟨6930320137677255178062929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18480853700472680474834477 6930320137677255178062929)
                  ·
                    refine ⟨5197740103257941383547197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6930320137677255178062929 5197740103257941383547197)
                    ·
                      refine ⟨1949152538721728018830199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5197740103257941383547197 1949152538721728018830199)
                      ·
                        rfl

theorem cell23_3795961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_3795961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795961 prefixEnd_3795961 := by exact prefixLift 3795961
  have htrace : WordTrace (prefixWord ++ tailWord_3795961) baseStart_3795961 baseEnd_3795961 := by
    simpa [prefixWord, tailWord_3795961, baseEnd_3795961] using wordTrace_append hprefix tailTrace_3795961
  have hstable : (prefixWord ++ tailWord_3795961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795961).length < 2 ^ (prefixWord ++ tailWord_3795961).sum := by decide
  have hdescent : baseEnd_3795961 < baseStart_3795961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795992 : List Nat := [2, 1, 2, 3, 2, 2, 2, 4, 1, 2, 2]
def baseStart_3795992 : Nat := 118140960795 + 3795992 * 2 ^ 59
def prefixEnd_3795992 : Nat := 4983230072969 + 3 ^ 40 * 3795992 * 2
def baseEnd_3795992 : Nat := 1949168456622017397542557

theorem tailTrace_3795992 : CollatzResearch.WordTrace tailWord_3795992 prefixEnd_3795992 1949168456622017397542557 := by
  unfold tailWord_3795992
  simp only [CollatzResearch.WordTrace]
  refine ⟨69225601231888381332303115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92300801642517841776404153 69225601231888381332303115)
  ·
    refine ⟨103838401847832571998454673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69225601231888381332303115 103838401847832571998454673)
    ·
      refine ⟨77878801385874428998841005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103838401847832571998454673 77878801385874428998841005)
      ·
        refine ⟨29204550519702910874565377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77878801385874428998841005 29204550519702910874565377)
        ·
          refine ⟨21903412889777183155924033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29204550519702910874565377 21903412889777183155924033)
          ·
            refine ⟨16427559667332887366943025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21903412889777183155924033 16427559667332887366943025)
            ·
              refine ⟨12320669750499665525207269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16427559667332887366943025 12320669750499665525207269)
              ·
                refine ⟨2310125578218687285976363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12320669750499665525207269 2310125578218687285976363)
                ·
                  refine ⟨3465188367328030928964545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310125578218687285976363 3465188367328030928964545)
                  ·
                    refine ⟨2598891275496023196723409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3465188367328030928964545 2598891275496023196723409)
                    ·
                      refine ⟨1949168456622017397542557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2598891275496023196723409 1949168456622017397542557)
                      ·
                        rfl

theorem cell23_3795992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_3795992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3795992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3795992 prefixEnd_3795992 := by exact prefixLift 3795992
  have htrace : WordTrace (prefixWord ++ tailWord_3795992) baseStart_3795992 baseEnd_3795992 := by
    simpa [prefixWord, tailWord_3795992, baseEnd_3795992] using wordTrace_append hprefix tailTrace_3795992
  have hstable : (prefixWord ++ tailWord_3795992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795992).length < 2 ^ (prefixWord ++ tailWord_3795992).sum := by decide
  have hdescent : baseEnd_3795992 < baseStart_3795992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796081 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 3, 5, 3]
def baseStart_3796081 : Nat := 118140960795 + 3796081 * 2 ^ 59
def prefixEnd_3796081 : Nat := 4983230072969 + 3 ^ 40 * 3796081 * 2
def baseEnd_3796081 : Nat := 1949214156400267549329647

theorem tailTrace_3796081 : CollatzResearch.WordTrace tailWord_3796081 prefixEnd_3796081 1949214156400267549329647 := by
  unfold tailWord_3796081
  simp only [CollatzResearch.WordTrace]
  refine ⟨138454448560454330864596097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92302965706969553909730731 138454448560454330864596097)
  ·
    refine ⟨103840836420340748148447073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138454448560454330864596097 103840836420340748148447073)
    ·
      refine ⟨77880627315255561111335305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103840836420340748148447073 77880627315255561111335305)
      ·
        refine ⟨58410470486441670833501479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77880627315255561111335305 58410470486441670833501479)
        ·
          refine ⟨87615705729662506250252219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58410470486441670833501479 87615705729662506250252219)
          ·
            refine ⟨131423558594493759375378329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87615705729662506250252219 131423558594493759375378329)
            ·
              refine ⟨98567668945870319531533747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131423558594493759375378329 98567668945870319531533747)
              ·
                refine ⟨147851503418805479297300621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98567668945870319531533747 147851503418805479297300621)
                ·
                  refine ⟨55444313782052054736487733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147851503418805479297300621 55444313782052054736487733)
                  ·
                    refine ⟨5197904417067380131545725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55444313782052054736487733 5197904417067380131545725)
                    ·
                      refine ⟨1949214156400267549329647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5197904417067380131545725 1949214156400267549329647)
                      ·
                        rfl

theorem cell23_3796081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_3796081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796081 prefixEnd_3796081 := by exact prefixLift 3796081
  have htrace : WordTrace (prefixWord ++ tailWord_3796081) baseStart_3796081 baseEnd_3796081 := by
    simpa [prefixWord, tailWord_3796081, baseEnd_3796081] using wordTrace_append hprefix tailTrace_3796081
  have hstable : (prefixWord ++ tailWord_3796081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796081).length < 2 ^ (prefixWord ++ tailWord_3796081).sum := by decide
  have hdescent : baseEnd_3796081 < baseStart_3796081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796105 : List Nat := [1, 2, 1, 1, 4, 3, 4, 2, 5]
def baseStart_3796105 : Nat := 118140960795 + 3796105 * 2 ^ 59
def prefixEnd_3796105 : Nat := 4983230072969 + 3 ^ 40 * 3796105 * 2
def baseEnd_3796105 : Nat := 216580719992886161714393

theorem tailTrace_3796105 : CollatzResearch.WordTrace tailWord_3796105 prefixEnd_3796105 216580719992886161714393 := by
  unfold tailWord_3796105
  simp only [CollatzResearch.WordTrace]
  refine ⟨138455323912367382963469769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92303549274911588642313179 138455323912367382963469769)
  ·
    refine ⟨103841492934275537222602327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138455323912367382963469769 103841492934275537222602327)
    ·
      refine ⟨155762239401413305833903491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103841492934275537222602327 155762239401413305833903491)
      ·
        refine ⟨233643359102119958750855237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155762239401413305833903491 233643359102119958750855237)
        ·
          refine ⟨43808129831647492265785357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233643359102119958750855237 43808129831647492265785357)
          ·
            refine ⟨16428048686867809599669509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43808129831647492265785357 16428048686867809599669509)
            ·
              refine ⟨3080259128787714299938033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16428048686867809599669509 3080259128787714299938033)
              ·
                refine ⟨2310194346590785724953525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3080259128787714299938033 2310194346590785724953525)
                ·
                  refine ⟨216580719992886161714393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2310194346590785724953525 216580719992886161714393)
                  ·
                    rfl

theorem cell23_3796105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 5].length) (baseStart_3796105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796105 prefixEnd_3796105 := by exact prefixLift 3796105
  have htrace : WordTrace (prefixWord ++ tailWord_3796105) baseStart_3796105 baseEnd_3796105 := by
    simpa [prefixWord, tailWord_3796105, baseEnd_3796105] using wordTrace_append hprefix tailTrace_3796105
  have hstable : (prefixWord ++ tailWord_3796105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796105).length < 2 ^ (prefixWord ++ tailWord_3796105).sum := by decide
  have hdescent : baseEnd_3796105 < baseStart_3796105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796135 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 2, 5]
def baseStart_3796135 : Nat := 118140960795 + 3796135 * 2 ^ 59
def prefixEnd_3796135 : Nat := 4983230072969 + 3 ^ 40 * 3796135 * 2
def baseEnd_3796135 : Nat := 649747294785203446018133

theorem tailTrace_3796135 : CollatzResearch.WordTrace tailWord_3796135 prefixEnd_3796135 649747294785203446018133 := by
  unfold tailWord_3796135
  simp only [CollatzResearch.WordTrace]
  refine ⟨138456418102258698087061859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92304278734839132058041239 138456418102258698087061859)
  ·
    refine ⟨207684627153388047130592789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138456418102258698087061859 207684627153388047130592789)
    ·
      refine ⟨9735216897815064709246537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 207684627153388047130592789 9735216897815064709246537)
      ·
        refine ⟨7301412673361298531934903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9735216897815064709246537 7301412673361298531934903)
        ·
          refine ⟨10952119010041947797902355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7301412673361298531934903 10952119010041947797902355)
          ·
            refine ⟨16428178515062921696853533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10952119010041947797902355 16428178515062921696853533)
            ·
              refine ⟨6160566943148595636320075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16428178515062921696853533 6160566943148595636320075)
              ·
                refine ⟨9240850414722893454480113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6160566943148595636320075 9240850414722893454480113)
                ·
                  refine ⟨6930637811042170090860085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9240850414722893454480113 6930637811042170090860085)
                  ·
                    refine ⟨649747294785203446018133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6930637811042170090860085 649747294785203446018133)
                    ·
                      rfl

theorem cell23_3796135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_3796135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796135 prefixEnd_3796135 := by exact prefixLift 3796135
  have htrace : WordTrace (prefixWord ++ tailWord_3796135) baseStart_3796135 baseEnd_3796135 := by
    simpa [prefixWord, tailWord_3796135, baseEnd_3796135] using wordTrace_append hprefix tailTrace_3796135
  have hstable : (prefixWord ++ tailWord_3796135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796135).length < 2 ^ (prefixWord ++ tailWord_3796135).sum := by decide
  have hdescent : baseEnd_3796135 < baseStart_3796135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796150 : List Nat := [5, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_3796150 : Nat := 118140960795 + 3796150 * 2 ^ 59
def prefixEnd_3796150 : Nat := 4983230072969 + 3 ^ 40 * 3796150 * 2
def baseEnd_3796150 : Nat := 1949249586565427779366831

theorem tailTrace_3796150 : CollatzResearch.WordTrace tailWord_3796150 prefixEnd_3796150 1949249586565427779366831 := by
  unfold tailWord_3796150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653560324825272228053619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92304643464802903765905269 8653560324825272228053619)
  ·
    refine ⟨12980340487237908342080429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8653560324825272228053619 12980340487237908342080429)
    ·
      refine ⟨4867627682714215628280161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12980340487237908342080429 4867627682714215628280161)
      ·
        refine ⟨3650720762035661721210121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4867627682714215628280161 3650720762035661721210121)
        ·
          refine ⟨2738040571526746290907591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3650720762035661721210121 2738040571526746290907591)
          ·
            refine ⟨4107060857290119436361387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738040571526746290907591 4107060857290119436361387)
            ·
              refine ⟨6160591285935179154542081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4107060857290119436361387 6160591285935179154542081)
              ·
                refine ⟨4620443464451384365906561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6160591285935179154542081 4620443464451384365906561)
                ·
                  refine ⟨3465332598338538274429921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4620443464451384365906561 3465332598338538274429921)
                  ·
                    refine ⟨2598999448753903705822441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3465332598338538274429921 2598999448753903705822441)
                    ·
                      refine ⟨1949249586565427779366831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2598999448753903705822441 1949249586565427779366831)
                      ·
                        rfl

theorem cell23_3796150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_3796150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796150 prefixEnd_3796150 := by exact prefixLift 3796150
  have htrace : WordTrace (prefixWord ++ tailWord_3796150) baseStart_3796150 baseEnd_3796150 := by
    simpa [prefixWord, tailWord_3796150, baseEnd_3796150] using wordTrace_append hprefix tailTrace_3796150
  have hstable : (prefixWord ++ tailWord_3796150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796150).length < 2 ^ (prefixWord ++ tailWord_3796150).sum := by decide
  have hdescent : baseEnd_3796150 < baseStart_3796150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796151 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_3796151 : Nat := 118140960795 + 3796151 * 2 ^ 59
def prefixEnd_3796151 : Nat := 4983230072969 + 3 ^ 40 * 3796151 * 2
def baseEnd_3796151 : Nat := 1949250100046082275454325

theorem tailTrace_3796151 : CollatzResearch.WordTrace tailWord_3796151 prefixEnd_3796151 1949250100046082275454325 := by
  unfold tailWord_3796151
  simp only [CollatzResearch.WordTrace]
  refine ⟨138457001670200732819644307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92304667780133821879762871 138457001670200732819644307)
  ·
    refine ⟨207685502505301099229466461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138457001670200732819644307 207685502505301099229466461)
    ·
      refine ⟨77882063439487912211049923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207685502505301099229466461 77882063439487912211049923)
      ·
        refine ⟨116823095159231868316574885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77882063439487912211049923 116823095159231868316574885)
        ·
          refine ⟨21904330342355975309357791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116823095159231868316574885 21904330342355975309357791)
          ·
            refine ⟨32856495513533962964036687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21904330342355975309357791 32856495513533962964036687)
            ·
              refine ⟨49284743270300944446055031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32856495513533962964036687 49284743270300944446055031)
              ·
                refine ⟨73927114905451416669082547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49284743270300944446055031 73927114905451416669082547)
                ·
                  refine ⟨110890672358177125003623821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73927114905451416669082547 110890672358177125003623821)
                  ·
                    refine ⟨41584002134316421876358933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110890672358177125003623821 41584002134316421876358933)
                    ·
                      refine ⟨1949250100046082275454325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41584002134316421876358933 1949250100046082275454325)
                      ·
                        rfl

theorem cell23_3796151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_3796151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796151 prefixEnd_3796151 := by exact prefixLift 3796151
  have htrace : WordTrace (prefixWord ++ tailWord_3796151) baseStart_3796151 baseEnd_3796151 := by
    simpa [prefixWord, tailWord_3796151, baseEnd_3796151] using wordTrace_append hprefix tailTrace_3796151
  have hstable : (prefixWord ++ tailWord_3796151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796151).length < 2 ^ (prefixWord ++ tailWord_3796151).sum := by decide
  have hdescent : baseEnd_3796151 < baseStart_3796151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796201 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 5]
def baseStart_3796201 : Nat := 118140960795 + 3796201 * 2 ^ 59
def prefixEnd_3796201 : Nat := 4983230072969 + 3 ^ 40 * 3796201 * 2
def baseEnd_3796201 : Nat := 1949275774078807079829095

theorem tailTrace_3796201 : CollatzResearch.WordTrace tailWord_3796201 prefixEnd_3796201 1949275774078807079829095 := by
  unfold tailWord_3796201
  simp only [CollatzResearch.WordTrace]
  refine ⟨138458825320019591358964457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92305883546679727572642971 138458825320019591358964457)
  ·
    refine ⟨103844118990014693519223343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138458825320019591358964457 103844118990014693519223343)
    ·
      refine ⟨155766178485022040278835015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103844118990014693519223343 155766178485022040278835015)
      ·
        refine ⟨233649267727533060418252523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155766178485022040278835015 233649267727533060418252523)
        ·
          refine ⟨350473901591299590627378785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233649267727533060418252523 350473901591299590627378785)
          ·
            refine ⟨262855426193474692970534089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350473901591299590627378785 262855426193474692970534089)
            ·
              refine ⟨197141569645106019727900567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262855426193474692970534089 197141569645106019727900567)
              ·
                refine ⟨295712354467659029591850851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197141569645106019727900567 295712354467659029591850851)
                ·
                  refine ⟨443568531701488544387776277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295712354467659029591850851 443568531701488544387776277)
                  ·
                    refine ⟨20792274923507275518177013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 443568531701488544387776277 20792274923507275518177013)
                    ·
                      refine ⟨1949275774078807079829095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20792274923507275518177013 1949275774078807079829095)
                      ·
                        rfl

theorem cell23_3796201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_3796201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796201 prefixEnd_3796201 := by exact prefixLift 3796201
  have htrace : WordTrace (prefixWord ++ tailWord_3796201) baseStart_3796201 baseEnd_3796201 := by
    simpa [prefixWord, tailWord_3796201, baseEnd_3796201] using wordTrace_append hprefix tailTrace_3796201
  have hstable : (prefixWord ++ tailWord_3796201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796201).length < 2 ^ (prefixWord ++ tailWord_3796201).sum := by decide
  have hdescent : baseEnd_3796201 < baseStart_3796201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796215 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 2, 3, 2]
def baseStart_3796215 : Nat := 118140960795 + 3796215 * 2 ^ 59
def prefixEnd_3796215 : Nat := 4983230072969 + 3 ^ 40 * 3796215 * 2
def baseEnd_3796215 : Nat := 1949282962807970025054031

theorem tailTrace_3796215 : CollatzResearch.WordTrace tailWord_3796215 prefixEnd_3796215 1949282962807970025054031 := by
  unfold tailWord_3796215
  simp only [CollatzResearch.WordTrace]
  refine ⟨138459335941968871749974099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92306223961312581166649399 138459335941968871749974099)
  ·
    refine ⟨207689003912953307624961149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138459335941968871749974099 207689003912953307624961149)
    ·
      refine ⟨77883376467357490359360431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207689003912953307624961149 77883376467357490359360431)
      ·
        refine ⟨116825064701036235539040647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77883376467357490359360431 116825064701036235539040647)
        ·
          refine ⟨175237597051554353308560971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116825064701036235539040647 175237597051554353308560971)
          ·
            refine ⟨262856395577331529962841457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175237597051554353308560971 262856395577331529962841457)
            ·
              refine ⟨197142296682998647472131093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262856395577331529962841457 197142296682998647472131093)
              ·
                refine ⟨9241045157015561600256145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197142296682998647472131093 9241045157015561600256145)
                ·
                  refine ⟨6930783867761671200192109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9241045157015561600256145 6930783867761671200192109)
                  ·
                    refine ⟨2599043950410626700072041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6930783867761671200192109 2599043950410626700072041)
                    ·
                      refine ⟨1949282962807970025054031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2599043950410626700072041 1949282962807970025054031)
                      ·
                        rfl

theorem cell23_3796215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 3, 2].length) (baseStart_3796215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796215 prefixEnd_3796215 := by exact prefixLift 3796215
  have htrace : WordTrace (prefixWord ++ tailWord_3796215) baseStart_3796215 baseEnd_3796215 := by
    simpa [prefixWord, tailWord_3796215, baseEnd_3796215] using wordTrace_append hprefix tailTrace_3796215
  have hstable : (prefixWord ++ tailWord_3796215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796215).length < 2 ^ (prefixWord ++ tailWord_3796215).sum := by decide
  have hdescent : baseEnd_3796215 < baseStart_3796215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796255 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 1, 6]
def baseStart_3796255 : Nat := 118140960795 + 3796255 * 2 ^ 59
def prefixEnd_3796255 : Nat := 4983230072969 + 3 ^ 40 * 3796255 * 2
def baseEnd_3796255 : Nat := 649767834011383289517949

theorem tailTrace_3796255 : CollatzResearch.WordTrace tailWord_3796255 prefixEnd_3796255 649767834011383289517949 := by
  unfold tailWord_3796255
  simp only [CollatzResearch.WordTrace]
  refine ⟨138460794861823958581430219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92307196574549305720953479 138460794861823958581430219)
  ·
    refine ⟨207691192292735937872145329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138460794861823958581430219 207691192292735937872145329)
    ·
      refine ⟨155768394219551953404108997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207691192292735937872145329 155768394219551953404108997)
      ·
        refine ⟨29206573916165991263270437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155768394219551953404108997 29206573916165991263270437)
        ·
          refine ⟨5476232609281123361863207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29206573916165991263270437 5476232609281123361863207)
          ·
            refine ⟨8214348913921685042794811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5476232609281123361863207 8214348913921685042794811)
            ·
              refine ⟨12321523370882527564192217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8214348913921685042794811 12321523370882527564192217)
              ·
                refine ⟨9241142528161895673144163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12321523370882527564192217 9241142528161895673144163)
                ·
                  refine ⟨13861713792242843509716245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9241142528161895673144163 13861713792242843509716245)
                  ·
                    refine ⟨649767834011383289517949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13861713792242843509716245 649767834011383289517949)
                    ·
                      rfl

theorem cell23_3796255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 6].length) (baseStart_3796255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796255 prefixEnd_3796255 := by exact prefixLift 3796255
  have htrace : WordTrace (prefixWord ++ tailWord_3796255) baseStart_3796255 baseEnd_3796255 := by
    simpa [prefixWord, tailWord_3796255, baseEnd_3796255] using wordTrace_append hprefix tailTrace_3796255
  have hstable : (prefixWord ++ tailWord_3796255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796255).length < 2 ^ (prefixWord ++ tailWord_3796255).sum := by decide
  have hdescent : baseEnd_3796255 < baseStart_3796255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796292 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3796292 : Nat := 118140960795 + 3796292 * 2 ^ 59
def prefixEnd_3796292 : Nat := 4983230072969 + 3 ^ 40 * 3796292 * 2
def baseEnd_3796292 : Nat := 1949322500818366223791177

theorem tailTrace_3796292 : CollatzResearch.WordTrace tailWord_3796292 prefixEnd_3796292 1949322500818366223791177 := by
  unfold tailWord_3796292
  simp only [CollatzResearch.WordTrace]
  refine ⟨69231072181344956950263565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92308096241793275933684753 69231072181344956950263565)
  ·
    refine ⟨25961652068004358856348837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69231072181344956950263565 25961652068004358856348837)
    ·
      refine ⟨4867809762750817285565407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25961652068004358856348837 4867809762750817285565407)
      ·
        refine ⟨7301714644126225928348111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867809762750817285565407 7301714644126225928348111)
        ·
          refine ⟨10952571966189338892522167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7301714644126225928348111 10952571966189338892522167)
          ·
            refine ⟨16428857949284008338783251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10952571966189338892522167 16428857949284008338783251)
            ·
              refine ⟨24643286923926012508174877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16428857949284008338783251 24643286923926012508174877)
              ·
                refine ⟨9241232596472254690565579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24643286923926012508174877 9241232596472254690565579)
                ·
                  refine ⟨13861848894708382035848369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9241232596472254690565579 13861848894708382035848369)
                  ·
                    refine ⟨10396386671031286526886277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13861848894708382035848369 10396386671031286526886277)
                    ·
                      refine ⟨1949322500818366223791177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10396386671031286526886277 1949322500818366223791177)
                      ·
                        rfl

theorem cell23_3796292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3796292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796292 prefixEnd_3796292 := by exact prefixLift 3796292
  have htrace : WordTrace (prefixWord ++ tailWord_3796292) baseStart_3796292 baseEnd_3796292 := by
    simpa [prefixWord, tailWord_3796292, baseEnd_3796292] using wordTrace_append hprefix tailTrace_3796292
  have hstable : (prefixWord ++ tailWord_3796292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796292).length < 2 ^ (prefixWord ++ tailWord_3796292).sum := by decide
  have hdescent : baseEnd_3796292 < baseStart_3796292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796295 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_3796295 : Nat := 118140960795 + 3796295 * 2 ^ 59
def prefixEnd_3796295 : Nat := 4983230072969 + 3 ^ 40 * 3796295 * 2
def baseEnd_3796295 : Nat := 1949324041260329712053663

theorem tailTrace_3796295 : CollatzResearch.WordTrace tailWord_3796295 prefixEnd_3796295 1949324041260329712053663 := by
  unfold tailWord_3796295
  simp only [CollatzResearch.WordTrace]
  refine ⟨138462253781679045412886339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92308169187786030275257559 138462253781679045412886339)
  ·
    refine ⟨207693380672518568119329509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138462253781679045412886339 207693380672518568119329509)
    ·
      refine ⟨38942508876097231522374283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207693380672518568119329509 38942508876097231522374283)
      ·
        refine ⟨58413763314145847283561425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38942508876097231522374283 58413763314145847283561425)
        ·
          refine ⟨43810322485609385462671069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58413763314145847283561425 43810322485609385462671069)
          ·
            refine ⟨16428870932103519548501651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43810322485609385462671069 16428870932103519548501651)
            ·
              refine ⟨24643306398155279322752477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16428870932103519548501651 24643306398155279322752477)
              ·
                refine ⟨9241239899308229746032179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24643306398155279322752477 9241239899308229746032179)
                ·
                  refine ⟨13861859848962344619048269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9241239899308229746032179 13861859848962344619048269)
                  ·
                    refine ⟨5198197443360879232143101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13861859848962344619048269 5198197443360879232143101)
                    ·
                      refine ⟨1949324041260329712053663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5198197443360879232143101 1949324041260329712053663)
                      ·
                        rfl

theorem cell23_3796295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_3796295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796295 prefixEnd_3796295 := by exact prefixLift 3796295
  have htrace : WordTrace (prefixWord ++ tailWord_3796295) baseStart_3796295 baseEnd_3796295 := by
    simpa [prefixWord, tailWord_3796295, baseEnd_3796295] using wordTrace_append hprefix tailTrace_3796295
  have hstable : (prefixWord ++ tailWord_3796295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796295).length < 2 ^ (prefixWord ++ tailWord_3796295).sum := by decide
  have hdescent : baseEnd_3796295 < baseStart_3796295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796310 : List Nat := [5, 2, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3796310 : Nat := 118140960795 + 3796310 * 2 ^ 59
def prefixEnd_3796310 : Nat := 4983230072969 + 3 ^ 40 * 3796310 * 2
def baseEnd_3796310 : Nat := 649777247823382384455365

theorem tailTrace_3796310 : CollatzResearch.WordTrace tailWord_3796310 prefixEnd_3796310 649777247823382384455365 := by
  unfold tailWord_3796310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653925054789043935917649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92308533917749801983121589 8653925054789043935917649)
  ·
    refine ⟨6490443791091782951938237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8653925054789043935917649 6490443791091782951938237)
    ·
      refine ⟨2433916421659418606976839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6490443791091782951938237 2433916421659418606976839)
      ·
        refine ⟨3650874632489127910465259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433916421659418606976839 3650874632489127910465259)
        ·
          refine ⟨5476311948733691865697889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3650874632489127910465259 5476311948733691865697889)
          ·
            refine ⟨4107233961550268899273417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5476311948733691865697889 4107233961550268899273417)
            ·
              refine ⟨3080425471162701674455063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4107233961550268899273417 3080425471162701674455063)
              ·
                refine ⟨4620638206744052511682595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3080425471162701674455063 4620638206744052511682595)
                ·
                  refine ⟨6930957310116078767523893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4620638206744052511682595 6930957310116078767523893)
                  ·
                    refine ⟨649777247823382384455365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6930957310116078767523893 649777247823382384455365)
                    ·
                      rfl

theorem cell23_3796310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3796310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796310 prefixEnd_3796310 := by exact prefixLift 3796310
  have htrace : WordTrace (prefixWord ++ tailWord_3796310) baseStart_3796310 baseEnd_3796310 := by
    simpa [prefixWord, tailWord_3796310, baseEnd_3796310] using wordTrace_append hprefix tailTrace_3796310
  have hstable : (prefixWord ++ tailWord_3796310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796310).length < 2 ^ (prefixWord ++ tailWord_3796310).sum := by decide
  have hdescent : baseEnd_3796310 < baseStart_3796310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796372 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3796372 : Nat := 118140960795 + 3796372 * 2 ^ 59
def prefixEnd_3796372 : Nat := 4983230072969 + 3 ^ 40 * 3796372 * 2
def baseEnd_3796372 : Nat := 1949363579270725910790809

theorem tailTrace_3796372 : CollatzResearch.WordTrace tailWord_3796372 prefixEnd_3796372 1949363579270725910790809 := by
  unfold tailWord_3796372
  simp only [CollatzResearch.WordTrace]
  refine ⟨69232531101200043781719685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92310041468266725042292913 69232531101200043781719685)
  ·
    refine ⟨12981099581475008209072441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69232531101200043781719685 12981099581475008209072441)
    ·
      refine ⟨9735824686106256156804331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12981099581475008209072441 9735824686106256156804331)
      ·
        refine ⟨14603737029159384235206497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9735824686106256156804331 14603737029159384235206497)
        ·
          refine ⟨10952802771869538176404873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14603737029159384235206497 10952802771869538176404873)
          ·
            refine ⟨8214602078902153632303655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10952802771869538176404873 8214602078902153632303655)
            ·
              refine ⟨12321903118353230448455483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8214602078902153632303655 12321903118353230448455483)
              ·
                refine ⟨18482854677529845672683225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12321903118353230448455483 18482854677529845672683225)
                ·
                  refine ⟨13862141008147384254512419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18482854677529845672683225 13862141008147384254512419)
                  ·
                    refine ⟨20793211512221076381768629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13862141008147384254512419 20793211512221076381768629)
                    ·
                      refine ⟨1949363579270725910790809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20793211512221076381768629 1949363579270725910790809)
                      ·
                        rfl

theorem cell23_3796372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3796372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796372 prefixEnd_3796372 := by exact prefixLift 3796372
  have htrace : WordTrace (prefixWord ++ tailWord_3796372) baseStart_3796372 baseEnd_3796372 := by
    simpa [prefixWord, tailWord_3796372, baseEnd_3796372] using wordTrace_append hprefix tailTrace_3796372
  have hstable : (prefixWord ++ tailWord_3796372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796372).length < 2 ^ (prefixWord ++ tailWord_3796372).sum := by decide
  have hdescent : baseEnd_3796372 < baseStart_3796372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796442 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_3796442 : Nat := 118140960795 + 3796442 * 2 ^ 59
def prefixEnd_3796442 : Nat := 4983230072969 + 3 ^ 40 * 3796442 * 2
def baseEnd_3796442 : Nat := 1949399522916540636915487

theorem tailTrace_3796442 : CollatzResearch.WordTrace tailWord_3796442 prefixEnd_3796442 1949399522916540636915487 := by
  unfold tailWord_3796442
  simp only [CollatzResearch.WordTrace]
  refine ⟨34616903828036622379621895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92311743541430993012325053 34616903828036622379621895)
  ·
    refine ⟨51925355742054933569432843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34616903828036622379621895 51925355742054933569432843)
    ·
      refine ⟨77888033613082400354149265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51925355742054933569432843 77888033613082400354149265)
      ·
        refine ⟨58416025209811800265611949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77888033613082400354149265 58416025209811800265611949)
        ·
          refine ⟨21906009453679425099604481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58416025209811800265611949 21906009453679425099604481)
          ·
            refine ⟨16429507090259568824703361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21906009453679425099604481 16429507090259568824703361)
            ·
              refine ⟨12322130317694676618527521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16429507090259568824703361 12322130317694676618527521)
              ·
                refine ⟨9241597738271007463895641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12322130317694676618527521 9241597738271007463895641)
                ·
                  refine ⟨6931198303703255597921731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9241597738271007463895641 6931198303703255597921731)
                  ·
                    refine ⟨10396797455554883396882597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6931198303703255597921731 10396797455554883396882597)
                    ·
                      refine ⟨1949399522916540636915487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10396797455554883396882597 1949399522916540636915487)
                      ·
                        rfl

theorem cell23_3796442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_3796442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796442 prefixEnd_3796442 := by exact prefixLift 3796442
  have htrace : WordTrace (prefixWord ++ tailWord_3796442) baseStart_3796442 baseEnd_3796442 := by
    simpa [prefixWord, tailWord_3796442, baseEnd_3796442] using wordTrace_append hprefix tailTrace_3796442
  have hstable : (prefixWord ++ tailWord_3796442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796442).length < 2 ^ (prefixWord ++ tailWord_3796442).sum := by decide
  have hdescent : baseEnd_3796442 < baseStart_3796442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796462 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_3796462 : Nat := 118140960795 + 3796462 * 2 ^ 59
def prefixEnd_3796462 : Nat := 4983230072969 + 3 ^ 40 * 3796462 * 2
def baseEnd_3796462 : Nat := 1949409792529630558665395

theorem tailTrace_3796462 : CollatzResearch.WordTrace tailWord_3796462 prefixEnd_3796462 1949409792529630558665395 := by
  unfold tailWord_3796462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17308543096509254116776955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92312229848049355289477093 17308543096509254116776955)
  ·
    refine ⟨25962814644763881175165433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17308543096509254116776955 25962814644763881175165433)
    ·
      refine ⟨19472110983572910881374075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25962814644763881175165433 19472110983572910881374075)
      ·
        refine ⟨29208166475359366322061113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19472110983572910881374075 29208166475359366322061113)
        ·
          refine ⟨21906124856519524741545835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29208166475359366322061113 21906124856519524741545835)
          ·
            refine ⟨32859187284779287112318753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21906124856519524741545835 32859187284779287112318753)
            ·
              refine ⟨24644390463584465334239065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32859187284779287112318753 24644390463584465334239065)
              ·
                refine ⟨18483292847688349000679299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24644390463584465334239065 18483292847688349000679299)
                ·
                  refine ⟨27724939271532523501018949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18483292847688349000679299 27724939271532523501018949)
                  ·
                    refine ⟨5198426113412348156441053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27724939271532523501018949 5198426113412348156441053)
                    ·
                      refine ⟨1949409792529630558665395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5198426113412348156441053 1949409792529630558665395)
                      ·
                        rfl

theorem cell23_3796462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_3796462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796462 prefixEnd_3796462 := by exact prefixLift 3796462
  have htrace : WordTrace (prefixWord ++ tailWord_3796462) baseStart_3796462 baseEnd_3796462 := by
    simpa [prefixWord, tailWord_3796462, baseEnd_3796462] using wordTrace_append hprefix tailTrace_3796462
  have hstable : (prefixWord ++ tailWord_3796462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796462).length < 2 ^ (prefixWord ++ tailWord_3796462).sum := by decide
  have hdescent : baseEnd_3796462 < baseStart_3796462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796469 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3796469 : Nat := 118140960795 + 3796469 * 2 ^ 59
def prefixEnd_3796469 : Nat := 4983230072969 + 3 ^ 40 * 3796469 * 2
def baseEnd_3796469 : Nat := 649804462298070677092621

theorem tailTrace_3796469 : CollatzResearch.WordTrace tailWord_3796469 prefixEnd_3796469 649804462298070677092621 := by
  unfold tailWord_3796469
  simp only [CollatzResearch.WordTrace]
  refine ⟨138468600083048673129720461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92312400055365782086480307 138468600083048673129720461)
  ·
    refine ⟨51925725031143252423645173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138468600083048673129720461 51925725031143252423645173)
    ·
      refine ⟨4868036721669679914716735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51925725031143252423645173 4868036721669679914716735)
      ·
        refine ⟨7302055082504519872075103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4868036721669679914716735 7302055082504519872075103)
        ·
          refine ⟨10953082623756779808112655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7302055082504519872075103 10953082623756779808112655)
          ·
            refine ⟨16429623935635169712168983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10953082623756779808112655 16429623935635169712168983)
            ·
              refine ⟨24644435903452754568253475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16429623935635169712168983 24644435903452754568253475)
              ·
                refine ⟨36966653855179131852380213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24644435903452754568253475 36966653855179131852380213)
                ·
                  refine ⟨3465623798923043611160645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36966653855179131852380213 3465623798923043611160645)
                  ·
                    refine ⟨649804462298070677092621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3465623798923043611160645 649804462298070677092621)
                    ·
                      rfl

theorem cell23_3796469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3796469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796469 prefixEnd_3796469 := by exact prefixLift 3796469
  have htrace : WordTrace (prefixWord ++ tailWord_3796469) baseStart_3796469 baseEnd_3796469 := by
    simpa [prefixWord, tailWord_3796469, baseEnd_3796469] using wordTrace_append hprefix tailTrace_3796469
  have hstable : (prefixWord ++ tailWord_3796469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796469).length < 2 ^ (prefixWord ++ tailWord_3796469).sum := by decide
  have hdescent : baseEnd_3796469 < baseStart_3796469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796475 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 3]
def baseStart_3796475 : Nat := 118140960795 + 3796475 * 2 ^ 59
def prefixEnd_3796475 : Nat := 4983230072969 + 3 ^ 40 * 3796475 * 2
def baseEnd_3796475 : Nat := 1949416467778139007802835

theorem tailTrace_3796475 : CollatzResearch.WordTrace tailWord_3796475 prefixEnd_3796475 1949416467778139007802835 := by
  unfold tailWord_3796475
  simp only [CollatzResearch.WordTrace]
  refine ⟨138468818921026936154438879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92312545947351290769625919 138468818921026936154438879)
  ·
    refine ⟨207703228381540404231658319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138468818921026936154438879 207703228381540404231658319)
    ·
      refine ⟨311554842572310606347487479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207703228381540404231658319 311554842572310606347487479)
      ·
        refine ⟨467332263858465909521231219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311554842572310606347487479 467332263858465909521231219)
        ·
          refine ⟨700998395787698864281846829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467332263858465909521231219 700998395787698864281846829)
          ·
            refine ⟨262874398420387074105692561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 700998395787698864281846829 262874398420387074105692561)
            ·
              refine ⟨197155798815290305579269421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262874398420387074105692561 197155798815290305579269421)
              ·
                refine ⟨73933424555733864592226033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197155798815290305579269421 73933424555733864592226033)
                ·
                  refine ⟨55450068416800398444169525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73933424555733864592226033 55450068416800398444169525)
                  ·
                    refine ⟨5198443914075037354140893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55450068416800398444169525 5198443914075037354140893)
                    ·
                      refine ⟨1949416467778139007802835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5198443914075037354140893 1949416467778139007802835)
                      ·
                        rfl

theorem cell23_3796475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 3].length) (baseStart_3796475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796475 prefixEnd_3796475 := by exact prefixLift 3796475
  have htrace : WordTrace (prefixWord ++ tailWord_3796475) baseStart_3796475 baseEnd_3796475 := by
    simpa [prefixWord, tailWord_3796475, baseEnd_3796475] using wordTrace_append hprefix tailTrace_3796475
  have hstable : (prefixWord ++ tailWord_3796475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796475).length < 2 ^ (prefixWord ++ tailWord_3796475).sum := by decide
  have hdescent : baseEnd_3796475 < baseStart_3796475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796526 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_3796526 : Nat := 118140960795 + 3796526 * 2 ^ 59
def prefixEnd_3796526 : Nat := 4983230072969 + 3 ^ 40 * 3796526 * 2
def baseEnd_3796526 : Nat := 1949442655291518308265101

theorem tailTrace_3796526 : CollatzResearch.WordTrace tailWord_3796526 prefixEnd_3796526 1949442655291518308265101 := by
  unfold tailWord_3796526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17308834880480271483068179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92313786029228114576363621 17308834880480271483068179)
  ·
    refine ⟨25963252320720407224602269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17308834880480271483068179 25963252320720407224602269)
    ·
      refine ⟨9736219620270152709225851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25963252320720407224602269 9736219620270152709225851)
      ·
        refine ⟨14604329430405229063838777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9736219620270152709225851 14604329430405229063838777)
        ·
          refine ⟨10953247072803921797879083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14604329430405229063838777 10953247072803921797879083)
          ·
            refine ⟨16429870609205882696818625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10953247072803921797879083 16429870609205882696818625)
            ·
              refine ⟨12322402956904412022613969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16429870609205882696818625 12322402956904412022613969)
              ·
                refine ⟨9241802217678309016960477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12322402956904412022613969 9241802217678309016960477)
                ·
                  refine ⟨3465675831629365881360179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9241802217678309016960477 3465675831629365881360179)
                  ·
                    refine ⟨5198513747444048822040269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3465675831629365881360179 5198513747444048822040269)
                    ·
                      refine ⟨1949442655291518308265101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5198513747444048822040269 1949442655291518308265101)
                      ·
                        rfl

theorem cell23_3796526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_3796526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796526 prefixEnd_3796526 := by exact prefixLift 3796526
  have htrace : WordTrace (prefixWord ++ tailWord_3796526) baseStart_3796526 baseEnd_3796526 := by
    simpa [prefixWord, tailWord_3796526, baseEnd_3796526] using wordTrace_append hprefix tailTrace_3796526
  have hstable : (prefixWord ++ tailWord_3796526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796526).length < 2 ^ (prefixWord ++ tailWord_3796526).sum := by decide
  have hdescent : baseEnd_3796526 < baseStart_3796526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796543 : List Nat := [1, 1, 2, 2, 3, 5, 1, 3, 1, 1, 3]
def baseStart_3796543 : Nat := 118140960795 + 3796543 * 2 ^ 59
def prefixEnd_3796543 : Nat := 4983230072969 + 3 ^ 40 * 3796543 * 2
def baseEnd_3796543 : Nat := 1949451384462644741752523

theorem tailTrace_3796543 : CollatzResearch.WordTrace tailWord_3796543 prefixEnd_3796543 1949451384462644741752523 := by
  unfold tailWord_3796543
  simp only [CollatzResearch.WordTrace]
  refine ⟨138471299084780583767914283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92314199389853722511942855 138471299084780583767914283)
  ·
    refine ⟨207706948627170875651871425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138471299084780583767914283 207706948627170875651871425)
    ·
      refine ⟨155780211470378156738903569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207706948627170875651871425 155780211470378156738903569)
      ·
        refine ⟨116835158602783617554177677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155780211470378156738903569 116835158602783617554177677)
        ·
          refine ⟨43813184476043856582816629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116835158602783617554177677 43813184476043856582816629)
          ·
            refine ⟨4107486044629111554639059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43813184476043856582816629 4107486044629111554639059)
            ·
              refine ⟨6161229066943667331958589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4107486044629111554639059 6161229066943667331958589)
              ·
                refine ⟨2310460900103875249484471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6161229066943667331958589 2310460900103875249484471)
                ·
                  refine ⟨3465691350155812874226707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310460900103875249484471 3465691350155812874226707)
                  ·
                    refine ⟨5198537025233719311340061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3465691350155812874226707 5198537025233719311340061)
                    ·
                      refine ⟨1949451384462644741752523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5198537025233719311340061 1949451384462644741752523)
                      ·
                        rfl

theorem cell23_3796543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 1, 1, 3].length) (baseStart_3796543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796543 prefixEnd_3796543 := by exact prefixLift 3796543
  have htrace : WordTrace (prefixWord ++ tailWord_3796543) baseStart_3796543 baseEnd_3796543 := by
    simpa [prefixWord, tailWord_3796543, baseEnd_3796543] using wordTrace_append hprefix tailTrace_3796543
  have hstable : (prefixWord ++ tailWord_3796543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796543).length < 2 ^ (prefixWord ++ tailWord_3796543).sum := by decide
  have hdescent : baseEnd_3796543 < baseStart_3796543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796552 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_3796552 : Nat := 118140960795 + 3796552 * 2 ^ 59
def prefixEnd_3796552 : Nat := 4983230072969 + 3 ^ 40 * 3796552 * 2
def baseEnd_3796552 : Nat := 1949456005788535206539981

theorem tailTrace_3796552 : CollatzResearch.WordTrace tailWord_3796552 prefixEnd_3796552 1949456005788535206539981 := by
  unfold tailWord_3796552
  simp only [CollatzResearch.WordTrace]
  refine ⟨69235813670873989152495955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92314418227831985536661273 69235813670873989152495955)
  ·
    refine ⟨103853720506310983728743933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69235813670873989152495955 103853720506310983728743933)
    ·
      refine ⟨38945145189866618898278975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103853720506310983728743933 38945145189866618898278975)
      ·
        refine ⟨58417717784799928347418463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38945145189866618898278975 58417717784799928347418463)
        ·
          refine ⟨87626576677199892521127695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58417717784799928347418463 87626576677199892521127695)
          ·
            refine ⟨131439865015799838781691543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87626576677199892521127695 131439865015799838781691543)
            ·
              refine ⟨197159797523699758172537315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131439865015799838781691543 197159797523699758172537315)
              ·
                refine ⟨295739696285549637258805973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197159797523699758172537315 295739696285549637258805973)
                ·
                  refine ⟨6931399131692569623253265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 295739696285549637258805973 6931399131692569623253265)
                  ·
                    refine ⟨5198549348769427217439949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6931399131692569623253265 5198549348769427217439949)
                    ·
                      refine ⟨1949456005788535206539981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5198549348769427217439949 1949456005788535206539981)
                      ·
                        rfl

theorem cell23_3796552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_3796552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796552 prefixEnd_3796552 := by exact prefixLift 3796552
  have htrace : WordTrace (prefixWord ++ tailWord_3796552) baseStart_3796552 baseEnd_3796552 := by
    simpa [prefixWord, tailWord_3796552, baseEnd_3796552] using wordTrace_append hprefix tailTrace_3796552
  have hstable : (prefixWord ++ tailWord_3796552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796552).length < 2 ^ (prefixWord ++ tailWord_3796552).sum := by decide
  have hdescent : baseEnd_3796552 < baseStart_3796552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796562 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_3796562 : Nat := 118140960795 + 3796562 * 2 ^ 59
def prefixEnd_3796562 : Nat := 4983230072969 + 3 ^ 40 * 3796562 * 2
def baseEnd_3796562 : Nat := 1949461140595080167414935

theorem tailTrace_3796562 : CollatzResearch.WordTrace tailWord_3796562 prefixEnd_3796562 1949461140595080167414935 := by
  unfold tailWord_3796562
  simp only [CollatzResearch.WordTrace]
  refine ⟨34617998017927937503213985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92314661381141166675237293 34617998017927937503213985)
  ·
    refine ⟨25963498513445953127410489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34617998017927937503213985 25963498513445953127410489)
    ·
      refine ⟨19472623885084464845557867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25963498513445953127410489 19472623885084464845557867)
      ·
        refine ⟨29208935827626697268336801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19472623885084464845557867 29208935827626697268336801)
        ·
          refine ⟨21906701870720022951252601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29208935827626697268336801 21906701870720022951252601)
          ·
            refine ⟨16430026403040017213439451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21906701870720022951252601 16430026403040017213439451)
            ·
              refine ⟨24645039604560025820159177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16430026403040017213439451 24645039604560025820159177)
              ·
                refine ⟨18483779703420019365119383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24645039604560025820159177 18483779703420019365119383)
                ·
                  refine ⟨27725669555130029047679075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18483779703420019365119383 27725669555130029047679075)
                  ·
                    refine ⟨41588504332695043571518613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27725669555130029047679075 41588504332695043571518613)
                    ·
                      refine ⟨1949461140595080167414935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41588504332695043571518613 1949461140595080167414935)
                      ·
                        rfl

theorem cell23_3796562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_3796562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796562 prefixEnd_3796562 := by exact prefixLift 3796562
  have htrace : WordTrace (prefixWord ++ tailWord_3796562) baseStart_3796562 baseEnd_3796562 := by
    simpa [prefixWord, tailWord_3796562, baseEnd_3796562] using wordTrace_append hprefix tailTrace_3796562
  have hstable : (prefixWord ++ tailWord_3796562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796562).length < 2 ^ (prefixWord ++ tailWord_3796562).sum := by decide
  have hdescent : baseEnd_3796562 < baseStart_3796562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796572 : List Nat := [2, 2, 4, 1, 2, 1, 1, 10]
def baseStart_3796572 : Nat := 118140960795 + 3796572 * 2 ^ 59
def prefixEnd_3796572 : Nat := 4983230072969 + 3 ^ 40 * 3796572 * 2
def baseEnd_3796572 : Nat := 72202454644504634381107

theorem tailTrace_3796572 : CollatzResearch.WordTrace tailWord_3796572 prefixEnd_3796572 72202454644504634381107 := by
  unfold tailWord_3796572
  simp only [CollatzResearch.WordTrace]
  refine ⟨69236178400837760860359985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92314904534450347813813313 69236178400837760860359985)
  ·
    refine ⟨51927133800628320645269989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69236178400837760860359985 51927133800628320645269989)
    ·
      refine ⟨9736337587617810120988123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51927133800628320645269989 9736337587617810120988123)
      ·
        refine ⟨14604506381426715181482185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9736337587617810120988123 14604506381426715181482185)
        ·
          refine ⟨10953379786070036386111639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14604506381426715181482185 10953379786070036386111639)
          ·
            refine ⟨16430069679105054579167459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10953379786070036386111639 16430069679105054579167459)
            ·
              refine ⟨24645104518657581868751189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16430069679105054579167459 24645104518657581868751189)
              ·
                refine ⟨72202454644504634381107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24645104518657581868751189 72202454644504634381107)
                ·
                  rfl

theorem cell23_3796572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 10].length) (baseStart_3796572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796572 prefixEnd_3796572 := by exact prefixLift 3796572
  have htrace : WordTrace (prefixWord ++ tailWord_3796572) baseStart_3796572 baseEnd_3796572 := by
    simpa [prefixWord, tailWord_3796572, baseEnd_3796572] using wordTrace_append hprefix tailTrace_3796572
  have hstable : (prefixWord ++ tailWord_3796572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796572).length < 2 ^ (prefixWord ++ tailWord_3796572).sum := by decide
  have hdescent : baseEnd_3796572 < baseStart_3796572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796586 : List Nat := [3, 1, 3, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_3796586 : Nat := 118140960795 + 3796586 * 2 ^ 59
def prefixEnd_3796586 : Nat := 4983230072969 + 3 ^ 40 * 3796586 * 2
def baseEnd_3796586 : Nat := 1949473464130788073514825

theorem tailTrace_3796586 : CollatzResearch.WordTrace tailWord_3796586 prefixEnd_3796586 1949473464130788073514825 := by
  unfold tailWord_3796586
  simp only [CollatzResearch.WordTrace]
  refine ⟨34618216855906200527932403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92315244949083201407819741 34618216855906200527932403)
  ·
    refine ⟨51927325283859300791898605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34618216855906200527932403 51927325283859300791898605)
    ·
      refine ⟨19472746981447237796961977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51927325283859300791898605 19472746981447237796961977)
      ·
        refine ⟨14604560236085428347721483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19472746981447237796961977 14604560236085428347721483)
        ·
          refine ⟨21906840354128142521582225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14604560236085428347721483 21906840354128142521582225)
          ·
            refine ⟨16430130265596106891186669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21906840354128142521582225 16430130265596106891186669)
            ·
              refine ⟨6161298849598540084195001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16430130265596106891186669 6161298849598540084195001)
              ·
                refine ⟨4620974137198905063146251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6161298849598540084195001 4620974137198905063146251)
                ·
                  refine ⟨6931461205798357594719377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4620974137198905063146251 6931461205798357594719377)
                  ·
                    refine ⟨5198595904348768196039533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6931461205798357594719377 5198595904348768196039533)
                    ·
                      refine ⟨1949473464130788073514825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5198595904348768196039533 1949473464130788073514825)
                      ·
                        rfl

theorem cell23_3796586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_3796586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796586 prefixEnd_3796586 := by exact prefixLift 3796586
  have htrace : WordTrace (prefixWord ++ tailWord_3796586) baseStart_3796586 baseEnd_3796586 := by
    simpa [prefixWord, tailWord_3796586, baseEnd_3796586] using wordTrace_append hprefix tailTrace_3796586
  have hstable : (prefixWord ++ tailWord_3796586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796586).length < 2 ^ (prefixWord ++ tailWord_3796586).sum := by decide
  have hdescent : baseEnd_3796586 < baseStart_3796586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796595 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 7]
def baseStart_3796595 : Nat := 118140960795 + 3796595 * 2 ^ 59
def prefixEnd_3796595 : Nat := 4983230072969 + 3 ^ 40 * 3796595 * 2
def baseEnd_3796595 : Nat := 1949478085456678538302283

theorem tailTrace_3796595 : CollatzResearch.WordTrace tailWord_3796595 prefixEnd_3796595 1949478085456678538302283 := by
  unfold tailWord_3796595
  simp only [CollatzResearch.WordTrace]
  refine ⟨138473195680592196648807239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92315463787061464432538159 138473195680592196648807239)
  ·
    refine ⟨207709793520888294973210859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138473195680592196648807239 207709793520888294973210859)
    ·
      refine ⟨311564690281332442459816289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207709793520888294973210859 311564690281332442459816289)
      ·
        refine ⟨233673517710999331844862217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311564690281332442459816289 233673517710999331844862217)
        ·
          refine ⟨175255138283249498883646663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233673517710999331844862217 175255138283249498883646663)
          ·
            refine ⟨262882707424874248325469995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175255138283249498883646663 262882707424874248325469995)
            ·
              refine ⟨394324061137311372488204993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262882707424874248325469995 394324061137311372488204993)
              ·
                refine ⟨295743045852983529366153745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394324061137311372488204993 295743045852983529366153745)
                ·
                  refine ⟨221807284389737647024615309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295743045852983529366153745 221807284389737647024615309)
                  ·
                    refine ⟨83177731646151617634230741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221807284389737647024615309 83177731646151617634230741)
                    ·
                      refine ⟨1949478085456678538302283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83177731646151617634230741 1949478085456678538302283)
                      ·
                        rfl

theorem cell23_3796595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_3796595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796595 prefixEnd_3796595 := by exact prefixLift 3796595
  have htrace : WordTrace (prefixWord ++ tailWord_3796595) baseStart_3796595 baseEnd_3796595 := by
    simpa [prefixWord, tailWord_3796595, baseEnd_3796595] using wordTrace_append hprefix tailTrace_3796595
  have hstable : (prefixWord ++ tailWord_3796595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796595).length < 2 ^ (prefixWord ++ tailWord_3796595).sum := by decide
  have hdescent : baseEnd_3796595 < baseStart_3796595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796632 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 1, 8]
def baseStart_3796632 : Nat := 118140960795 + 3796632 * 2 ^ 59
def prefixEnd_3796632 : Nat := 4983230072969 + 3 ^ 40 * 3796632 * 2
def baseEnd_3796632 : Nat := 649832361413631631179871

theorem tailTrace_3796632 : CollatzResearch.WordTrace tailWord_3796632 prefixEnd_3796632 649832361413631631179871 := by
  unfold tailWord_3796632
  simp only [CollatzResearch.WordTrace]
  refine ⟨69237272590729075983952075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92316363454305434645269433 69237272590729075983952075)
  ·
    refine ⟨103855908886093613975928113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69237272590729075983952075 103855908886093613975928113)
    ·
      refine ⟨77891931664570210481946085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103855908886093613975928113 77891931664570210481946085)
      ·
        refine ⟨14604737187106914465364891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77891931664570210481946085 14604737187106914465364891)
        ·
          refine ⟨21907105780660371698047337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14604737187106914465364891 21907105780660371698047337)
          ·
            refine ⟨16430329335495278773535503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21907105780660371698047337 16430329335495278773535503)
            ·
              refine ⟨24645494003242918160303255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16430329335495278773535503 24645494003242918160303255)
              ·
                refine ⟨36968241004864377240454883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24645494003242918160303255 36968241004864377240454883)
                ·
                  refine ⟨55452361507296565860682325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36968241004864377240454883 55452361507296565860682325)
                  ·
                    refine ⟨649832361413631631179871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55452361507296565860682325 649832361413631631179871)
                    ·
                      rfl

theorem cell23_3796632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_3796632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796632 prefixEnd_3796632 := by exact prefixLift 3796632
  have htrace : WordTrace (prefixWord ++ tailWord_3796632) baseStart_3796632 baseEnd_3796632 := by
    simpa [prefixWord, tailWord_3796632, baseEnd_3796632] using wordTrace_append hprefix tailTrace_3796632
  have hstable : (prefixWord ++ tailWord_3796632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796632).length < 2 ^ (prefixWord ++ tailWord_3796632).sum := by decide
  have hdescent : baseEnd_3796632 < baseStart_3796632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796679 : List Nat := [1, 1, 4, 1, 1, 1, 3, 6, 5]
def baseStart_3796679 : Nat := 118140960795 + 3796679 * 2 ^ 59
def prefixEnd_3796679 : Nat := 4983230072969 + 3 ^ 40 * 3796679 * 2
def baseEnd_3796679 : Nat := 216613468647961801072433

theorem tailTrace_3796679 : CollatzResearch.WordTrace tailWord_3796679 prefixEnd_3796679 216613468647961801072433 := by
  unfold tailWord_3796679
  simp only [CollatzResearch.WordTrace]
  refine ⟨138476259412287878994865091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92317506274858585996576727 138476259412287878994865091)
  ·
    refine ⟨207714389118431818492297637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138476259412287878994865091 207714389118431818492297637)
    ·
      refine ⟨38946447959705965967305807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207714389118431818492297637 38946447959705965967305807)
      ·
        refine ⟨58419671939558948950958711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38946447959705965967305807 58419671939558948950958711)
        ·
          refine ⟨87629507909338423426438067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58419671939558948950958711 87629507909338423426438067)
          ·
            refine ⟨131444261864007635139657101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87629507909338423426438067 131444261864007635139657101)
            ·
              refine ⟨49291598199002863177371413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131444261864007635139657101 49291598199002863177371413)
              ·
                refine ⟨2310543665578259211439285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49291598199002863177371413 2310543665578259211439285)
                ·
                  refine ⟨216613468647961801072433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2310543665578259211439285 216613468647961801072433)
                  ·
                    rfl

theorem cell23_3796679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 5].length) (baseStart_3796679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796679 prefixEnd_3796679 := by exact prefixLift 3796679
  have htrace : WordTrace (prefixWord ++ tailWord_3796679) baseStart_3796679 baseEnd_3796679 := by
    simpa [prefixWord, tailWord_3796679, baseEnd_3796679] using wordTrace_append hprefix tailTrace_3796679
  have hstable : (prefixWord ++ tailWord_3796679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796679).length < 2 ^ (prefixWord ++ tailWord_3796679).sum := by decide
  have hdescent : baseEnd_3796679 < baseStart_3796679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796689 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 2, 3, 3]
def baseStart_3796689 : Nat := 118140960795 + 3796689 * 2 ^ 59
def prefixEnd_3796689 : Nat := 4983230072969 + 3 ^ 40 * 3796689 * 2
def baseEnd_3796689 : Nat := 1949526352638201170526851

theorem tailTrace_3796689 : CollatzResearch.WordTrace tailWord_3796689 prefixEnd_3796689 1949526352638201170526851 := by
  unfold tailWord_3796689
  simp only [CollatzResearch.WordTrace]
  refine ⟨138476624142251650702729121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92317749428167767135152747 138476624142251650702729121)
  ·
    refine ⟨103857468106688738027046841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138476624142251650702729121 103857468106688738027046841)
    ·
      refine ⟨77893101080016553520285131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103857468106688738027046841 77893101080016553520285131)
      ·
        refine ⟨116839651620024830280427697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77893101080016553520285131 116839651620024830280427697)
        ·
          refine ⟨87629738715018622710320773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116839651620024830280427697 87629738715018622710320773)
          ·
            refine ⟨16430576009065991758185145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87629738715018622710320773 16430576009065991758185145)
            ·
              refine ⟨12322932006799493818638859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16430576009065991758185145 12322932006799493818638859)
              ·
                refine ⟨18484398010199240727958289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12322932006799493818638859 18484398010199240727958289)
                ·
                  refine ⟨13863298507649430545968717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18484398010199240727958289 13863298507649430545968717)
                  ·
                    refine ⟨5198736940368536454738269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13863298507649430545968717 5198736940368536454738269)
                    ·
                      refine ⟨1949526352638201170526851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5198736940368536454738269 1949526352638201170526851)
                      ·
                        rfl

theorem cell23_3796689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_3796689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796689 prefixEnd_3796689 := by exact prefixLift 3796689
  have htrace : WordTrace (prefixWord ++ tailWord_3796689) baseStart_3796689 baseEnd_3796689 := by
    simpa [prefixWord, tailWord_3796689, baseEnd_3796689] using wordTrace_append hprefix tailTrace_3796689
  have hstable : (prefixWord ++ tailWord_3796689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796689).length < 2 ^ (prefixWord ++ tailWord_3796689).sum := by decide
  have hdescent : baseEnd_3796689 < baseStart_3796689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796709 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 2, 5]
def baseStart_3796709 : Nat := 118140960795 + 3796709 * 2 ^ 59
def prefixEnd_3796709 : Nat := 4983230072969 + 3 ^ 40 * 3796709 * 2
def baseEnd_3796709 : Nat := 649845540750430364092253

theorem tailTrace_3796709 : CollatzResearch.WordTrace tailWord_3796709 prefixEnd_3796709 649845540750430364092253 := by
  unfold tailWord_3796709
  simp only [CollatzResearch.WordTrace]
  refine ⟨138477353602179194118457181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92318235734786129412304787 138477353602179194118457181)
  ·
    refine ⟨51929007600817197794421443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138477353602179194118457181 51929007600817197794421443)
    ·
      refine ⟨77893511401225796691632165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51929007600817197794421443 77893511401225796691632165)
      ·
        refine ⟨14605033387729836879681031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77893511401225796691632165 14605033387729836879681031)
        ·
          refine ⟨21907550081594755319521547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14605033387729836879681031 21907550081594755319521547)
          ·
            refine ⟨32861325122392132979282321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21907550081594755319521547 32861325122392132979282321)
            ·
              refine ⟨24645993841794099734461741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32861325122392132979282321 24645993841794099734461741)
              ·
                refine ⟨9242247690672787400423153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24645993841794099734461741 9242247690672787400423153)
                ·
                  refine ⟨6931685768004590550317365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9242247690672787400423153 6931685768004590550317365)
                  ·
                    refine ⟨649845540750430364092253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6931685768004590550317365 649845540750430364092253)
                    ·
                      rfl

theorem cell23_3796709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_3796709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796709 prefixEnd_3796709 := by exact prefixLift 3796709
  have htrace : WordTrace (prefixWord ++ tailWord_3796709) baseStart_3796709 baseEnd_3796709 := by
    simpa [prefixWord, tailWord_3796709, baseEnd_3796709] using wordTrace_append hprefix tailTrace_3796709
  have hstable : (prefixWord ++ tailWord_3796709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796709).length < 2 ^ (prefixWord ++ tailWord_3796709).sum := by decide
  have hdescent : baseEnd_3796709 < baseStart_3796709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796726 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_3796726 : Nat := 118140960795 + 3796726 * 2 ^ 59
def prefixEnd_3796726 : Nat := 4983230072969 + 3 ^ 40 * 3796726 * 2
def baseEnd_3796726 : Nat := 649848450474139175254727

theorem tailTrace_3796726 : CollatzResearch.WordTrace tailWord_3796726 prefixEnd_3796726 649848450474139175254727 := by
  unfold tailWord_3796726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654873352694850376364127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92318649095411737347884021 8654873352694850376364127)
  ·
    refine ⟨12982310029042275564546191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8654873352694850376364127 12982310029042275564546191)
    ·
      refine ⟨19473465043563413346819287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12982310029042275564546191 19473465043563413346819287)
      ·
        refine ⟨29210197565345120020228931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19473465043563413346819287 29210197565345120020228931)
        ·
          refine ⟨43815296348017680030343397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29210197565345120020228931 43815296348017680030343397)
          ·
            refine ⟨8215368065253315005689387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43815296348017680030343397 8215368065253315005689387)
            ·
              refine ⟨12323052097879972508534081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8215368065253315005689387 12323052097879972508534081)
              ·
                refine ⟨9242289073409979381400561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12323052097879972508534081 9242289073409979381400561)
                ·
                  refine ⟨6931716805057484536050421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9242289073409979381400561 6931716805057484536050421)
                  ·
                    refine ⟨649848450474139175254727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6931716805057484536050421 649848450474139175254727)
                    ·
                      rfl

theorem cell23_3796726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_3796726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796726 prefixEnd_3796726 := by exact prefixLift 3796726
  have htrace : WordTrace (prefixWord ++ tailWord_3796726) baseStart_3796726 baseEnd_3796726 := by
    simpa [prefixWord, tailWord_3796726, baseEnd_3796726] using wordTrace_append hprefix tailTrace_3796726
  have hstable : (prefixWord ++ tailWord_3796726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796726).length < 2 ^ (prefixWord ++ tailWord_3796726).sum := by decide
  have hdescent : baseEnd_3796726 < baseStart_3796726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796786 : List Nat := [3, 2, 1, 1, 3, 3, 2, 2, 6]
def baseStart_3796786 : Nat := 118140960795 + 3796786 * 2 ^ 59
def prefixEnd_3796786 : Nat := 4983230072969 + 3 ^ 40 * 3796786 * 2
def baseEnd_3796786 : Nat := 216619573362409699001545

theorem tailTrace_3796786 : CollatzResearch.WordTrace tailWord_3796786 prefixEnd_3796786 216619573362409699001545 := by
  unfold tailWord_3796786
  simp only [CollatzResearch.WordTrace]
  refine ⟨34620040505725059067252553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92320108015266824179340141 34620040505725059067252553)
  ·
    refine ⟨25965030379293794300439415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34620040505725059067252553 25965030379293794300439415)
    ·
      refine ⟨38947545568940691450659123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25965030379293794300439415 38947545568940691450659123)
      ·
        refine ⟨58421318353411037175988685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38947545568940691450659123 58421318353411037175988685)
        ·
          refine ⟨21907994382529138940995757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58421318353411037175988685 21907994382529138940995757)
          ·
            refine ⟨8215497893448427102873409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21907994382529138940995757 8215497893448427102873409)
            ·
              refine ⟨6161623420086320327155057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8215497893448427102873409 6161623420086320327155057)
              ·
                refine ⟨4621217565064740245366293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6161623420086320327155057 4621217565064740245366293)
                ·
                  refine ⟨216619573362409699001545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4621217565064740245366293 216619573362409699001545)
                  ·
                    rfl

theorem cell23_3796786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_3796786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796786 prefixEnd_3796786 := by exact prefixLift 3796786
  have htrace : WordTrace (prefixWord ++ tailWord_3796786) baseStart_3796786 baseEnd_3796786 := by
    simpa [prefixWord, tailWord_3796786, baseEnd_3796786] using wordTrace_append hprefix tailTrace_3796786
  have hstable : (prefixWord ++ tailWord_3796786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796786).length < 2 ^ (prefixWord ++ tailWord_3796786).sum := by decide
  have hdescent : baseEnd_3796786 < baseStart_3796786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796823 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 1, 5, 2]
def baseStart_3796823 : Nat := 118140960795 + 3796823 * 2 ^ 59
def prefixEnd_3796823 : Nat := 4983230072969 + 3 ^ 40 * 3796823 * 2
def baseEnd_3796823 : Nat := 1949595159045903646251235

theorem tailTrace_3796823 : CollatzResearch.WordTrace tailWord_3796823 prefixEnd_3796823 1949595159045903646251235 := by
  unfold tailWord_3796823
  simp only [CollatzResearch.WordTrace]
  refine ⟨138481511523766191588107123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92321007682510794392071415 138481511523766191588107123)
  ·
    refine ⟨207722267285649287382160685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138481511523766191588107123 207722267285649287382160685)
    ·
      refine ⟨77895850232118482768310257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207722267285649287382160685 77895850232118482768310257)
      ·
        refine ⟨58421887674088862076232693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77895850232118482768310257 58421887674088862076232693)
        ·
          refine ⟨5477051969445830819646815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58421887674088862076232693 5477051969445830819646815)
          ·
            refine ⟨8215577954168746229470223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5477051969445830819646815 8215577954168746229470223)
            ·
              refine ⟨12323366931253119344205335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8215577954168746229470223 12323366931253119344205335)
              ·
                refine ⟨18485050396879679016308003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12323366931253119344205335 18485050396879679016308003)
                ·
                  refine ⟨27727575595319518524462005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18485050396879679016308003 27727575595319518524462005)
                  ·
                    refine ⟨2599460212061204861668313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27727575595319518524462005 2599460212061204861668313)
                    ·
                      refine ⟨1949595159045903646251235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2599460212061204861668313 1949595159045903646251235)
                      ·
                        rfl

theorem cell23_3796823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_3796823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796823 prefixEnd_3796823 := by exact prefixLift 3796823
  have htrace : WordTrace (prefixWord ++ tailWord_3796823) baseStart_3796823 baseEnd_3796823 := by
    simpa [prefixWord, tailWord_3796823, baseEnd_3796823] using wordTrace_append hprefix tailTrace_3796823
  have hstable : (prefixWord ++ tailWord_3796823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796823).length < 2 ^ (prefixWord ++ tailWord_3796823).sum := by decide
  have hdescent : baseEnd_3796823 < baseStart_3796823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796849 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_3796849 : Nat := 118140960795 + 3796849 * 2 ^ 59
def prefixEnd_3796849 : Nat := 4983230072969 + 3 ^ 40 * 3796849 * 2
def baseEnd_3796849 : Nat := 1949608509542920544526115

theorem tailTrace_3796849 : CollatzResearch.WordTrace tailWord_3796849 prefixEnd_3796849 1949608509542920544526115 := by
  unfold tailWord_3796849
  simp only [CollatzResearch.WordTrace]
  refine ⟨138482459821671998028553601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92321639881114665352369067 138482459821671998028553601)
  ·
    refine ⟨103861844866253998521415201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138482459821671998028553601 103861844866253998521415201)
    ·
      refine ⟨77896383649690498891061401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103861844866253998521415201 77896383649690498891061401)
      ·
        refine ⟨58422287737267874168296051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77896383649690498891061401 58422287737267874168296051)
        ·
          refine ⟨87633431605901811252444077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58422287737267874168296051 87633431605901811252444077)
          ·
            refine ⟨32862536852213179219666529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87633431605901811252444077 32862536852213179219666529)
            ·
              refine ⟨24646902639159884414749897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32862536852213179219666529 24646902639159884414749897)
              ·
                refine ⟨18485176979369913311062423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24646902639159884414749897 18485176979369913311062423)
                ·
                  refine ⟨27727765469054869966593635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18485176979369913311062423 27727765469054869966593635)
                  ·
                    refine ⟨41591648203582304949890453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27727765469054869966593635 41591648203582304949890453)
                    ·
                      refine ⟨1949608509542920544526115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41591648203582304949890453 1949608509542920544526115)
                      ·
                        rfl

theorem cell23_3796849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_3796849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796849 prefixEnd_3796849 := by exact prefixLift 3796849
  have htrace : WordTrace (prefixWord ++ tailWord_3796849) baseStart_3796849 baseEnd_3796849 := by
    simpa [prefixWord, tailWord_3796849, baseEnd_3796849] using wordTrace_append hprefix tailTrace_3796849
  have hstable : (prefixWord ++ tailWord_3796849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796849).length < 2 ^ (prefixWord ++ tailWord_3796849).sum := by decide
  have hdescent : baseEnd_3796849 < baseStart_3796849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796873 : List Nat := [1, 2, 1, 1, 5, 1, 4, 2, 1, 2, 3]
def baseStart_3796873 : Nat := 118140960795 + 3796873 * 2 ^ 59
def prefixEnd_3796873 : Nat := 4983230072969 + 3 ^ 40 * 3796873 * 2
def baseEnd_3796873 : Nat := 1949620833078628450626005

theorem tailTrace_3796873 : CollatzResearch.WordTrace tailWord_3796873 prefixEnd_3796873 1949620833078628450626005 := by
  unfold tailWord_3796873
  simp only [CollatzResearch.WordTrace]
  refine ⟨138483335173585050127427273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92322223449056700084951515 138483335173585050127427273)
  ·
    refine ⟨103862501380188787595570455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138483335173585050127427273 103862501380188787595570455)
    ·
      refine ⟨155793752070283181393355683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103862501380188787595570455 155793752070283181393355683)
      ·
        refine ⟨233690628105424772090033525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155793752070283181393355683 233690628105424772090033525)
        ·
          refine ⟨21908496384883572383440643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233690628105424772090033525 21908496384883572383440643)
          ·
            refine ⟨32862744577325358575160965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21908496384883572383440643 32862744577325358575160965)
            ·
              refine ⟨6161764608248504732842681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32862744577325358575160965 6161764608248504732842681)
              ·
                refine ⟨4621323456186378549632011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6161764608248504732842681 4621323456186378549632011)
                ·
                  refine ⟨6931985184279567824448017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4621323456186378549632011 6931985184279567824448017)
                  ·
                    refine ⟨5198988888209675868336013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6931985184279567824448017 5198988888209675868336013)
                    ·
                      refine ⟨1949620833078628450626005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5198988888209675868336013 1949620833078628450626005)
                      ·
                        rfl

theorem cell23_3796873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 2, 3].length) (baseStart_3796873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796873 prefixEnd_3796873 := by exact prefixLift 3796873
  have htrace : WordTrace (prefixWord ++ tailWord_3796873) baseStart_3796873 baseEnd_3796873 := by
    simpa [prefixWord, tailWord_3796873, baseEnd_3796873] using wordTrace_append hprefix tailTrace_3796873
  have hstable : (prefixWord ++ tailWord_3796873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796873).length < 2 ^ (prefixWord ++ tailWord_3796873).sum := by decide
  have hdescent : baseEnd_3796873 < baseStart_3796873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796887 : List Nat := [1, 1, 3, 3, 1, 3, 3, 3, 1, 2, 2]
def baseStart_3796887 : Nat := 118140960795 + 3796887 * 2 ^ 59
def prefixEnd_3796887 : Nat := 4983230072969 + 3 ^ 40 * 3796887 * 2
def baseEnd_3796887 : Nat := 1949628021807791395850941

theorem tailTrace_3796887 : CollatzResearch.WordTrace tailWord_3796887 prefixEnd_3796887 1949628021807791395850941 := by
  unfold tailWord_3796887
  simp only [CollatzResearch.WordTrace]
  refine ⟨138483845795534330518436915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92322563863689553678957943 138483845795534330518436915)
  ·
    refine ⟨207725768693301495777655373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138483845795534330518436915 207725768693301495777655373)
    ·
      refine ⟨77897163259988060916620765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207725768693301495777655373 77897163259988060916620765)
      ·
        refine ⟨29211436222495522843732787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77897163259988060916620765 29211436222495522843732787)
        ·
          refine ⟨43817154333743284265599181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29211436222495522843732787 43817154333743284265599181)
          ·
            refine ⟨16431432875153731599599693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43817154333743284265599181 16431432875153731599599693)
            ·
              refine ⟨6161787328182649349849885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16431432875153731599599693 6161787328182649349849885)
              ·
                refine ⟨2310670248068493506193707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6161787328182649349849885 2310670248068493506193707)
                ·
                  refine ⟨3466005372102740259290561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310670248068493506193707 3466005372102740259290561)
                  ·
                    refine ⟨2599504029077055194467921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3466005372102740259290561 2599504029077055194467921)
                    ·
                      refine ⟨1949628021807791395850941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2599504029077055194467921 1949628021807791395850941)
                      ·
                        rfl

theorem cell23_3796887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_3796887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796887 prefixEnd_3796887 := by exact prefixLift 3796887
  have htrace : WordTrace (prefixWord ++ tailWord_3796887) baseStart_3796887 baseEnd_3796887 := by
    simpa [prefixWord, tailWord_3796887, baseEnd_3796887] using wordTrace_append hprefix tailTrace_3796887
  have hstable : (prefixWord ++ tailWord_3796887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796887).length < 2 ^ (prefixWord ++ tailWord_3796887).sum := by decide
  have hdescent : baseEnd_3796887 < baseStart_3796887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796899 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 5]
def baseStart_3796899 : Nat := 118140960795 + 3796899 * 2 ^ 59
def prefixEnd_3796899 : Nat := 4983230072969 + 3 ^ 40 * 3796899 * 2
def baseEnd_3796899 : Nat := 1949634183575645348900885

theorem tailTrace_3796899 : CollatzResearch.WordTrace tailWord_3796899 prefixEnd_3796899 1949634183575645348900885 := by
  unfold tailWord_3796899
  simp only [CollatzResearch.WordTrace]
  refine ⟨138484283471490856567873751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92322855647660571045249167 138484283471490856567873751)
  ·
    refine ⟨207726425207236284851810627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138484283471490856567873751 207726425207236284851810627)
    ·
      refine ⟨311589637810854427277715941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207726425207236284851810627 311589637810854427277715941)
      ·
        refine ⟨58423057089535205114571739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311589637810854427277715941 58423057089535205114571739)
        ·
          refine ⟨87634585634302807671857609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58423057089535205114571739 87634585634302807671857609)
          ·
            refine ⟨65725939225727105753893207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87634585634302807671857609 65725939225727105753893207)
            ·
              refine ⟨98588908838590658630839811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65725939225727105753893207 98588908838590658630839811)
              ·
                refine ⟨147883363257885987946259717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98588908838590658630839811 147883363257885987946259717)
                ·
                  refine ⟨27728130610853622739923697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147883363257885987946259717 27728130610853622739923697)
                  ·
                    refine ⟨20796097958140217054942773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27728130610853622739923697 20796097958140217054942773)
                    ·
                      refine ⟨1949634183575645348900885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20796097958140217054942773 1949634183575645348900885)
                      ·
                        rfl

theorem cell23_3796899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_3796899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796899 prefixEnd_3796899 := by exact prefixLift 3796899
  have htrace : WordTrace (prefixWord ++ tailWord_3796899) baseStart_3796899 baseEnd_3796899 := by
    simpa [prefixWord, tailWord_3796899, baseEnd_3796899] using wordTrace_append hprefix tailTrace_3796899
  have hstable : (prefixWord ++ tailWord_3796899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796899).length < 2 ^ (prefixWord ++ tailWord_3796899).sum := by decide
  have hdescent : baseEnd_3796899 < baseStart_3796899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796919 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 1, 8]
def baseStart_3796919 : Nat := 118140960795 + 3796919 * 2 ^ 59
def prefixEnd_3796919 : Nat := 4983230072969 + 3 ^ 40 * 3796919 * 2
def baseEnd_3796919 : Nat := 649881484396245090216931

theorem tailTrace_3796919 : CollatzResearch.WordTrace tailWord_3796919 prefixEnd_3796919 649881484396245090216931 := by
  unfold tailWord_3796919
  simp only [CollatzResearch.WordTrace]
  refine ⟨138485012931418399983601811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92323341954278933322401207 138485012931418399983601811)
  ·
    refine ⟨207727519397127599975402717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138485012931418399983601811 207727519397127599975402717)
    ·
      refine ⟨77897819773922849990776019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207727519397127599975402717 77897819773922849990776019)
      ·
        refine ⟨116846729660884274986164029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77897819773922849990776019 116846729660884274986164029)
        ·
          refine ⟨43817523622831603119811511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116846729660884274986164029 43817523622831603119811511)
          ·
            refine ⟨65726285434247404679717267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43817523622831603119811511 65726285434247404679717267)
            ·
              refine ⟨98589428151371107019575901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65726285434247404679717267 98589428151371107019575901)
              ·
                refine ⟨36971035556764165132340963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98589428151371107019575901 36971035556764165132340963)
                ·
                  refine ⟨55456553335146247698511445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36971035556764165132340963 55456553335146247698511445)
                  ·
                    refine ⟨649881484396245090216931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55456553335146247698511445 649881484396245090216931)
                    ·
                      rfl

theorem cell23_3796919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_3796919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796919 prefixEnd_3796919 := by exact prefixLift 3796919
  have htrace : WordTrace (prefixWord ++ tailWord_3796919) baseStart_3796919 baseEnd_3796919 := by
    simpa [prefixWord, tailWord_3796919, baseEnd_3796919] using wordTrace_append hprefix tailTrace_3796919
  have hstable : (prefixWord ++ tailWord_3796919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796919).length < 2 ^ (prefixWord ++ tailWord_3796919).sum := by decide
  have hdescent : baseEnd_3796919 < baseStart_3796919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796924 : List Nat := [2, 2, 2, 5, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3796924 : Nat := 118140960795 + 3796924 * 2 ^ 59
def prefixEnd_3796924 : Nat := 4983230072969 + 3 ^ 40 * 3796924 * 2
def baseEnd_3796924 : Nat := 1949647020592007751088271

theorem tailTrace_3796924 : CollatzResearch.WordTrace tailWord_3796924 prefixEnd_3796924 1949647020592007751088271 := by
  unfold tailWord_3796924
  simp only [CollatzResearch.WordTrace]
  refine ⟨69242597648200142918766913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92323463530933523891689217 69242597648200142918766913)
  ·
    refine ⟨51931948236150107189075185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69242597648200142918766913 51931948236150107189075185)
    ·
      refine ⟨38948961177112580391806389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51931948236150107189075185 38948961177112580391806389)
      ·
        refine ⟨3651465110354304411731849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38948961177112580391806389 3651465110354304411731849)
        ·
          refine ⟨2738598832765728308798887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3651465110354304411731849 2738598832765728308798887)
          ·
            refine ⟨4107898249148592463198331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738598832765728308798887 4107898249148592463198331)
            ·
              refine ⟨6161847373722888694797497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4107898249148592463198331 6161847373722888694797497)
              ·
                refine ⟨4621385530292166521098123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6161847373722888694797497 4621385530292166521098123)
                ·
                  refine ⟨6932078295438249781647185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4621385530292166521098123 6932078295438249781647185)
                  ·
                    refine ⟨5199058721578687336235389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6932078295438249781647185 5199058721578687336235389)
                    ·
                      refine ⟨1949647020592007751088271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5199058721578687336235389 1949647020592007751088271)
                      ·
                        rfl

theorem cell23_3796924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3796924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796924 prefixEnd_3796924 := by exact prefixLift 3796924
  have htrace : WordTrace (prefixWord ++ tailWord_3796924) baseStart_3796924 baseEnd_3796924 := by
    simpa [prefixWord, tailWord_3796924, baseEnd_3796924] using wordTrace_append hprefix tailTrace_3796924
  have hstable : (prefixWord ++ tailWord_3796924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796924).length < 2 ^ (prefixWord ++ tailWord_3796924).sum := by decide
  have hdescent : baseEnd_3796924 < baseStart_3796924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796943 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 1, 4, 2]
def baseStart_3796943 : Nat := 118140960795 + 3796943 * 2 ^ 59
def prefixEnd_3796943 : Nat := 4983230072969 + 3 ^ 40 * 3796943 * 2
def baseEnd_3796943 : Nat := 1949656776724443176750683

theorem tailTrace_3796943 : CollatzResearch.WordTrace tailWord_3796943 prefixEnd_3796943 1949656776724443176750683 := by
  unfold tailWord_3796943
  simp only [CollatzResearch.WordTrace]
  refine ⟨138485888283331452082475483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92323925522220968054983655 138485888283331452082475483)
  ·
    refine ⟨207728832424997178123713225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138485888283331452082475483 207728832424997178123713225)
    ·
      refine ⟨155796624318747883592784919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207728832424997178123713225 155796624318747883592784919)
      ·
        refine ⟨233694936478121825389177379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155796624318747883592784919 233694936478121825389177379)
        ·
          refine ⟨350542404717182738083766069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233694936478121825389177379 350542404717182738083766069)
          ·
            refine ⟨32863350442235881695353069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 350542404717182738083766069 32863350442235881695353069)
            ·
              refine ⟨12323756415838455635757401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32863350442235881695353069 12323756415838455635757401)
              ·
                refine ⟨9242817311878841726818051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12323756415838455635757401 9242817311878841726818051)
                ·
                  refine ⟨13864225967818262590227077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9242817311878841726818051 13864225967818262590227077)
                  ·
                    refine ⟨2599542368965924235667577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13864225967818262590227077 2599542368965924235667577)
                    ·
                      refine ⟨1949656776724443176750683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2599542368965924235667577 1949656776724443176750683)
                      ·
                        rfl

theorem cell23_3796943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 4, 2].length) (baseStart_3796943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796943 prefixEnd_3796943 := by exact prefixLift 3796943
  have htrace : WordTrace (prefixWord ++ tailWord_3796943) baseStart_3796943 baseEnd_3796943 := by
    simpa [prefixWord, tailWord_3796943, baseEnd_3796943] using wordTrace_append hprefix tailTrace_3796943
  have hstable : (prefixWord ++ tailWord_3796943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796943).length < 2 ^ (prefixWord ++ tailWord_3796943).sum := by decide
  have hdescent : baseEnd_3796943 < baseStart_3796943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796976 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 3]
def baseStart_3796976 : Nat := 118140960795 + 3796976 * 2 ^ 59
def prefixEnd_3796976 : Nat := 4983230072969 + 3 ^ 40 * 3796976 * 2
def baseEnd_3796976 : Nat := 1949673721586041547638031

theorem tailTrace_3796976 : CollatzResearch.WordTrace tailWord_3796976 prefixEnd_3796976 1949673721586041547638031 := by
  unfold tailWord_3796976
  simp only [CollatzResearch.WordTrace]
  refine ⟨69243545946105949359213391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92324727928141265812284521 69243545946105949359213391)
  ·
    refine ⟨103865318919158924038820087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69243545946105949359213391 103865318919158924038820087)
    ·
      refine ⟨155797978378738386058230131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103865318919158924038820087 155797978378738386058230131)
      ·
        refine ⟨233696967568107579087345197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155797978378738386058230131 233696967568107579087345197)
        ·
          refine ⟨87636362838040342157754449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233696967568107579087345197 87636362838040342157754449)
          ·
            refine ⟨65727272128530256618315837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87636362838040342157754449 65727272128530256618315837)
            ·
              refine ⟨24647727048198846231868439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65727272128530256618315837 24647727048198846231868439)
              ·
                refine ⟨36971590572298269347802659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24647727048198846231868439 36971590572298269347802659)
                ·
                  refine ⟨55457385858447404021703989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36971590572298269347802659 55457385858447404021703989)
                  ·
                    refine ⟨5199129924229444127034749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55457385858447404021703989 5199129924229444127034749)
                    ·
                      refine ⟨1949673721586041547638031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5199129924229444127034749 1949673721586041547638031)
                      ·
                        rfl

theorem cell23_3796976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 3].length) (baseStart_3796976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796976 prefixEnd_3796976 := by exact prefixLift 3796976
  have htrace : WordTrace (prefixWord ++ tailWord_3796976) baseStart_3796976 baseEnd_3796976 := by
    simpa [prefixWord, tailWord_3796976, baseEnd_3796976] using wordTrace_append hprefix tailTrace_3796976
  have hstable : (prefixWord ++ tailWord_3796976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796976).length < 2 ^ (prefixWord ++ tailWord_3796976).sum := by decide
  have hdescent : baseEnd_3796976 < baseStart_3796976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796998 : List Nat := [6, 2, 1, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3796998 : Nat := 118140960795 + 3796998 * 2 ^ 59
def prefixEnd_3796998 : Nat := 4983230072969 + 3 ^ 40 * 3796998 * 2
def baseEnd_3796998 : Nat := 1949685018160440461562931

theorem tailTrace_3796998 : CollatzResearch.WordTrace tailWord_3796998 prefixEnd_3796998 1949685018160440461562931 := by
  unfold tailWord_3796998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4327746696816631139866489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92325262865421464317151765 4327746696816631139866489)
  ·
    refine ⟨3245810022612473354899867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4327746696816631139866489 3245810022612473354899867)
    ·
      refine ⟨4868715033918710032349801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3245810022612473354899867 4868715033918710032349801)
      ·
        refine ⟨3651536275439032524262351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4868715033918710032349801 3651536275439032524262351)
        ·
          refine ⟨5477304413158548786393527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3651536275439032524262351 5477304413158548786393527)
          ·
            refine ⟨8215956619737823179590291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5477304413158548786393527 8215956619737823179590291)
            ·
              refine ⟨12323934929606734769385437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8215956619737823179590291 12323934929606734769385437)
              ·
                refine ⟨4621475598602525538519539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12323934929606734769385437 4621475598602525538519539)
                ·
                  refine ⟨6932213397903788307779309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4621475598602525538519539 6932213397903788307779309)
                  ·
                    refine ⟨2599580024213920615417241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6932213397903788307779309 2599580024213920615417241)
                    ·
                      refine ⟨1949685018160440461562931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2599580024213920615417241 1949685018160440461562931)
                      ·
                        rfl

theorem cell23_3796998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3796998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3796998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3796998 prefixEnd_3796998 := by exact prefixLift 3796998
  have htrace : WordTrace (prefixWord ++ tailWord_3796998) baseStart_3796998 baseEnd_3796998 := by
    simpa [prefixWord, tailWord_3796998, baseEnd_3796998] using wordTrace_append hprefix tailTrace_3796998
  have hstable : (prefixWord ++ tailWord_3796998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796998).length < 2 ^ (prefixWord ++ tailWord_3796998).sum := by decide
  have hdescent : baseEnd_3796998 < baseStart_3796998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797043 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 3, 4]
def baseStart_3797043 : Nat := 118140960795 + 3797043 * 2 ^ 59
def prefixEnd_3797043 : Nat := 4983230072969 + 3 ^ 40 * 3797043 * 2
def baseEnd_3797043 : Nat := 649902708263297595166741

theorem tailTrace_3797043 : CollatzResearch.WordTrace tailWord_3797043 prefixEnd_3797043 649902708263297595166741 := by
  unfold tailWord_3797043
  simp only [CollatzResearch.WordTrace]
  refine ⟨138489535582969169161115783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92326357055312779440743855 138489535582969169161115783)
  ·
    refine ⟨207734303374453753741673675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138489535582969169161115783 207734303374453753741673675)
    ·
      refine ⟨311601455061680630612510513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207734303374453753741673675 311601455061680630612510513)
      ·
        refine ⟨233701091296260472959382885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311601455061680630612510513 233701091296260472959382885)
        ·
          refine ⟨43818954618048838679884291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233701091296260472959382885 43818954618048838679884291)
          ·
            refine ⟨65728431927073258019826437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43818954618048838679884291 65728431927073258019826437)
            ·
              refine ⟨12324080986326235878717457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65728431927073258019826437 12324080986326235878717457)
              ·
                refine ⟨9243060739744676909038093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12324080986326235878717457 9243060739744676909038093)
                ·
                  refine ⟨3466147777404253840889285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9243060739744676909038093 3466147777404253840889285)
                  ·
                    refine ⟨649902708263297595166741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3466147777404253840889285 649902708263297595166741)
                    ·
                      rfl

theorem cell23_3797043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 4].length) (baseStart_3797043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797043 prefixEnd_3797043 := by exact prefixLift 3797043
  have htrace : WordTrace (prefixWord ++ tailWord_3797043) baseStart_3797043 baseEnd_3797043 := by
    simpa [prefixWord, tailWord_3797043, baseEnd_3797043] using wordTrace_append hprefix tailTrace_3797043
  have hstable : (prefixWord ++ tailWord_3797043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797043).length < 2 ^ (prefixWord ++ tailWord_3797043).sum := by decide
  have hdescent : baseEnd_3797043 < baseStart_3797043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797053 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_3797053 : Nat := 118140960795 + 3797053 * 2 ^ 59
def prefixEnd_3797053 : Nat := 4983230072969 + 3 ^ 40 * 3797053 * 2
def baseEnd_3797053 : Nat := 1949713259596437746375177

theorem tailTrace_3797053 : CollatzResearch.WordTrace tailWord_3797053 prefixEnd_3797053 1949713259596437746375177 := by
  unfold tailWord_3797053
  simp only [CollatzResearch.WordTrace]
  refine ⟨138489900312932940868979813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92326600208621960579319875 138489900312932940868979813)
  ·
    refine ⟨25966856308674926412933715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138489900312932940868979813 25966856308674926412933715)
    ·
      refine ⟨38950284463012389619400573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25966856308674926412933715 38950284463012389619400573)
      ·
        refine ⟨14606356673629646107275215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38950284463012389619400573 14606356673629646107275215)
        ·
          refine ⟨21909535010444469160912823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14606356673629646107275215 21909535010444469160912823)
          ·
            refine ⟨32864302515666703741369235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21909535010444469160912823 32864302515666703741369235)
            ·
              refine ⟨49296453773500055612053853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32864302515666703741369235 49296453773500055612053853)
              ·
                refine ⟨18486170165062520854520195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49296453773500055612053853 18486170165062520854520195)
                ·
                  refine ⟨27729255247593781281780293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18486170165062520854520195 27729255247593781281780293)
                  ·
                    refine ⟨5199235358923833990333805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27729255247593781281780293 5199235358923833990333805)
                    ·
                      refine ⟨1949713259596437746375177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5199235358923833990333805 1949713259596437746375177)
                      ·
                        rfl

theorem cell23_3797053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_3797053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797053 prefixEnd_3797053 := by exact prefixLift 3797053
  have htrace : WordTrace (prefixWord ++ tailWord_3797053) baseStart_3797053 baseEnd_3797053 := by
    simpa [prefixWord, tailWord_3797053, baseEnd_3797053] using wordTrace_append hprefix tailTrace_3797053
  have hstable : (prefixWord ++ tailWord_3797053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797053).length < 2 ^ (prefixWord ++ tailWord_3797053).sum := by decide
  have hdescent : baseEnd_3797053 < baseStart_3797053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797056 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 8]
def baseStart_3797056 : Nat := 118140960795 + 3797056 * 2 ^ 59
def prefixEnd_3797056 : Nat := 4983230072969 + 3 ^ 40 * 3797056 * 2
def baseEnd_3797056 : Nat := 216634977782044581626407

theorem tailTrace_3797056 : CollatzResearch.WordTrace tailWord_3797056 prefixEnd_3797056 216634977782044581626407 := by
  unfold tailWord_3797056
  simp only [CollatzResearch.WordTrace]
  refine ⟨69245004865961036190669511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92326673154614714920892681 69245004865961036190669511)
  ·
    refine ⟨103867507298941554286004267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69245004865961036190669511 103867507298941554286004267)
    ·
      refine ⟨155801260948412331429006401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103867507298941554286004267 155801260948412331429006401)
      ·
        refine ⟨116850945711309248571754801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155801260948412331429006401 116850945711309248571754801)
        ·
          refine ⟨87638209283481936428816101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116850945711309248571754801 87638209283481936428816101)
          ·
            refine ⟨16432164240652863080403019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87638209283481936428816101 16432164240652863080403019)
            ·
              refine ⟨24648246360979294620604529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16432164240652863080403019 24648246360979294620604529)
              ·
                refine ⟨18486184770734470965453397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24648246360979294620604529 18486184770734470965453397)
                ·
                  refine ⟨216634977782044581626407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18486184770734470965453397 216634977782044581626407)
                  ·
                    rfl

theorem cell23_3797056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 8].length) (baseStart_3797056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797056 prefixEnd_3797056 := by exact prefixLift 3797056
  have htrace : WordTrace (prefixWord ++ tailWord_3797056) baseStart_3797056 baseEnd_3797056 := by
    simpa [prefixWord, tailWord_3797056, baseEnd_3797056] using wordTrace_append hprefix tailTrace_3797056
  have hstable : (prefixWord ++ tailWord_3797056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797056).length < 2 ^ (prefixWord ++ tailWord_3797056).sum := by decide
  have hdescent : baseEnd_3797056 < baseStart_3797056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797070 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_3797070 : Nat := 118140960795 + 3797070 * 2 ^ 59
def prefixEnd_3797070 : Nat := 4983230072969 + 3 ^ 40 * 3797070 * 2
def baseEnd_3797070 : Nat := 1949721988767564179862599

theorem tailTrace_3797070 : CollatzResearch.WordTrace tailWord_3797070 prefixEnd_3797070 1949721988767564179862599 := by
  unfold tailWord_3797070
  simp only [CollatzResearch.WordTrace]
  refine ⟨17311315044233919096543583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92327013569247568514899109 17311315044233919096543583)
  ·
    refine ⟨25966972566350878644815375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17311315044233919096543583 25966972566350878644815375)
    ·
      refine ⟨38950458849526317967223063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25966972566350878644815375 38950458849526317967223063)
      ·
        refine ⟨58425688274289476950834595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38950458849526317967223063 58425688274289476950834595)
        ·
          refine ⟨87638532411434215426251893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58425688274289476950834595 87638532411434215426251893)
          ·
            refine ⟨8216112413571957696211115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87638532411434215426251893 8216112413571957696211115)
            ·
              refine ⟨12324168620357936544316673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8216112413571957696211115 12324168620357936544316673)
              ·
                refine ⟨9243126465268452408237505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12324168620357936544316673 9243126465268452408237505)
                ·
                  refine ⟨6932344848951339306178129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9243126465268452408237505 6932344848951339306178129)
                  ·
                    refine ⟨5199258636713504479633597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6932344848951339306178129 5199258636713504479633597)
                    ·
                      refine ⟨1949721988767564179862599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5199258636713504479633597 1949721988767564179862599)
                      ·
                        rfl

theorem cell23_3797070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_3797070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797070 prefixEnd_3797070 := by exact prefixLift 3797070
  have htrace : WordTrace (prefixWord ++ tailWord_3797070) baseStart_3797070 baseEnd_3797070 := by
    simpa [prefixWord, tailWord_3797070, baseEnd_3797070] using wordTrace_append hprefix tailTrace_3797070
  have hstable : (prefixWord ++ tailWord_3797070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797070).length < 2 ^ (prefixWord ++ tailWord_3797070).sum := by decide
  have hdescent : baseEnd_3797070 < baseStart_3797070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797103 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 3, 5]
def baseStart_3797103 : Nat := 118140960795 + 3797103 * 2 ^ 59
def prefixEnd_3797103 : Nat := 4983230072969 + 3 ^ 40 * 3797103 * 2
def baseEnd_3797103 : Nat := 649912977876387516916649

theorem tailTrace_3797103 : CollatzResearch.WordTrace tailWord_3797103 prefixEnd_3797103 649912977876387516916649 := by
  unfold tailWord_3797103
  simp only [CollatzResearch.WordTrace]
  refine ⟨138491723962751799408299963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92327815975167866272199975 138491723962751799408299963)
  ·
    refine ⟨207737585944127699112449945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138491723962751799408299963 207737585944127699112449945)
    ·
      refine ⟨155803189458095774334337459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207737585944127699112449945 155803189458095774334337459)
      ·
        refine ⟨233704784187143661501506189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155803189458095774334337459 233704784187143661501506189)
        ·
          refine ⟨87639294070178873063064821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233704784187143661501506189 87639294070178873063064821)
          ·
            refine ⟨8216183819079269349662327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87639294070178873063064821 8216183819079269349662327)
            ·
              refine ⟨12324275728618904024493491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8216183819079269349662327 12324275728618904024493491)
              ·
                refine ⟨18486413592928356036740237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12324275728618904024493491 18486413592928356036740237)
                ·
                  refine ⟨6932405097348133513777589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18486413592928356036740237 6932405097348133513777589)
                  ·
                    refine ⟨649912977876387516916649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6932405097348133513777589 649912977876387516916649)
                    ·
                      rfl

theorem cell23_3797103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 5].length) (baseStart_3797103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797103 prefixEnd_3797103 := by exact prefixLift 3797103
  have htrace : WordTrace (prefixWord ++ tailWord_3797103) baseStart_3797103 baseEnd_3797103 := by
    simpa [prefixWord, tailWord_3797103, baseEnd_3797103] using wordTrace_append hprefix tailTrace_3797103
  have hstable : (prefixWord ++ tailWord_3797103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797103).length < 2 ^ (prefixWord ++ tailWord_3797103).sum := by decide
  have hdescent : baseEnd_3797103 < baseStart_3797103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797157 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 3, 2, 2]
def baseStart_3797157 : Nat := 118140960795 + 3797157 * 2 ^ 59
def prefixEnd_3797157 : Nat := 4983230072969 + 3 ^ 40 * 3797157 * 2
def baseEnd_3797157 : Nat := 1949766661584505339474699

theorem tailTrace_3797157 : CollatzResearch.WordTrace tailWord_3797157 prefixEnd_3797157 1949766661584505339474699 := by
  unfold tailWord_3797157
  simp only [CollatzResearch.WordTrace]
  refine ⟨138493693504556166630765725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92329129003037444420510483 138493693504556166630765725)
  ·
    refine ⟨51935135064208562486537147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138493693504556166630765725 51935135064208562486537147)
    ·
      refine ⟨77902702596312843729805721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51935135064208562486537147 77902702596312843729805721)
      ·
        refine ⟨58427026947234632797354291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77902702596312843729805721 58427026947234632797354291)
        ·
          refine ⟨87640540420851949196031437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58427026947234632797354291 87640540420851949196031437)
          ·
            refine ⟨32865202657819480948511789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87640540420851949196031437 32865202657819480948511789)
            ·
              refine ⟨12324450996682305355691921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32865202657819480948511789 12324450996682305355691921)
              ·
                refine ⟨9243338247511729016768941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12324450996682305355691921 9243338247511729016768941)
                ·
                  refine ⟨3466251842816898381288353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9243338247511729016768941 3466251842816898381288353)
                  ·
                    refine ⟨2599688882112673785966265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3466251842816898381288353 2599688882112673785966265)
                    ·
                      refine ⟨1949766661584505339474699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2599688882112673785966265 1949766661584505339474699)
                      ·
                        rfl

theorem cell23_3797157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_3797157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797157 prefixEnd_3797157 := by exact prefixLift 3797157
  have htrace : WordTrace (prefixWord ++ tailWord_3797157) baseStart_3797157 baseEnd_3797157 := by
    simpa [prefixWord, tailWord_3797157, baseEnd_3797157] using wordTrace_append hprefix tailTrace_3797157
  have hstable : (prefixWord ++ tailWord_3797157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797157).length < 2 ^ (prefixWord ++ tailWord_3797157).sum := by decide
  have hdescent : baseEnd_3797157 < baseStart_3797157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797233 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_3797233 : Nat := 118140960795 + 3797233 * 2 ^ 59
def prefixEnd_3797233 : Nat := 4983230072969 + 3 ^ 40 * 3797233 * 2
def baseEnd_3797233 : Nat := 1949805686114247042124349

theorem tailTrace_3797233 : CollatzResearch.WordTrace tailWord_3797233 prefixEnd_3797233 1949805686114247042124349 := by
  unfold tailWord_3797233
  simp only [CollatzResearch.WordTrace]
  refine ⟨138496465452280831610532353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92330976968187221073688235 138496465452280831610532353)
  ·
    refine ⟨103872349089210623707899265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138496465452280831610532353 103872349089210623707899265)
    ·
      refine ⟨77904261816907967780924449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103872349089210623707899265 77904261816907967780924449)
      ·
        refine ⟨58428196362680975835693337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77904261816907967780924449 58428196362680975835693337)
        ·
          refine ⟨43821147272010731876770003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58428196362680975835693337 43821147272010731876770003)
          ·
            refine ⟨65731720908016097815155005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43821147272010731876770003 65731720908016097815155005)
            ·
              refine ⟨24649395340506036680683127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65731720908016097815155005 24649395340506036680683127)
              ·
                refine ⟨36974093010759055021024691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24649395340506036680683127 36974093010759055021024691)
                ·
                  refine ⟨55461139516138582531537037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36974093010759055021024691 55461139516138582531537037)
                  ·
                    refine ⟨20797927318551968449326389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55461139516138582531537037 20797927318551968449326389)
                    ·
                      refine ⟨1949805686114247042124349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20797927318551968449326389 1949805686114247042124349)
                      ·
                        rfl

theorem cell23_3797233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_3797233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797233 prefixEnd_3797233 := by exact prefixLift 3797233
  have htrace : WordTrace (prefixWord ++ tailWord_3797233) baseStart_3797233 baseEnd_3797233 := by
    simpa [prefixWord, tailWord_3797233, baseEnd_3797233] using wordTrace_append hprefix tailTrace_3797233
  have hstable : (prefixWord ++ tailWord_3797233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797233).length < 2 ^ (prefixWord ++ tailWord_3797233).sum := by decide
  have hdescent : baseEnd_3797233 < baseStart_3797233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797234 : List Nat := [3, 2, 1, 3, 2, 1, 2, 3, 1, 3, 2]
def baseStart_3797234 : Nat := 118140960795 + 3797234 * 2 ^ 59
def prefixEnd_3797234 : Nat := 4983230072969 + 3 ^ 40 * 3797234 * 2
def baseEnd_3797234 : Nat := 1949806199594901538211845

theorem tailTrace_3797234 : CollatzResearch.WordTrace tailWord_3797234 prefixEnd_3797234 1949806199594901538211845 := by
  unfold tailWord_3797234
  simp only [CollatzResearch.WordTrace]
  refine ⟨34624125481319302195329689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92331001283518139187545837 34624125481319302195329689)
  ·
    refine ⟨25968094110989476646497267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34624125481319302195329689 25968094110989476646497267)
    ·
      refine ⟨38952141166484214969745901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25968094110989476646497267 38952141166484214969745901)
      ·
        refine ⟨14607052937431580613654713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38952141166484214969745901 14607052937431580613654713)
        ·
          refine ⟨10955289703073685460241035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14607052937431580613654713 10955289703073685460241035)
          ·
            refine ⟨16432934554610528190361553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10955289703073685460241035 16432934554610528190361553)
            ·
              refine ⟨12324700915957896142771165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16432934554610528190361553 12324700915957896142771165)
              ·
                refine ⟨4621762843484211053539187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12324700915957896142771165 4621762843484211053539187)
                ·
                  refine ⟨6932644265226316580308781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4621762843484211053539187 6932644265226316580308781)
                  ·
                    refine ⟨2599741599459868717615793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6932644265226316580308781 2599741599459868717615793)
                    ·
                      refine ⟨1949806199594901538211845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2599741599459868717615793 1949806199594901538211845)
                      ·
                        rfl

theorem cell23_3797234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_3797234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797234 prefixEnd_3797234 := by exact prefixLift 3797234
  have htrace : WordTrace (prefixWord ++ tailWord_3797234) baseStart_3797234 baseEnd_3797234 := by
    simpa [prefixWord, tailWord_3797234, baseEnd_3797234] using wordTrace_append hprefix tailTrace_3797234
  have hstable : (prefixWord ++ tailWord_3797234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797234).length < 2 ^ (prefixWord ++ tailWord_3797234).sum := by decide
  have hdescent : baseEnd_3797234 < baseStart_3797234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797247 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 4, 2, 2]
def baseStart_3797247 : Nat := 118140960795 + 3797247 * 2 ^ 59
def prefixEnd_3797247 : Nat := 4983230072969 + 3 ^ 40 * 3797247 * 2
def baseEnd_3797247 : Nat := 1949812874843409987349285

theorem tailTrace_3797247 : CollatzResearch.WordTrace tailWord_3797247 prefixEnd_3797247 1949812874843409987349285 := by
  unfold tailWord_3797247
  simp only [CollatzResearch.WordTrace]
  refine ⟨138496976074230112001541995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92331317382820074667694663 138496976074230112001541995)
  ·
    refine ⟨207745464111345168002312993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138496976074230112001541995 207745464111345168002312993)
    ·
      refine ⟨155809098083508876001734745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207745464111345168002312993 155809098083508876001734745)
      ·
        refine ⟨116856823562631657001301059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155809098083508876001734745 116856823562631657001301059)
        ·
          refine ⟨175285235343947485501951589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116856823562631657001301059 175285235343947485501951589)
          ·
            refine ⟨32865981626990153531615923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175285235343947485501951589 32865981626990153531615923)
            ·
              refine ⟨49298972440485230297423885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32865981626990153531615923 49298972440485230297423885)
              ·
                refine ⟨18487114665181961361533957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49298972440485230297423885 18487114665181961361533957)
                ·
                  refine ⟨3466333999721617755287617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18487114665181961361533957 3466333999721617755287617)
                  ·
                    refine ⟨2599750499791213316465713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3466333999721617755287617 2599750499791213316465713)
                    ·
                      refine ⟨1949812874843409987349285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2599750499791213316465713 1949812874843409987349285)
                      ·
                        rfl

theorem cell23_3797247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 2, 2].length) (baseStart_3797247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797247 prefixEnd_3797247 := by exact prefixLift 3797247
  have htrace : WordTrace (prefixWord ++ tailWord_3797247) baseStart_3797247 baseEnd_3797247 := by
    simpa [prefixWord, tailWord_3797247, baseEnd_3797247] using wordTrace_append hprefix tailTrace_3797247
  have hstable : (prefixWord ++ tailWord_3797247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797247).length < 2 ^ (prefixWord ++ tailWord_3797247).sum := by decide
  have hdescent : baseEnd_3797247 < baseStart_3797247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797253 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 7]
def baseStart_3797253 : Nat := 118140960795 + 3797253 * 2 ^ 59
def prefixEnd_3797253 : Nat := 4983230072969 + 3 ^ 40 * 3797253 * 2
def baseEnd_3797253 : Nat := 216646217303037440430473

theorem tailTrace_3797253 : CollatzResearch.WordTrace tailWord_3797253 prefixEnd_3797253 216646217303037440430473 := by
  unfold tailWord_3797253
  simp only [CollatzResearch.WordTrace]
  refine ⟨138497194912208375026260413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92331463274805583350840275 138497194912208375026260413)
  ·
    refine ⟨51936448092078140634847655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138497194912208375026260413 51936448092078140634847655)
    ·
      refine ⟨77904672138117210952271483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51936448092078140634847655 77904672138117210952271483)
      ·
        refine ⟨116857008207175816428407225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77904672138117210952271483 116857008207175816428407225)
        ·
          refine ⟨87642756155381862321305419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116857008207175816428407225 87642756155381862321305419)
          ·
            refine ⟨131464134233072793481958129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87642756155381862321305419 131464134233072793481958129)
            ·
              refine ⟨98598100674804595111468597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131464134233072793481958129 98598100674804595111468597)
              ·
                refine ⟨9243571938262930791700181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98598100674804595111468597 9243571938262930791700181)
                ·
                  refine ⟨216646217303037440430473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9243571938262930791700181 216646217303037440430473)
                  ·
                    rfl

theorem cell23_3797253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_3797253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797253 prefixEnd_3797253 := by exact prefixLift 3797253
  have htrace : WordTrace (prefixWord ++ tailWord_3797253) baseStart_3797253 baseEnd_3797253 := by
    simpa [prefixWord, tailWord_3797253, baseEnd_3797253] using wordTrace_append hprefix tailTrace_3797253
  have hstable : (prefixWord ++ tailWord_3797253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797253).length < 2 ^ (prefixWord ++ tailWord_3797253).sum := by decide
  have hdescent : baseEnd_3797253 < baseStart_3797253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797320 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_3797320 : Nat := 118140960795 + 3797320 * 2 ^ 59
def prefixEnd_3797320 : Nat := 4983230072969 + 3 ^ 40 * 3797320 * 2
def baseEnd_3797320 : Nat := 1949850358931188201736449

theorem tailTrace_3797320 : CollatzResearch.WordTrace tailWord_3797320 prefixEnd_3797320 1949850358931188201736449 := by
  unfold tailWord_3797320
  simp only [CollatzResearch.WordTrace]
  refine ⟨69249819301482822734474707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92333092401977096979299609 69249819301482822734474707)
  ·
    refine ⟨103874728952224234101712061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69249819301482822734474707 103874728952224234101712061)
    ·
      refine ⟨38953023357084087788142023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103874728952224234101712061 38953023357084087788142023)
      ·
        refine ⟨58429535035626131682213035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38953023357084087788142023 58429535035626131682213035)
        ·
          refine ⟨87644302553439197523319553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58429535035626131682213035 87644302553439197523319553)
          ·
            refine ⟨65733226915079398142489665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87644302553439197523319553 65733226915079398142489665)
            ·
              refine ⟨49299920186309548606867249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65733226915079398142489665 49299920186309548606867249)
              ·
                refine ⟨36974940139732161455150437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49299920186309548606867249 36974940139732161455150437)
                ·
                  refine ⟨6932801276199780272840707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36974940139732161455150437 6932801276199780272840707)
                  ·
                    refine ⟨10399201914299670409261061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6932801276199780272840707 10399201914299670409261061)
                    ·
                      refine ⟨1949850358931188201736449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10399201914299670409261061 1949850358931188201736449)
                      ·
                        rfl

theorem cell23_3797320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_3797320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797320 prefixEnd_3797320 := by exact prefixLift 3797320
  have htrace : WordTrace (prefixWord ++ tailWord_3797320) baseStart_3797320 baseEnd_3797320 := by
    simpa [prefixWord, tailWord_3797320, baseEnd_3797320] using wordTrace_append hprefix tailTrace_3797320
  have hstable : (prefixWord ++ tailWord_3797320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797320).length < 2 ^ (prefixWord ++ tailWord_3797320).sum := by decide
  have hdescent : baseEnd_3797320 < baseStart_3797320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797354 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_3797354 : Nat := 118140960795 + 3797354 * 2 ^ 59
def prefixEnd_3797354 : Nat := 4983230072969 + 3 ^ 40 * 3797354 * 2
def baseEnd_3797354 : Nat := 1949867817273441068711293

theorem tailTrace_3797354 : CollatzResearch.WordTrace tailWord_3797354 prefixEnd_3797354 1949867817273441068711293 := by
  unfold tailWord_3797354
  simp only [CollatzResearch.WordTrace]
  refine ⟨34625219671210617318921779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92333919123228312850458077 34625219671210617318921779)
  ·
    refine ⟨51937829506815925978382669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34625219671210617318921779 51937829506815925978382669)
    ·
      refine ⟨19476686065055972241893501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51937829506815925978382669 19476686065055972241893501)
      ·
        refine ⟨7303757274395989590710063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19476686065055972241893501 7303757274395989590710063)
        ·
          refine ⟨10955635911593984386065095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7303757274395989590710063 10955635911593984386065095)
          ·
            refine ⟨16433453867390976579097643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10955635911593984386065095 16433453867390976579097643)
            ·
              refine ⟨24650180801086464868646465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16433453867390976579097643 24650180801086464868646465)
              ·
                refine ⟨18487635600814848651484849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24650180801086464868646465 18487635600814848651484849)
                ·
                  refine ⟨13865726700611136488613637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18487635600814848651484849 13865726700611136488613637)
                  ·
                    refine ⟨2599823756364588091615057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13865726700611136488613637 2599823756364588091615057)
                    ·
                      refine ⟨1949867817273441068711293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2599823756364588091615057 1949867817273441068711293)
                      ·
                        rfl

theorem cell23_3797354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_3797354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797354 prefixEnd_3797354 := by exact prefixLift 3797354
  have htrace : WordTrace (prefixWord ++ tailWord_3797354) baseStart_3797354 baseEnd_3797354 := by
    simpa [prefixWord, tailWord_3797354, baseEnd_3797354] using wordTrace_append hprefix tailTrace_3797354
  have hstable : (prefixWord ++ tailWord_3797354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797354).length < 2 ^ (prefixWord ++ tailWord_3797354).sum := by decide
  have hdescent : baseEnd_3797354 < baseStart_3797354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797357 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_3797357 : Nat := 118140960795 + 3797357 * 2 ^ 59
def prefixEnd_3797357 : Nat := 4983230072969 + 3 ^ 40 * 3797357 * 2
def baseEnd_3797357 : Nat := 1949869357715404556973779

theorem tailTrace_3797357 : CollatzResearch.WordTrace tailWord_3797357 prefixEnd_3797357 1949869357715404556973779 := by
  unfold tailWord_3797357
  simp only [CollatzResearch.WordTrace]
  refine ⟨138500988103831600788046325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92333992069221067192030883 138500988103831600788046325)
  ·
    refine ⟨12984467634734212573879343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138500988103831600788046325 12984467634734212573879343)
    ·
      refine ⟨19476701452101318860819015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12984467634734212573879343 19476701452101318860819015)
      ·
        refine ⟨29215052178151978291228523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19476701452101318860819015 29215052178151978291228523)
        ·
          refine ⟨43822578267227967436842785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29215052178151978291228523 43822578267227967436842785)
          ·
            refine ⟨32866933700420975577632089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43822578267227967436842785 32866933700420975577632089)
            ·
              refine ⟨24650200275315731683224067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32866933700420975577632089 24650200275315731683224067)
              ·
                refine ⟨36975300412973597524836101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24650200275315731683224067 36975300412973597524836101)
                ·
                  refine ⟨6932868827432549535906769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36975300412973597524836101 6932868827432549535906769)
                  ·
                    refine ⟨5199651620574412151930077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6932868827432549535906769 5199651620574412151930077)
                    ·
                      refine ⟨1949869357715404556973779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5199651620574412151930077 1949869357715404556973779)
                      ·
                        rfl

theorem cell23_3797357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_3797357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797357 prefixEnd_3797357 := by exact prefixLift 3797357
  have htrace : WordTrace (prefixWord ++ tailWord_3797357) baseStart_3797357 baseEnd_3797357 := by
    simpa [prefixWord, tailWord_3797357, baseEnd_3797357] using wordTrace_append hprefix tailTrace_3797357
  have hstable : (prefixWord ++ tailWord_3797357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797357).length < 2 ^ (prefixWord ++ tailWord_3797357).sum := by decide
  have hdescent : baseEnd_3797357 < baseStart_3797357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797360 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 8]
def baseStart_3797360 : Nat := 118140960795 + 3797360 * 2 ^ 59
def prefixEnd_3797360 : Nat := 4983230072969 + 3 ^ 40 * 3797360 * 2
def baseEnd_3797360 : Nat := 216652322017485338359585

theorem tailTrace_3797360 : CollatzResearch.WordTrace tailWord_3797360 prefixEnd_3797360 216652322017485338359585 := by
  unfold tailWord_3797360
  simp only [CollatzResearch.WordTrace]
  refine ⟨69250548761410366150202767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92334065015213821533603689 69250548761410366150202767)
  ·
    refine ⟨103875823142115549225304151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69250548761410366150202767 103875823142115549225304151)
    ·
      refine ⟨155813734713173323837956227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103875823142115549225304151 155813734713173323837956227)
      ·
        refine ⟨233720602069759985756934341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155813734713173323837956227 233720602069759985756934341)
        ·
          refine ⟨43822612888079997329425189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233720602069759985756934341 43822612888079997329425189)
          ·
            refine ⟨8216739916514999499267223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43822612888079997329425189 8216739916514999499267223)
            ·
              refine ⟨12325109874772499248900835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8216739916514999499267223 12325109874772499248900835)
              ·
                refine ⟨18487664812158748873351253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12325109874772499248900835 18487664812158748873351253)
                ·
                  refine ⟨216652322017485338359585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18487664812158748873351253 216652322017485338359585)
                  ·
                    rfl

theorem cell23_3797360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 8].length) (baseStart_3797360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797360 prefixEnd_3797360 := by exact prefixLift 3797360
  have htrace : WordTrace (prefixWord ++ tailWord_3797360) baseStart_3797360 baseEnd_3797360 := by
    simpa [prefixWord, tailWord_3797360, baseEnd_3797360] using wordTrace_append hprefix tailTrace_3797360
  have hstable : (prefixWord ++ tailWord_3797360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797360).length < 2 ^ (prefixWord ++ tailWord_3797360).sum := by decide
  have hdescent : baseEnd_3797360 < baseStart_3797360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797370 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3]
def baseStart_3797370 : Nat := 118140960795 + 3797370 * 2 ^ 59
def prefixEnd_3797370 : Nat := 4983230072969 + 3 ^ 40 * 3797370 * 2
def baseEnd_3797370 : Nat := 1949876032963913006111219

theorem tailTrace_3797370 : CollatzResearch.WordTrace tailWord_3797370 prefixEnd_3797370 1949876032963913006111219 := by
  unfold tailWord_3797370
  simp only [CollatzResearch.WordTrace]
  refine ⟨34625365563196126002067391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92334308168523002672179709 34625365563196126002067391)
  ·
    refine ⟨51938048344794189003101087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34625365563196126002067391 51938048344794189003101087)
    ·
      refine ⟨77907072517191283504651631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51938048344794189003101087 77907072517191283504651631)
      ·
        refine ⟨116860608775786925256977447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77907072517191283504651631 116860608775786925256977447)
        ·
          refine ⟨175290913163680387885466171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116860608775786925256977447 175290913163680387885466171)
          ·
            refine ⟨262936369745520581828199257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175290913163680387885466171 262936369745520581828199257)
            ·
              refine ⟨197202277309140436371149443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262936369745520581828199257 197202277309140436371149443)
              ·
                refine ⟨295803415963710654556724165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197202277309140436371149443 295803415963710654556724165)
                ·
                  refine ⟨55463140493195747729385781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295803415963710654556724165 55463140493195747729385781)
                  ·
                    refine ⟨5199669421237101349629917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55463140493195747729385781 5199669421237101349629917)
                    ·
                      refine ⟨1949876032963913006111219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5199669421237101349629917 1949876032963913006111219)
                      ·
                        rfl

theorem cell23_3797370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_3797370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797370 prefixEnd_3797370 := by exact prefixLift 3797370
  have htrace : WordTrace (prefixWord ++ tailWord_3797370) baseStart_3797370 baseEnd_3797370 := by
    simpa [prefixWord, tailWord_3797370, baseEnd_3797370] using wordTrace_append hprefix tailTrace_3797370
  have hstable : (prefixWord ++ tailWord_3797370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797370).length < 2 ^ (prefixWord ++ tailWord_3797370).sum := by decide
  have hdescent : baseEnd_3797370 < baseStart_3797370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797380 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_3797380 : Nat := 118140960795 + 3797380 * 2 ^ 59
def prefixEnd_3797380 : Nat := 4983230072969 + 3 ^ 40 * 3797380 * 2
def baseEnd_3797380 : Nat := 1949881167770457966986173

theorem tailTrace_3797380 : CollatzResearch.WordTrace tailWord_3797380 prefixEnd_3797380 1949881167770457966986173 := by
  unfold tailWord_3797380
  simp only [CollatzResearch.WordTrace]
  refine ⟨69250913491374137858066797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92334551321832183810755729 69250913491374137858066797)
  ·
    refine ⟨25969092559265301696775049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69250913491374137858066797 25969092559265301696775049)
    ·
      refine ⟨19476819419448976272581287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25969092559265301696775049 19476819419448976272581287)
      ·
        refine ⟨29215229129173464408871931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19476819419448976272581287 29215229129173464408871931)
        ·
          refine ⟨43822843693760196613307897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29215229129173464408871931 43822843693760196613307897)
          ·
            refine ⟨32867132770320147459980923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43822843693760196613307897 32867132770320147459980923)
            ·
              refine ⟨49300699155480221189971385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32867132770320147459980923 49300699155480221189971385)
              ·
                refine ⟨36975524366610165892478539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49300699155480221189971385 36975524366610165892478539)
                ·
                  refine ⟨55463286549915248838717809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36975524366610165892478539 55463286549915248838717809)
                  ·
                    refine ⟨41597464912436436629038357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55463286549915248838717809 41597464912436436629038357)
                    ·
                      refine ⟨1949881167770457966986173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41597464912436436629038357 1949881167770457966986173)
                      ·
                        rfl

theorem cell23_3797380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_3797380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797380 prefixEnd_3797380 := by exact prefixLift 3797380
  have htrace : WordTrace (prefixWord ++ tailWord_3797380) baseStart_3797380 baseEnd_3797380 := by
    simpa [prefixWord, tailWord_3797380, baseEnd_3797380] using wordTrace_append hprefix tailTrace_3797380
  have hstable : (prefixWord ++ tailWord_3797380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797380).length < 2 ^ (prefixWord ++ tailWord_3797380).sum := by decide
  have hdescent : baseEnd_3797380 < baseStart_3797380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797407 : List Nat := [1, 1, 2, 5, 1, 1, 1, 5, 1, 5]
def baseStart_3797407 : Nat := 118140960795 + 3797407 * 2 ^ 59
def prefixEnd_3797407 : Nat := 4983230072969 + 3 ^ 40 * 3797407 * 2
def baseEnd_3797407 : Nat := 649965010582709787116183

theorem tailTrace_3797407 : CollatzResearch.WordTrace tailWord_3797407 prefixEnd_3797407 649965010582709787116183 := by
  unfold tailWord_3797407
  simp only [CollatzResearch.WordTrace]
  refine ⟨138502811753650459327366475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92335207835766972884910983 138502811753650459327366475)
  ·
    refine ⟨207754217630475688991049713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138502811753650459327366475 207754217630475688991049713)
    ·
      refine ⟨155815663222856766743287285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207754217630475688991049713 155815663222856766743287285)
      ·
        refine ⟨14607718427142821882183183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155815663222856766743287285 14607718427142821882183183)
        ·
          refine ⟨21911577640714232823274775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14607718427142821882183183 21911577640714232823274775)
          ·
            refine ⟨32867366461071349234912163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21911577640714232823274775 32867366461071349234912163)
            ·
              refine ⟨49301049691607023852368245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32867366461071349234912163 49301049691607023852368245)
              ·
                refine ⟨4621973408588158486159523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49301049691607023852368245 4621973408588158486159523)
                ·
                  refine ⟨6932960112882237729239285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4621973408588158486159523 6932960112882237729239285)
                  ·
                    refine ⟨649965010582709787116183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6932960112882237729239285 649965010582709787116183)
                    ·
                      rfl

theorem cell23_3797407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 5].length) (baseStart_3797407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797407 prefixEnd_3797407 := by exact prefixLift 3797407
  have htrace : WordTrace (prefixWord ++ tailWord_3797407) baseStart_3797407 baseEnd_3797407 := by
    simpa [prefixWord, tailWord_3797407, baseEnd_3797407] using wordTrace_append hprefix tailTrace_3797407
  have hstable : (prefixWord ++ tailWord_3797407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797407).length < 2 ^ (prefixWord ++ tailWord_3797407).sum := by decide
  have hdescent : baseEnd_3797407 < baseStart_3797407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797450 : List Nat := [3, 1, 2, 1, 2, 2, 1, 11]
def baseStart_3797450 : Nat := 118140960795 + 3797450 * 2 ^ 59
def prefixEnd_3797450 : Nat := 4983230072969 + 3 ^ 40 * 3797450 * 2
def baseEnd_3797450 : Nat := 72219152274676766411513

theorem tailTrace_3797450 : CollatzResearch.WordTrace tailWord_3797450 prefixEnd_3797450 72219152274676766411513 := by
  unfold tailWord_3797450
  simp only [CollatzResearch.WordTrace]
  refine ⟨34626095023123669417795451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92336253394996451780787869 34626095023123669417795451)
  ·
    refine ⟨51939142534685504126693177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34626095023123669417795451 51939142534685504126693177)
    ·
      refine ⟨38954356901014128095019883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51939142534685504126693177 38954356901014128095019883)
      ·
        refine ⟨58431535351521192142529825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38954356901014128095019883 58431535351521192142529825)
        ·
          refine ⟨43823651513640894106897369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58431535351521192142529825 43823651513640894106897369)
          ·
            refine ⟨32867738635230670580173027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43823651513640894106897369 32867738635230670580173027)
            ·
              refine ⟨49301607952846005870259541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32867738635230670580173027 49301607952846005870259541)
              ·
                refine ⟨72219152274676766411513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 49301607952846005870259541 72219152274676766411513)
                ·
                  rfl

theorem cell23_3797450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 11].length) (baseStart_3797450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797450 prefixEnd_3797450 := by exact prefixLift 3797450
  have htrace : WordTrace (prefixWord ++ tailWord_3797450) baseStart_3797450 baseEnd_3797450 := by
    simpa [prefixWord, tailWord_3797450, baseEnd_3797450] using wordTrace_append hprefix tailTrace_3797450
  have hstable : (prefixWord ++ tailWord_3797450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797450).length < 2 ^ (prefixWord ++ tailWord_3797450).sum := by decide
  have hdescent : baseEnd_3797450 < baseStart_3797450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797458 : List Nat := [3, 2, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_3797458 : Nat := 118140960795 + 3797458 * 2 ^ 59
def prefixEnd_3797458 : Nat := 4983230072969 + 3 ^ 40 * 3797458 * 2
def baseEnd_3797458 : Nat := 649973739753836220603605

theorem tailTrace_3797458 : CollatzResearch.WordTrace tailWord_3797458 prefixEnd_3797458 649973739753836220603605 := by
  unfold tailWord_3797458
  simp only [CollatzResearch.WordTrace]
  refine ⟨34626167969116423759368257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92336447917643796691648685 34626167969116423759368257)
  ·
    refine ⟨25969625976837317819526193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34626167969116423759368257 25969625976837317819526193)
    ·
      refine ⟨19477219482627988364644645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25969625976837317819526193 19477219482627988364644645)
      ·
        refine ⟨3651978652992747818370871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19477219482627988364644645 3651978652992747818370871)
        ·
          refine ⟨5477967979489121727556307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3651978652992747818370871 5477967979489121727556307)
          ·
            refine ⟨8216951969233682591334461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5477967979489121727556307 8216951969233682591334461)
            ·
              refine ⟨3081356988462630971750423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8216951969233682591334461 3081356988462630971750423)
              ·
                refine ⟨4622035482693946457625635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081356988462630971750423 4622035482693946457625635)
                ·
                  refine ⟨6933053224040919686438453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4622035482693946457625635 6933053224040919686438453)
                  ·
                    refine ⟨649973739753836220603605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6933053224040919686438453 649973739753836220603605)
                    ·
                      rfl

theorem cell23_3797458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_3797458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797458 prefixEnd_3797458 := by exact prefixLift 3797458
  have htrace : WordTrace (prefixWord ++ tailWord_3797458) baseStart_3797458 baseEnd_3797458 := by
    simpa [prefixWord, tailWord_3797458, baseEnd_3797458] using wordTrace_append hprefix tailTrace_3797458
  have hstable : (prefixWord ++ tailWord_3797458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797458).length < 2 ^ (prefixWord ++ tailWord_3797458).sum := by decide
  have hdescent : baseEnd_3797458 < baseStart_3797458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797461 : List Nat := [1, 3, 2, 3, 1, 3, 3, 1, 1, 1, 4]
def baseStart_3797461 : Nat := 118140960795 + 3797461 * 2 ^ 59
def prefixEnd_3797461 : Nat := 4983230072969 + 3 ^ 40 * 3797461 * 2
def baseEnd_3797461 : Nat := 1949922759703472150073301

theorem tailTrace_3797461 : CollatzResearch.WordTrace tailWord_3797461 prefixEnd_3797461 1949922759703472150073301 := by
  unfold tailWord_3797461
  simp only [CollatzResearch.WordTrace]
  refine ⟨138504781295454826549832237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92336520863636551033221491 138504781295454826549832237)
  ·
    refine ⟨51939292985795559956187089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138504781295454826549832237 51939292985795559956187089)
    ·
      refine ⟨38954469739346669967140317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51939292985795559956187089 38954469739346669967140317)
      ·
        refine ⟨14607926152255001237677619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38954469739346669967140317 14607926152255001237677619)
        ·
          refine ⟨21911889228382501856516429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14607926152255001237677619 21911889228382501856516429)
          ·
            refine ⟨8216958460643438196193661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21911889228382501856516429 8216958460643438196193661)
            ·
              refine ⟨3081359422741289323572623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8216958460643438196193661 3081359422741289323572623)
              ·
                refine ⟨4622039134111933985358935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081359422741289323572623 4622039134111933985358935)
                ·
                  refine ⟨6933058701167900978038403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4622039134111933985358935 6933058701167900978038403)
                  ·
                    refine ⟨10399588051751851467057605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6933058701167900978038403 10399588051751851467057605)
                    ·
                      refine ⟨1949922759703472150073301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10399588051751851467057605 1949922759703472150073301)
                      ·
                        rfl

theorem cell23_3797461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_3797461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797461 prefixEnd_3797461 := by exact prefixLift 3797461
  have htrace : WordTrace (prefixWord ++ tailWord_3797461) baseStart_3797461 baseEnd_3797461 := by
    simpa [prefixWord, tailWord_3797461, baseEnd_3797461] using wordTrace_append hprefix tailTrace_3797461
  have hstable : (prefixWord ++ tailWord_3797461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797461).length < 2 ^ (prefixWord ++ tailWord_3797461).sum := by decide
  have hdescent : baseEnd_3797461 < baseStart_3797461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797520 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 9]
def baseStart_3797520 : Nat := 118140960795 + 3797520 * 2 ^ 59
def prefixEnd_3797520 : Nat := 4983230072969 + 3 ^ 40 * 3797520 * 2
def baseEnd_3797520 : Nat := 1949953055062087419235529

theorem tailTrace_3797520 : CollatzResearch.WordTrace tailWord_3797520 prefixEnd_3797520 1949953055062087419235529 := by
  unfold tailWord_3797520
  simp only [CollatzResearch.WordTrace]
  refine ⟨69253466601120539813115007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92337955468160719750820009 69253466601120539813115007)
  ·
    refine ⟨103880199901680809719672511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69253466601120539813115007 103880199901680809719672511)
    ·
      refine ⟨155820299852521214579508767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103880199901680809719672511 155820299852521214579508767)
      ·
        refine ⟨233730449778781821869263151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155820299852521214579508767 233730449778781821869263151)
        ·
          refine ⟨350595674668172732803894727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233730449778781821869263151 350595674668172732803894727)
          ·
            refine ⟨525893512002259099205842091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350595674668172732803894727 525893512002259099205842091)
            ·
              refine ⟨788840268003388648808763137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525893512002259099205842091 788840268003388648808763137)
              ·
                refine ⟨591630201002541486606572353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788840268003388648808763137 591630201002541486606572353)
                ·
                  refine ⟨443722650751906114954929265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591630201002541486606572353 443722650751906114954929265)
                  ·
                    refine ⟨332791988063929586216196949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 443722650751906114954929265 332791988063929586216196949)
                    ·
                      refine ⟨1949953055062087419235529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 332791988063929586216196949 1949953055062087419235529)
                      ·
                        rfl

theorem cell23_3797520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_3797520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797520 prefixEnd_3797520 := by exact prefixLift 3797520
  have htrace : WordTrace (prefixWord ++ tailWord_3797520) baseStart_3797520 baseEnd_3797520 := by
    simpa [prefixWord, tailWord_3797520, baseEnd_3797520] using wordTrace_append hprefix tailTrace_3797520
  have hstable : (prefixWord ++ tailWord_3797520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797520).length < 2 ^ (prefixWord ++ tailWord_3797520).sum := by decide
  have hdescent : baseEnd_3797520 < baseStart_3797520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797528 : List Nat := [2, 1, 2, 3, 3, 3, 1, 2, 2, 1, 3]
def baseStart_3797528 : Nat := 118140960795 + 3797528 * 2 ^ 59
def prefixEnd_3797528 : Nat := 4983230072969 + 3 ^ 40 * 3797528 * 2
def baseEnd_3797528 : Nat := 1949957162907323387935493

theorem tailTrace_3797528 : CollatzResearch.WordTrace tailWord_3797528 prefixEnd_3797528 1949957162907323387935493 := by
  unfold tailWord_3797528
  simp only [CollatzResearch.WordTrace]
  refine ⟨69253612493106048496260619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92338149990808064661680825 69253612493106048496260619)
  ·
    refine ⟨103880418739659072744390929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69253612493106048496260619 103880418739659072744390929)
    ·
      refine ⟨77910314054744304558293197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103880418739659072744390929 77910314054744304558293197)
      ·
        refine ⟨29216367770529114209359949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77910314054744304558293197 29216367770529114209359949)
        ·
          refine ⟨10956137913948417828509981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29216367770529114209359949 10956137913948417828509981)
          ·
            refine ⟨4108551717730656685691243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10956137913948417828509981 4108551717730656685691243)
            ·
              refine ⟨6162827576595985028536865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4108551717730656685691243 6162827576595985028536865)
              ·
                refine ⟨4622120682446988771402649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6162827576595985028536865 4622120682446988771402649)
                ·
                  refine ⟨3466590511835241578551987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4622120682446988771402649 3466590511835241578551987)
                  ·
                    refine ⟨5199885767752862367827981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3466590511835241578551987 5199885767752862367827981)
                    ·
                      refine ⟨1949957162907323387935493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5199885767752862367827981 1949957162907323387935493)
                      ·
                        rfl

theorem cell23_3797528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_3797528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797528 prefixEnd_3797528 := by exact prefixLift 3797528
  have htrace : WordTrace (prefixWord ++ tailWord_3797528) baseStart_3797528 baseEnd_3797528 := by
    simpa [prefixWord, tailWord_3797528, baseEnd_3797528] using wordTrace_append hprefix tailTrace_3797528
  have hstable : (prefixWord ++ tailWord_3797528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797528).length < 2 ^ (prefixWord ++ tailWord_3797528).sum := by decide
  have hdescent : baseEnd_3797528 < baseStart_3797528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797544 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 2, 6]
def baseStart_3797544 : Nat := 118140960795 + 3797544 * 2 ^ 59
def prefixEnd_3797544 : Nat := 4983230072969 + 3 ^ 40 * 3797544 * 2
def baseEnd_3797544 : Nat := 649988459532598441778473

theorem tailTrace_3797544 : CollatzResearch.WordTrace tailWord_3797544 prefixEnd_3797544 649988459532598441778473 := by
  unfold tailWord_3797544
  simp only [CollatzResearch.WordTrace]
  refine ⟨69253904277077065862551843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92338539036102754483402457 69253904277077065862551843)
  ·
    refine ⟨103880856415615598793827765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69253904277077065862551843 103880856415615598793827765)
    ·
      refine ⟨9738830288963962386921353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103880856415615598793827765 9738830288963962386921353)
      ·
        refine ⟨7304122716722971790191015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9738830288963962386921353 7304122716722971790191015)
        ·
          refine ⟨10956184075084457685286523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7304122716722971790191015 10956184075084457685286523)
          ·
            refine ⟨16434276112626686527929785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10956184075084457685286523 16434276112626686527929785)
            ·
              refine ⟨12325707084470014895947339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16434276112626686527929785 12325707084470014895947339)
              ·
                refine ⟨18488560626705022343921009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12325707084470014895947339 18488560626705022343921009)
                ·
                  refine ⟨13866420470028766757940757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18488560626705022343921009 13866420470028766757940757)
                  ·
                    refine ⟨649988459532598441778473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13866420470028766757940757 649988459532598441778473)
                    ·
                      rfl

theorem cell23_3797544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_3797544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797544 prefixEnd_3797544 := by exact prefixLift 3797544
  have htrace : WordTrace (prefixWord ++ tailWord_3797544) baseStart_3797544 baseEnd_3797544 := by
    simpa [prefixWord, tailWord_3797544, baseEnd_3797544] using wordTrace_append hprefix tailTrace_3797544
  have hstable : (prefixWord ++ tailWord_3797544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797544).length < 2 ^ (prefixWord ++ tailWord_3797544).sum := by decide
  have hdescent : baseEnd_3797544 < baseStart_3797544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797557 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 7]
def baseStart_3797557 : Nat := 118140960795 + 3797557 * 2 ^ 59
def prefixEnd_3797557 : Nat := 4983230072969 + 3 ^ 40 * 3797557 * 2
def baseEnd_3797557 : Nat := 216663561538478197163651

theorem tailTrace_3797557 : CollatzResearch.WordTrace tailWord_3797557 prefixEnd_3797557 216663561538478197163651 := by
  unfold tailWord_3797557
  simp only [CollatzResearch.WordTrace]
  refine ⟨138508282703107034945326925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92338855135404689963551283 138508282703107034945326925)
  ·
    refine ⟨51940606013665138104497597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138508282703107034945326925 51940606013665138104497597)
    ·
      refine ⟨19477727255124426789186599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51940606013665138104497597 19477727255124426789186599)
      ·
        refine ⟨29216590882686640183779899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19477727255124426789186599 29216590882686640183779899)
        ·
          refine ⟨43824886324029960275669849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29216590882686640183779899 43824886324029960275669849)
          ·
            refine ⟨32868664743022470206752387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43824886324029960275669849 32868664743022470206752387)
            ·
              refine ⟨49302997114533705310128581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32868664743022470206752387 49302997114533705310128581)
              ·
                refine ⟨9244311958975069745649109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49302997114533705310128581 9244311958975069745649109)
                ·
                  refine ⟨216663561538478197163651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9244311958975069745649109 216663561538478197163651)
                  ·
                    rfl

theorem cell23_3797557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_3797557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797557 prefixEnd_3797557 := by exact prefixLift 3797557
  have htrace : WordTrace (prefixWord ++ tailWord_3797557) baseStart_3797557 baseEnd_3797557 := by
    simpa [prefixWord, tailWord_3797557, baseEnd_3797557] using wordTrace_append hprefix tailTrace_3797557
  have hstable : (prefixWord ++ tailWord_3797557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797557).length < 2 ^ (prefixWord ++ tailWord_3797557).sum := by decide
  have hdescent : baseEnd_3797557 < baseStart_3797557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797591 : List Nat := [1, 1, 3, 2, 2, 2, 5, 2, 5]
def baseStart_3797591 : Nat := 118140960795 + 3797591 * 2 ^ 59
def prefixEnd_3797591 : Nat := 4983230072969 + 3 ^ 40 * 3797591 * 2
def baseEnd_3797591 : Nat := 216665501354284071271967

theorem tailTrace_3797591 : CollatzResearch.WordTrace tailWord_3797591 prefixEnd_3797591 216665501354284071271967 := by
  unfold tailWord_3797591
  simp only [CollatzResearch.WordTrace]
  refine ⟨138509522784983858752064627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92339681856655905834709751 138509522784983858752064627)
  ·
    refine ⟨207764284177475788128096941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138509522784983858752064627 207764284177475788128096941)
    ·
      refine ⟨77911606566553420548036353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207764284177475788128096941 77911606566553420548036353)
      ·
        refine ⟨58433704924915065411027265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77911606566553420548036353 58433704924915065411027265)
        ·
          refine ⟨43825278693686299058270449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58433704924915065411027265 43825278693686299058270449)
          ·
            refine ⟨32868959020264724293702837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43825278693686299058270449 32868959020264724293702837)
            ·
              refine ⟨3081464908149817902534641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32868959020264724293702837 3081464908149817902534641)
              ·
                refine ⟨2311098681112363426900981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081464908149817902534641 2311098681112363426900981)
                ·
                  refine ⟨216665501354284071271967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2311098681112363426900981 216665501354284071271967)
                  ·
                    rfl

theorem cell23_3797591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 5].length) (baseStart_3797591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797591 prefixEnd_3797591 := by exact prefixLift 3797591
  have htrace : WordTrace (prefixWord ++ tailWord_3797591) baseStart_3797591 baseEnd_3797591 := by
    simpa [prefixWord, tailWord_3797591, baseEnd_3797591] using wordTrace_append hprefix tailTrace_3797591
  have hstable : (prefixWord ++ tailWord_3797591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797591).length < 2 ^ (prefixWord ++ tailWord_3797591).sum := by decide
  have hdescent : baseEnd_3797591 < baseStart_3797591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797602 : List Nat := [3, 3, 2, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3797602 : Nat := 118140960795 + 3797602 * 2 ^ 59
def prefixEnd_3797602 : Nat := 4983230072969 + 3 ^ 40 * 3797602 * 2
def baseEnd_3797602 : Nat := 1949995160475756098410153

theorem tailTrace_3797602 : CollatzResearch.WordTrace tailWord_3797602 prefixEnd_3797602 1949995160475756098410153 := by
  unfold tailWord_3797602
  simp only [CollatzResearch.WordTrace]
  refine ⟨34627480996986001907678765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92339949325296005087143373 34627480996986001907678765)
  ·
    refine ⟨12985305373869750715379537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34627480996986001907678765 12985305373869750715379537)
    ·
      refine ⟨9738979030402313036534653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12985305373869750715379537 9738979030402313036534653)
      ·
        refine ⟨3652117136400867388700495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9738979030402313036534653 3652117136400867388700495)
        ·
          refine ⟨5478175704601301083050743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652117136400867388700495 5478175704601301083050743)
          ·
            refine ⟨8217263556901951624576115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5478175704601301083050743 8217263556901951624576115)
            ·
              refine ⟨12325895335352927436864173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8217263556901951624576115 12325895335352927436864173)
              ·
                refine ⟨4622210750757347788824065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12325895335352927436864173 4622210750757347788824065)
                ·
                  refine ⟨3466658063068010841618049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4622210750757347788824065 3466658063068010841618049)
                  ·
                    refine ⟨2599993547301008131213537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3466658063068010841618049 2599993547301008131213537)
                    ·
                      refine ⟨1949995160475756098410153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2599993547301008131213537 1949995160475756098410153)
                      ·
                        rfl

theorem cell23_3797602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3797602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797602 prefixEnd_3797602 := by exact prefixLift 3797602
  have htrace : WordTrace (prefixWord ++ tailWord_3797602) baseStart_3797602 baseEnd_3797602 := by
    simpa [prefixWord, tailWord_3797602, baseEnd_3797602] using wordTrace_append hprefix tailTrace_3797602
  have hstable : (prefixWord ++ tailWord_3797602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797602).length < 2 ^ (prefixWord ++ tailWord_3797602).sum := by decide
  have hdescent : baseEnd_3797602 < baseStart_3797602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797624 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 1, 6, 2]
def baseStart_3797624 : Nat := 118140960795 + 3797624 * 2 ^ 59
def prefixEnd_3797624 : Nat := 4983230072969 + 3 ^ 40 * 3797624 * 2
def baseEnd_3797624 : Nat := 1950006457050155012335051

theorem tailTrace_3797624 : CollatzResearch.WordTrace tailWord_3797624 prefixEnd_3797624 1950006457050155012335051 := by
  unfold tailWord_3797624
  simp only [CollatzResearch.WordTrace]
  refine ⟨69255363196932152694007963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92340484262576203592010617 69255363196932152694007963)
  ·
    refine ⟨103883044795398229041011945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69255363196932152694007963 103883044795398229041011945)
    ·
      refine ⟨77912283596548671780758959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103883044795398229041011945 77912283596548671780758959)
      ·
        refine ⟨116868425394823007671138439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77912283596548671780758959 116868425394823007671138439)
        ·
          refine ⟨175302638092234511506707659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116868425394823007671138439 175302638092234511506707659)
          ·
            refine ⟨262953957138351767260061489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175302638092234511506707659 262953957138351767260061489)
            ·
              refine ⟨197215467853763825445046117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262953957138351767260061489 197215467853763825445046117)
              ·
                refine ⟨36977900222580717270946147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197215467853763825445046117 36977900222580717270946147)
                ·
                  refine ⟨55466850333871075906419221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36977900222580717270946147 55466850333871075906419221)
                  ·
                    refine ⟨2600008609400206683113401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55466850333871075906419221 2600008609400206683113401)
                    ·
                      refine ⟨1950006457050155012335051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2600008609400206683113401 1950006457050155012335051)
                      ·
                        rfl

theorem cell23_3797624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 6, 2].length) (baseStart_3797624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797624 prefixEnd_3797624 := by exact prefixLift 3797624
  have htrace : WordTrace (prefixWord ++ tailWord_3797624) baseStart_3797624 baseEnd_3797624 := by
    simpa [prefixWord, tailWord_3797624, baseEnd_3797624] using wordTrace_append hprefix tailTrace_3797624
  have hstable : (prefixWord ++ tailWord_3797624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797624).length < 2 ^ (prefixWord ++ tailWord_3797624).sum := by decide
  have hdescent : baseEnd_3797624 < baseStart_3797624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797644 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 4, 2, 3]
def baseStart_3797644 : Nat := 118140960795 + 3797644 * 2 ^ 59
def prefixEnd_3797644 : Nat := 4983230072969 + 3 ^ 40 * 3797644 * 2
def baseEnd_3797644 : Nat := 1950016726663244934084959

theorem tailTrace_3797644 : CollatzResearch.WordTrace tailWord_3797644 prefixEnd_3797644 1950016726663244934084959 := by
  unfold tailWord_3797644
  simp only [CollatzResearch.WordTrace]
  refine ⟨69255727926895924401871993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92340970569194565869162657 69255727926895924401871993)
  ·
    refine ⟨51941795945171943301403995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69255727926895924401871993 51941795945171943301403995)
    ·
      refine ⟨77912693917757914952105993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51941795945171943301403995 77912693917757914952105993)
      ·
        refine ⟨58434520438318436214079495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77912693917757914952105993 58434520438318436214079495)
        ·
          refine ⟨87651780657477654321119243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58434520438318436214079495 87651780657477654321119243)
          ·
            refine ⟨131477670986216481481678865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87651780657477654321119243 131477670986216481481678865)
            ·
              refine ⟨98608253239662361111259149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131477670986216481481678865 98608253239662361111259149)
              ·
                refine ⟨36978094964873385416722181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98608253239662361111259149 36978094964873385416722181)
                ·
                  refine ⟨6933392805913759765635409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36978094964873385416722181 6933392805913759765635409)
                  ·
                    refine ⟨5200044604435319824226557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6933392805913759765635409 5200044604435319824226557)
                    ·
                      refine ⟨1950016726663244934084959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5200044604435319824226557 1950016726663244934084959)
                      ·
                        rfl

theorem cell23_3797644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_3797644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797644 prefixEnd_3797644 := by exact prefixLift 3797644
  have htrace : WordTrace (prefixWord ++ tailWord_3797644) baseStart_3797644 baseEnd_3797644 := by
    simpa [prefixWord, tailWord_3797644, baseEnd_3797644] using wordTrace_append hprefix tailTrace_3797644
  have hstable : (prefixWord ++ tailWord_3797644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797644).length < 2 ^ (prefixWord ++ tailWord_3797644).sum := by decide
  have hdescent : baseEnd_3797644 < baseStart_3797644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797651 : List Nat := [1, 1, 1, 2, 1, 2, 2, 8, 1, 4]
def baseStart_3797651 : Nat := 118140960795 + 3797651 * 2 ^ 59
def prefixEnd_3797651 : Nat := 4983230072969 + 3 ^ 40 * 3797651 * 2
def baseEnd_3797651 : Nat := 650006773675942135565809

theorem tailTrace_3797651 : CollatzResearch.WordTrace tailWord_3797651 prefixEnd_3797651 650006773675942135565809 := by
  unfold tailWord_3797651
  simp only [CollatzResearch.WordTrace]
  refine ⟨138511711164766488999248807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92341140776510992666165871 138511711164766488999248807)
  ·
    refine ⟨207767566747149733498873211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138511711164766488999248807 207767566747149733498873211)
    ·
      refine ⟨311651350120724600248309817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207767566747149733498873211 311651350120724600248309817)
      ·
        refine ⟨233738512590543450186232363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311651350120724600248309817 233738512590543450186232363)
        ·
          refine ⟨350607768885815175279348545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233738512590543450186232363 350607768885815175279348545)
          ·
            refine ⟨262955826664361381459511409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350607768885815175279348545 262955826664361381459511409)
            ·
              refine ⟨197216869998271036094633557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262955826664361381459511409 197216869998271036094633557)
              ·
                refine ⟨2311135195292238704233987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 197216869998271036094633557 2311135195292238704233987)
                ·
                  refine ⟨3466702792938358056350981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311135195292238704233987 3466702792938358056350981)
                  ·
                    refine ⟨650006773675942135565809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3466702792938358056350981 650006773675942135565809)
                    ·
                      rfl

theorem cell23_3797651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 1, 4].length) (baseStart_3797651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797651 prefixEnd_3797651 := by exact prefixLift 3797651
  have htrace : WordTrace (prefixWord ++ tailWord_3797651) baseStart_3797651 baseEnd_3797651 := by
    simpa [prefixWord, tailWord_3797651, baseEnd_3797651] using wordTrace_append hprefix tailTrace_3797651
  have hstable : (prefixWord ++ tailWord_3797651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797651).length < 2 ^ (prefixWord ++ tailWord_3797651).sum := by decide
  have hdescent : baseEnd_3797651 < baseStart_3797651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797667 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 6]
def baseStart_3797667 : Nat := 118140960795 + 3797667 * 2 ^ 59
def prefixEnd_3797667 : Nat := 4983230072969 + 3 ^ 40 * 3797667 * 2
def baseEnd_3797667 : Nat := 1950028536718298344097353

theorem tailTrace_3797667 : CollatzResearch.WordTrace tailWord_3797667 prefixEnd_3797667 1950028536718298344097353 := by
  unfold tailWord_3797667
  simp only [CollatzResearch.WordTrace]
  refine ⟨138512294732708523731831255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92341529821805682487887503 138512294732708523731831255)
  ·
    refine ⟨207768442099062785597746883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138512294732708523731831255 207768442099062785597746883)
    ·
      refine ⟨311652663148594178396620325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207768442099062785597746883 311652663148594178396620325)
      ·
        refine ⟨58434874340361408449366311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311652663148594178396620325 58434874340361408449366311)
        ·
          refine ⟨87652311510542112674049467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58434874340361408449366311 87652311510542112674049467)
          ·
            refine ⟨131478467265813169011074201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87652311510542112674049467 131478467265813169011074201)
            ·
              refine ⟨98608850449359876758305651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131478467265813169011074201 98608850449359876758305651)
              ·
                refine ⟨147913275674039815137458477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98608850449359876758305651 147913275674039815137458477)
                ·
                  refine ⟨55467478377764930676546929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147913275674039815137458477 55467478377764930676546929)
                  ·
                    refine ⟨41600608783323698007410197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55467478377764930676546929 41600608783323698007410197)
                    ·
                      refine ⟨1950028536718298344097353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41600608783323698007410197 1950028536718298344097353)
                      ·
                        rfl

theorem cell23_3797667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_3797667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797667 prefixEnd_3797667 := by exact prefixLift 3797667
  have htrace : WordTrace (prefixWord ++ tailWord_3797667) baseStart_3797667 baseEnd_3797667 := by
    simpa [prefixWord, tailWord_3797667, baseEnd_3797667] using wordTrace_append hprefix tailTrace_3797667
  have hstable : (prefixWord ++ tailWord_3797667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797667).length < 2 ^ (prefixWord ++ tailWord_3797667).sum := by decide
  have hdescent : baseEnd_3797667 < baseStart_3797667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797678 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3797678 : Nat := 118140960795 + 3797678 * 2 ^ 59
def prefixEnd_3797678 : Nat := 4983230072969 + 3 ^ 40 * 3797678 * 2
def baseEnd_3797678 : Nat := 1950034185005497801059803

theorem tailTrace_3797678 : CollatzResearch.WordTrace tailWord_3797678 prefixEnd_3797678 1950034185005497801059803 := by
  unfold tailWord_3797678
  simp only [CollatzResearch.WordTrace]
  refine ⟨17314086991958584076310211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92341797290445781740321125 17314086991958584076310211)
  ·
    refine ⟨25971130487937876114465317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17314086991958584076310211 25971130487937876114465317)
    ·
      refine ⟨4869586966488351771462247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25971130487937876114465317 4869586966488351771462247)
      ·
        refine ⟨7304380449732527657193371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4869586966488351771462247 7304380449732527657193371)
        ·
          refine ⟨10956570674598791485790057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7304380449732527657193371 10956570674598791485790057)
          ·
            refine ⟨8217428005949093614342543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10956570674598791485790057 8217428005949093614342543)
            ·
              refine ⟨12326142008923640421513815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8217428005949093614342543 12326142008923640421513815)
              ·
                refine ⟨18489213013385460632270723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12326142008923640421513815 18489213013385460632270723)
                ·
                  refine ⟨27733819520078190948406085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18489213013385460632270723 27733819520078190948406085)
                  ·
                    refine ⟨5200091160014660802826141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27733819520078190948406085 5200091160014660802826141)
                    ·
                      refine ⟨1950034185005497801059803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5200091160014660802826141 1950034185005497801059803)
                      ·
                        rfl

theorem cell23_3797678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3797678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797678 prefixEnd_3797678 := by exact prefixLift 3797678
  have htrace : WordTrace (prefixWord ++ tailWord_3797678) baseStart_3797678 baseEnd_3797678 := by
    simpa [prefixWord, tailWord_3797678, baseEnd_3797678] using wordTrace_append hprefix tailTrace_3797678
  have hstable : (prefixWord ++ tailWord_3797678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797678).length < 2 ^ (prefixWord ++ tailWord_3797678).sum := by decide
  have hdescent : baseEnd_3797678 < baseStart_3797678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797685 : List Nat := [1, 3, 3, 3, 1, 2, 2, 3, 1, 4]
def baseStart_3797685 : Nat := 118140960795 + 3797685 * 2 ^ 59
def prefixEnd_3797685 : Nat := 4983230072969 + 3 ^ 40 * 3797685 * 2
def baseEnd_3797685 : Nat := 650012593123359757890757

theorem tailTrace_3797685 : CollatzResearch.WordTrace tailWord_3797685 prefixEnd_3797685 650012593123359757890757 := by
  unfold tailWord_3797685
  simp only [CollatzResearch.WordTrace]
  refine ⟨138512951246643312805986509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92341967497762208537324339 138512951246643312805986509)
  ·
    refine ⟨51942356717491242302244941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138512951246643312805986509 51942356717491242302244941)
    ·
      refine ⟨19478383769059215863341853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51942356717491242302244941 19478383769059215863341853)
      ·
        refine ⟨7304393913397205948753195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19478383769059215863341853 7304393913397205948753195)
        ·
          refine ⟨10956590870095808923129793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7304393913397205948753195 10956590870095808923129793)
          ·
            refine ⟨8217443152571856692347345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10956590870095808923129793 8217443152571856692347345)
            ·
              refine ⟨6163082364428892519260509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8217443152571856692347345 6163082364428892519260509)
              ·
                refine ⟨2311155886660834694722691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6163082364428892519260509 2311155886660834694722691)
                ·
                  refine ⟨3466733829991252042084037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311155886660834694722691 3466733829991252042084037)
                  ·
                    refine ⟨650012593123359757890757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3466733829991252042084037 650012593123359757890757)
                    ·
                      rfl

theorem cell23_3797685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_3797685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797685 prefixEnd_3797685 := by exact prefixLift 3797685
  have htrace : WordTrace (prefixWord ++ tailWord_3797685) baseStart_3797685 baseEnd_3797685 := by
    simpa [prefixWord, tailWord_3797685, baseEnd_3797685] using wordTrace_append hprefix tailTrace_3797685
  have hstable : (prefixWord ++ tailWord_3797685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797685).length < 2 ^ (prefixWord ++ tailWord_3797685).sum := by decide
  have hdescent : baseEnd_3797685 < baseStart_3797685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797702 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3797702 : Nat := 118140960795 + 3797702 * 2 ^ 59
def prefixEnd_3797702 : Nat := 4983230072969 + 3 ^ 40 * 3797702 * 2
def baseEnd_3797702 : Nat := 650015502847068569053231

theorem tailTrace_3797702 : CollatzResearch.WordTrace tailWord_3797702 prefixEnd_3797702 650015502847068569053231 := by
  unfold tailWord_3797702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328549102736928897167355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92342380858387816472903573 4328549102736928897167355)
  ·
    refine ⟨6492823654105393345751033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4328549102736928897167355 6492823654105393345751033)
    ·
      refine ⟨4869617740579045009313275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6492823654105393345751033 4869617740579045009313275)
      ·
        refine ⟨7304426610868567513969913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4869617740579045009313275 7304426610868567513969913)
        ·
          refine ⟨5478319958151425635477435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7304426610868567513969913 5478319958151425635477435)
          ·
            refine ⟨8217479937227138453216153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5478319958151425635477435 8217479937227138453216153)
            ·
              refine ⟨6163109952920353839912115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8217479937227138453216153 6163109952920353839912115)
              ·
                refine ⟨9244664929380530759868173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6163109952920353839912115 9244664929380530759868173)
                ·
                  refine ⟨3466749348517699034950565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9244664929380530759868173 3466749348517699034950565)
                  ·
                    refine ⟨650015502847068569053231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3466749348517699034950565 650015502847068569053231)
                    ·
                      rfl

theorem cell23_3797702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3797702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797702 prefixEnd_3797702 := by exact prefixLift 3797702
  have htrace : WordTrace (prefixWord ++ tailWord_3797702) baseStart_3797702 baseEnd_3797702 := by
    simpa [prefixWord, tailWord_3797702, baseEnd_3797702] using wordTrace_append hprefix tailTrace_3797702
  have hstable : (prefixWord ++ tailWord_3797702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797702).length < 2 ^ (prefixWord ++ tailWord_3797702).sum := by decide
  have hdescent : baseEnd_3797702 < baseStart_3797702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797707 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 2, 10]
def baseStart_3797707 : Nat := 118140960795 + 3797707 * 2 ^ 59
def prefixEnd_3797707 : Nat := 4983230072969 + 3 ^ 40 * 3797707 * 2
def baseEnd_3797707 : Nat := 650016358648159395865723

theorem tailTrace_3797707 : CollatzResearch.WordTrace tailWord_3797707 prefixEnd_3797707 650016358648159395865723 := by
  unfold tailWord_3797707
  simp only [CollatzResearch.WordTrace]
  refine ⟨138513753652563610563287375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92342502435042407042191583 138513753652563610563287375)
  ·
    refine ⟨207770630478845415844931063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138513753652563610563287375 207770630478845415844931063)
    ·
      refine ⟨311655945718268123767396595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207770630478845415844931063 311655945718268123767396595)
      ·
        refine ⟨467483918577402185651094893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311655945718268123767396595 467483918577402185651094893)
        ·
          refine ⟨175306469466525819619160585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467483918577402185651094893 175306469466525819619160585)
          ·
            refine ⟨131479852099894364714370439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175306469466525819619160585 131479852099894364714370439)
            ·
              refine ⟨197219778149841547071555659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131479852099894364714370439 197219778149841547071555659)
              ·
                refine ⟨295829667224762320607333489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197219778149841547071555659 295829667224762320607333489)
                ·
                  refine ⟨221872250418571740455500117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295829667224762320607333489 221872250418571740455500117)
                  ·
                    refine ⟨650016358648159395865723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 221872250418571740455500117 650016358648159395865723)
                    ·
                      rfl

theorem cell23_3797707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 10].length) (baseStart_3797707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797707 prefixEnd_3797707 := by exact prefixLift 3797707
  have htrace : WordTrace (prefixWord ++ tailWord_3797707) baseStart_3797707 baseEnd_3797707 := by
    simpa [prefixWord, tailWord_3797707, baseEnd_3797707] using wordTrace_append hprefix tailTrace_3797707
  have hstable : (prefixWord ++ tailWord_3797707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797707).length < 2 ^ (prefixWord ++ tailWord_3797707).sum := by decide
  have hdescent : baseEnd_3797707 < baseStart_3797707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797708 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3797708 : Nat := 118140960795 + 3797708 * 2 ^ 59
def prefixEnd_3797708 : Nat := 4983230072969 + 3 ^ 40 * 3797708 * 2
def baseEnd_3797708 : Nat := 1950049589425132683684665

theorem tailTrace_3797708 : CollatzResearch.WordTrace tailWord_3797708 prefixEnd_3797708 1950049589425132683684665 := by
  unfold tailWord_3797708
  simp only [CollatzResearch.WordTrace]
  refine ⟨69256895062779993867036889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92342526750373325156049185 69256895062779993867036889)
  ·
    refine ⟨51942671297084995400277667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69256895062779993867036889 51942671297084995400277667)
    ·
      refine ⟨77914006945627493100416501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51942671297084995400277667 77914006945627493100416501)
      ·
        refine ⟨7304438151152577478164047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77914006945627493100416501 7304438151152577478164047)
        ·
          refine ⟨10956657226728866217246071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7304438151152577478164047 10956657226728866217246071)
          ·
            refine ⟨16434985840093299325869107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10956657226728866217246071 16434985840093299325869107)
            ·
              refine ⟨24652478760139948988803661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16434985840093299325869107 24652478760139948988803661)
              ·
                refine ⟨9244679535052480870801373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24652478760139948988803661 9244679535052480870801373)
                ·
                  refine ⟨3466754825644680326550515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9244679535052480870801373 3466754825644680326550515)
                  ·
                    refine ⟨5200132238467020489825773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3466754825644680326550515 5200132238467020489825773)
                    ·
                      refine ⟨1950049589425132683684665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5200132238467020489825773 1950049589425132683684665)
                      ·
                        rfl

theorem cell23_3797708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3797708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797708 prefixEnd_3797708 := by exact prefixLift 3797708
  have htrace : WordTrace (prefixWord ++ tailWord_3797708) baseStart_3797708 baseEnd_3797708 := by
    simpa [prefixWord, tailWord_3797708, baseEnd_3797708] using wordTrace_append hprefix tailTrace_3797708
  have hstable : (prefixWord ++ tailWord_3797708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797708).length < 2 ^ (prefixWord ++ tailWord_3797708).sum := by decide
  have hdescent : baseEnd_3797708 < baseStart_3797708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797741 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_3797741 : Nat := 118140960795 + 3797741 * 2 ^ 59
def prefixEnd_3797741 : Nat := 4983230072969 + 3 ^ 40 * 3797741 * 2
def baseEnd_3797741 : Nat := 650022178095577018190671

theorem tailTrace_3797741 : CollatzResearch.WordTrace tailWord_3797741 prefixEnd_3797741 650022178095577018190671 := by
  unfold tailWord_3797741
  simp only [CollatzResearch.WordTrace]
  refine ⟨138514993734440434370025077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92343329156293622913350051 138514993734440434370025077)
  ·
    refine ⟨12985780662603790722189851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138514993734440434370025077 12985780662603790722189851)
    ·
      refine ⟨19478670993905686083284777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12985780662603790722189851 19478670993905686083284777)
      ·
        refine ⟨14609003245429264562463583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19478670993905686083284777 14609003245429264562463583)
        ·
          refine ⟨21913504868143896843695375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14609003245429264562463583 21913504868143896843695375)
          ·
            refine ⟨32870257302215845265543063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21913504868143896843695375 32870257302215845265543063)
            ·
              refine ⟨49305385953323767898314595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32870257302215845265543063 49305385953323767898314595)
              ·
                refine ⟨73958078929985651847471893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49305385953323767898314595 73958078929985651847471893)
                ·
                  refine ⟨3466784949843077430350245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73958078929985651847471893 3466784949843077430350245)
                  ·
                    refine ⟨650022178095577018190671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3466784949843077430350245 650022178095577018190671)
                    ·
                      rfl

theorem cell23_3797741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_3797741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797741 prefixEnd_3797741 := by exact prefixLift 3797741
  have htrace : WordTrace (prefixWord ++ tailWord_3797741) baseStart_3797741 baseEnd_3797741 := by
    simpa [prefixWord, tailWord_3797741, baseEnd_3797741] using wordTrace_append hprefix tailTrace_3797741
  have hstable : (prefixWord ++ tailWord_3797741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797741).length < 2 ^ (prefixWord ++ tailWord_3797741).sum := by decide
  have hdescent : baseEnd_3797741 < baseStart_3797741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797742 : List Nat := [4, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_3797742 : Nat := 118140960795 + 3797742 * 2 ^ 59
def prefixEnd_3797742 : Nat := 4983230072969 + 3 ^ 40 * 3797742 * 2
def baseEnd_3797742 : Nat := 1950067047767385550659509

theorem tailTrace_3797742 : CollatzResearch.WordTrace tailWord_3797742 prefixEnd_3797742 1950067047767385550659509 := by
  unfold tailWord_3797742
  simp only [CollatzResearch.WordTrace]
  refine ⟨17314378775929601442601435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92343353471624541027207653 17314378775929601442601435)
  ·
    refine ⟨25971568163894402163902153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17314378775929601442601435 25971568163894402163902153)
    ·
      refine ⟨19478676122920801622926615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25971568163894402163902153 19478676122920801622926615)
      ·
        refine ⟨29218014184381202434389923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19478676122920801622926615 29218014184381202434389923)
        ·
          refine ⟨43827021276571803651584885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29218014184381202434389923 43827021276571803651584885)
          ·
            refine ⟨4108783244678606592336083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43827021276571803651584885 4108783244678606592336083)
            ·
              refine ⟨6163174867017909888504125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4108783244678606592336083 6163174867017909888504125)
              ·
                refine ⟨2311190575131716208189047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6163174867017909888504125 2311190575131716208189047)
                ·
                  refine ⟨3466785862697574312283571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311190575131716208189047 3466785862697574312283571)
                  ·
                    refine ⟨5200178794046361468425357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3466785862697574312283571 5200178794046361468425357)
                    ·
                      refine ⟨1950067047767385550659509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5200178794046361468425357 1950067047767385550659509)
                      ·
                        rfl

theorem cell23_3797742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_3797742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797742 prefixEnd_3797742 := by exact prefixLift 3797742
  have htrace : WordTrace (prefixWord ++ tailWord_3797742) baseStart_3797742 baseEnd_3797742 := by
    simpa [prefixWord, tailWord_3797742, baseEnd_3797742] using wordTrace_append hprefix tailTrace_3797742
  have hstable : (prefixWord ++ tailWord_3797742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797742).length < 2 ^ (prefixWord ++ tailWord_3797742).sum := by decide
  have hdescent : baseEnd_3797742 < baseStart_3797742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797744 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 4]
def baseStart_3797744 : Nat := 118140960795 + 3797744 * 2 ^ 59
def prefixEnd_3797744 : Nat := 4983230072969 + 3 ^ 40 * 3797744 * 2
def baseEnd_3797744 : Nat := 1950068074728694542834499

theorem tailTrace_3797744 : CollatzResearch.WordTrace tailWord_3797744 prefixEnd_3797744 1950068074728694542834499 := by
  unfold tailWord_3797744
  simp only [CollatzResearch.WordTrace]
  refine ⟨69257551576714782941192143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92343402102286377254922857 69257551576714782941192143)
  ·
    refine ⟨103886327365072174411788215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69257551576714782941192143 103886327365072174411788215)
    ·
      refine ⟨155829491047608261617682323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103886327365072174411788215 155829491047608261617682323)
      ·
        refine ⟨233744236571412392426523485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155829491047608261617682323 233744236571412392426523485)
        ·
          refine ⟨87654088714279647159946307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233744236571412392426523485 87654088714279647159946307)
          ·
            refine ⟨131481133071419470739919461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87654088714279647159946307 131481133071419470739919461)
            ·
              refine ⟨24652712450891150763734899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131481133071419470739919461 24652712450891150763734899)
              ·
                refine ⟨36979068676336726145602349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24652712450891150763734899 36979068676336726145602349)
                ·
                  refine ⟨13867150753626272304600881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36979068676336726145602349 13867150753626272304600881)
                  ·
                    refine ⟨10400363065219704228450661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13867150753626272304600881 10400363065219704228450661)
                    ·
                      refine ⟨1950068074728694542834499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10400363065219704228450661 1950068074728694542834499)
                      ·
                        rfl

theorem cell23_3797744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_3797744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797744 prefixEnd_3797744 := by exact prefixLift 3797744
  have htrace : WordTrace (prefixWord ++ tailWord_3797744) baseStart_3797744 baseEnd_3797744 := by
    simpa [prefixWord, tailWord_3797744, baseEnd_3797744] using wordTrace_append hprefix tailTrace_3797744
  have hstable : (prefixWord ++ tailWord_3797744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797744).length < 2 ^ (prefixWord ++ tailWord_3797744).sum := by decide
  have hdescent : baseEnd_3797744 < baseStart_3797744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797758 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3797758 : Nat := 118140960795 + 3797758 * 2 ^ 59
def prefixEnd_3797758 : Nat := 4983230072969 + 3 ^ 40 * 3797758 * 2
def baseEnd_3797758 : Nat := 650025087819285829353145

theorem tailTrace_3797758 : CollatzResearch.WordTrace tailWord_3797758 prefixEnd_3797758 650025087819285829353145 := by
  unfold tailWord_3797758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17314451721922355784174241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92343742516919230848929285 17314451721922355784174241)
  ·
    refine ⟨12985838791441766838130681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17314451721922355784174241 12985838791441766838130681)
    ·
      refine ⟨9739379093581325128598011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12985838791441766838130681 9739379093581325128598011)
      ·
        refine ⟨14609068640371987692897017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9739379093581325128598011 14609068640371987692897017)
        ·
          refine ⟨10956801480278990769672763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14609068640371987692897017 10956801480278990769672763)
          ·
            refine ⟨16435202220418486154509145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10956801480278990769672763 16435202220418486154509145)
            ·
              refine ⟨12326401665313864615881859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16435202220418486154509145 12326401665313864615881859)
              ·
                refine ⟨18489602497970796923822789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12326401665313864615881859 18489602497970796923822789)
                ·
                  refine ⟨3466800468369524423216773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18489602497970796923822789 3466800468369524423216773)
                  ·
                    refine ⟨650025087819285829353145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3466800468369524423216773 650025087819285829353145)
                    ·
                      rfl

theorem cell23_3797758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3797758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797758 prefixEnd_3797758 := by exact prefixLift 3797758
  have htrace : WordTrace (prefixWord ++ tailWord_3797758) baseStart_3797758 baseEnd_3797758 := by
    simpa [prefixWord, tailWord_3797758, baseEnd_3797758] using wordTrace_append hprefix tailTrace_3797758
  have hstable : (prefixWord ++ tailWord_3797758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797758).length < 2 ^ (prefixWord ++ tailWord_3797758).sum := by decide
  have hdescent : baseEnd_3797758 < baseStart_3797758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797765 : List Nat := [1, 3, 1, 1, 2, 1, 1, 8, 1, 2, 2]
def baseStart_3797765 : Nat := 118140960795 + 3797765 * 2 ^ 59
def prefixEnd_3797765 : Nat := 4983230072969 + 3 ^ 40 * 3797765 * 2
def baseEnd_3797765 : Nat := 1950078857822438960671903

theorem tailTrace_3797765 : CollatzResearch.WordTrace tailWord_3797765 prefixEnd_3797765 1950078857822438960671903 := by
  unfold tailWord_3797765
  simp only [CollatzResearch.WordTrace]
  refine ⟨138515869086353486468898749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92343912724235657645932499 138515869086353486468898749)
  ·
    refine ⟨51943450907382557425837031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138515869086353486468898749 51943450907382557425837031)
    ·
      refine ⟨77915176361073836138755547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51943450907382557425837031 77915176361073836138755547)
      ·
        refine ⟨116872764541610754208133321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77915176361073836138755547 116872764541610754208133321)
        ·
          refine ⟨87654573406208065656099991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116872764541610754208133321 87654573406208065656099991)
          ·
            refine ⟨131481860109312098484149987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87654573406208065656099991 131481860109312098484149987)
            ·
              refine ⟨197222790163968147726224981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131481860109312098484149987 197222790163968147726224981)
              ·
                refine ⟨2311204572234001731166699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 197222790163968147726224981 2311204572234001731166699)
                ·
                  refine ⟨3466806858351002596750049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311204572234001731166699 3466806858351002596750049)
                  ·
                    refine ⟨2600105143763251947562537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3466806858351002596750049 2600105143763251947562537)
                    ·
                      refine ⟨1950078857822438960671903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2600105143763251947562537 1950078857822438960671903)
                      ·
                        rfl

theorem cell23_3797765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 1, 2, 2].length) (baseStart_3797765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797765 prefixEnd_3797765 := by exact prefixLift 3797765
  have htrace : WordTrace (prefixWord ++ tailWord_3797765) baseStart_3797765 baseEnd_3797765 := by
    simpa [prefixWord, tailWord_3797765, baseEnd_3797765] using wordTrace_append hprefix tailTrace_3797765
  have hstable : (prefixWord ++ tailWord_3797765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797765).length < 2 ^ (prefixWord ++ tailWord_3797765).sum := by decide
  have hdescent : baseEnd_3797765 < baseStart_3797765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797774 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3797774 : Nat := 118140960795 + 3797774 * 2 ^ 59
def prefixEnd_3797774 : Nat := 4983230072969 + 3 ^ 40 * 3797774 * 2
def baseEnd_3797774 : Nat := 1950083479148329425459361

theorem tailTrace_3797774 : CollatzResearch.WordTrace tailWord_3797774 prefixEnd_3797774 1950083479148329425459361 := by
  unfold tailWord_3797774
  simp only [CollatzResearch.WordTrace]
  refine ⟨17314524667915110125747047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92344131562213920670650917 17314524667915110125747047)
  ·
    refine ⟨25971787001872665188620571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17314524667915110125747047 25971787001872665188620571)
    ·
      refine ⟨38957680502808997782930857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25971787001872665188620571 38957680502808997782930857)
      ·
        refine ⟨29218260377106748337198143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38957680502808997782930857 29218260377106748337198143)
        ·
          refine ⟨43827390565660122505797215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29218260377106748337198143 43827390565660122505797215)
          ·
            refine ⟨65741085848490183758695823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43827390565660122505797215 65741085848490183758695823)
            ·
              refine ⟨98611628772735275638043735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65741085848490183758695823 98611628772735275638043735)
              ·
                refine ⟨147917443159102913457065603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98611628772735275638043735 147917443159102913457065603)
                ·
                  refine ⟨221876164738654370185598405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147917443159102913457065603 221876164738654370185598405)
                  ·
                    refine ⟨41601780888497694409799701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221876164738654370185598405 41601780888497694409799701)
                    ·
                      refine ⟨1950083479148329425459361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41601780888497694409799701 1950083479148329425459361)
                      ·
                        rfl

theorem cell23_3797774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3797774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797774 prefixEnd_3797774 := by exact prefixLift 3797774
  have htrace : WordTrace (prefixWord ++ tailWord_3797774) baseStart_3797774 baseEnd_3797774 := by
    simpa [prefixWord, tailWord_3797774, baseEnd_3797774] using wordTrace_append hprefix tailTrace_3797774
  have hstable : (prefixWord ++ tailWord_3797774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797774).length < 2 ^ (prefixWord ++ tailWord_3797774).sum := by decide
  have hdescent : baseEnd_3797774 < baseStart_3797774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797781 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_3797781 : Nat := 118140960795 + 3797781 * 2 ^ 59
def prefixEnd_3797781 : Nat := 4983230072969 + 3 ^ 40 * 3797781 * 2
def baseEnd_3797781 : Nat := 1950087073512910898071829

theorem tailTrace_3797781 : CollatzResearch.WordTrace tailWord_3797781 prefixEnd_3797781 1950087073512910898071829 := by
  unfold tailWord_3797781
  simp only [CollatzResearch.WordTrace]
  refine ⟨138516452654295521201481197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92344301769530347467654131 138516452654295521201481197)
  ·
    refine ⟨51943669745360820450555449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138516452654295521201481197 51943669745360820450555449)
    ·
      refine ⟨38957752309020615337916587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51943669745360820450555449 38957752309020615337916587)
      ·
        refine ⟨58436628463530923006874881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38957752309020615337916587 58436628463530923006874881)
        ·
          refine ⟨43827471347648192255156161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58436628463530923006874881 43827471347648192255156161)
          ·
            refine ⟨32870603510736144191367121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43827471347648192255156161 32870603510736144191367121)
            ·
              refine ⟨24652952633052108143525341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32870603510736144191367121 24652952633052108143525341)
              ·
                refine ⟨9244857237394540553822003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24652952633052108143525341 9244857237394540553822003)
                ·
                  refine ⟨13867285856091810830733005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9244857237394540553822003 13867285856091810830733005)
                  ·
                    refine ⟨5200232196034429061524877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13867285856091810830733005 5200232196034429061524877)
                    ·
                      refine ⟨1950087073512910898071829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5200232196034429061524877 1950087073512910898071829)
                      ·
                        rfl

theorem cell23_3797781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_3797781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797781 prefixEnd_3797781 := by exact prefixLift 3797781
  have htrace : WordTrace (prefixWord ++ tailWord_3797781) baseStart_3797781 baseEnd_3797781 := by
    simpa [prefixWord, tailWord_3797781, baseEnd_3797781] using wordTrace_append hprefix tailTrace_3797781
  have hstable : (prefixWord ++ tailWord_3797781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797781).length < 2 ^ (prefixWord ++ tailWord_3797781).sum := by decide
  have hdescent : baseEnd_3797781 < baseStart_3797781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797802 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3797802 : Nat := 118140960795 + 3797802 * 2 ^ 59
def prefixEnd_3797802 : Nat := 4983230072969 + 3 ^ 40 * 3797802 * 2
def baseEnd_3797802 : Nat := 1950097856606655315909233

theorem tailTrace_3797802 : CollatzResearch.WordTrace tailWord_3797802 prefixEnd_3797802 1950097856606655315909233 := by
  unfold tailWord_3797802
  simp only [CollatzResearch.WordTrace]
  refine ⟨34629304646804860446998915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92344812391479627858663773 34629304646804860446998915)
  ·
    refine ⟨51943956970207290670498373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34629304646804860446998915 51943956970207290670498373)
    ·
      refine ⟨9739491931913867000718445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51943956970207290670498373 9739491931913867000718445)
      ·
        refine ⟨3652309474467700125269417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9739491931913867000718445 3652309474467700125269417)
        ·
          refine ⟨2739232105850775093952063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3652309474467700125269417 2739232105850775093952063)
          ·
            refine ⟨4108848158776162640928095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739232105850775093952063 4108848158776162640928095)
            ·
              refine ⟨6163272238164243961392143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4108848158776162640928095 6163272238164243961392143)
              ·
                refine ⟨9244908357246365942088215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6163272238164243961392143 9244908357246365942088215)
                ·
                  refine ⟨13867362535869548913132323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9244908357246365942088215 13867362535869548913132323)
                  ·
                    refine ⟨20801043803804323369698485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13867362535869548913132323 20801043803804323369698485)
                    ·
                      refine ⟨1950097856606655315909233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20801043803804323369698485 1950097856606655315909233)
                      ·
                        rfl

theorem cell23_3797802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3797802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797802 prefixEnd_3797802 := by exact prefixLift 3797802
  have htrace : WordTrace (prefixWord ++ tailWord_3797802) baseStart_3797802 baseEnd_3797802 := by
    simpa [prefixWord, tailWord_3797802, baseEnd_3797802] using wordTrace_append hprefix tailTrace_3797802
  have hstable : (prefixWord ++ tailWord_3797802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797802).length < 2 ^ (prefixWord ++ tailWord_3797802).sum := by decide
  have hdescent : baseEnd_3797802 < baseStart_3797802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797808 : List Nat := [2, 1, 1, 1, 2, 2, 1, 7, 1, 3, 2]
def baseStart_3797808 : Nat := 118140960795 + 3797808 * 2 ^ 59
def prefixEnd_3797808 : Nat := 4983230072969 + 3 ^ 40 * 3797808 * 2
def baseEnd_3797808 : Nat := 1950100937490582292434205

theorem tailTrace_3797808 : CollatzResearch.WordTrace tailWord_3797808 prefixEnd_3797808 1950100937490582292434205 := by
  unfold tailWord_3797808
  simp only [CollatzResearch.WordTrace]
  refine ⟨69258718712598852406357039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92344958283465136541809385 69258718712598852406357039)
  ·
    refine ⟨103888078068898278609535559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69258718712598852406357039 103888078068898278609535559)
    ·
      refine ⟨155832117103347417914303339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103888078068898278609535559 155832117103347417914303339)
      ·
        refine ⟨233748175655021126871455009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155832117103347417914303339 233748175655021126871455009)
        ·
          refine ⟨175311131741265845153591257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233748175655021126871455009 175311131741265845153591257)
          ·
            refine ⟨131483348805949383865193443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175311131741265845153591257 131483348805949383865193443)
            ·
              refine ⟨197225023208924075797790165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131483348805949383865193443 197225023208924075797790165)
              ·
                refine ⟨4622461481459158026510707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 197225023208924075797790165 4622461481459158026510707)
                ·
                  refine ⟨6933692222188737039766061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4622461481459158026510707 6933692222188737039766061)
                  ·
                    refine ⟨2600134583320776389912273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6933692222188737039766061 2600134583320776389912273)
                    ·
                      refine ⟨1950100937490582292434205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2600134583320776389912273 1950100937490582292434205)
                      ·
                        rfl

theorem cell23_3797808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 1, 3, 2].length) (baseStart_3797808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797808 prefixEnd_3797808 := by exact prefixLift 3797808
  have htrace : WordTrace (prefixWord ++ tailWord_3797808) baseStart_3797808 baseEnd_3797808 := by
    simpa [prefixWord, tailWord_3797808, baseEnd_3797808] using wordTrace_append hprefix tailTrace_3797808
  have hstable : (prefixWord ++ tailWord_3797808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797808).length < 2 ^ (prefixWord ++ tailWord_3797808).sum := by decide
  have hdescent : baseEnd_3797808 < baseStart_3797808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797824 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 5]
def baseStart_3797824 : Nat := 118140960795 + 3797824 * 2 ^ 59
def prefixEnd_3797824 : Nat := 4983230072969 + 3 ^ 40 * 3797824 * 2
def baseEnd_3797824 : Nat := 1950109153181054229834131

theorem tailTrace_3797824 : CollatzResearch.WordTrace tailWord_3797824 prefixEnd_3797824 1950109153181054229834131 := by
  unfold tailWord_3797824
  simp only [CollatzResearch.WordTrace]
  refine ⟨69259010496569869772648263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92345347328759826363531017 69259010496569869772648263)
  ·
    refine ⟨103888515744854804658972395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69259010496569869772648263 103888515744854804658972395)
    ·
      refine ⟨155832773617282206988458593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103888515744854804658972395 155832773617282206988458593)
      ·
        refine ⟨116874580212961655241343945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155832773617282206988458593 116874580212961655241343945)
        ·
          refine ⟨87655935159721241431007959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116874580212961655241343945 87655935159721241431007959)
          ·
            refine ⟨131483902739581862146511939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87655935159721241431007959 131483902739581862146511939)
            ·
              refine ⟨197225854109372793219767909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131483902739581862146511939 197225854109372793219767909)
              ·
                refine ⟨36979847645507398728706483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197225854109372793219767909 36979847645507398728706483)
                ·
                  refine ⟨55469771468261098093059725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36979847645507398728706483 55469771468261098093059725)
                  ·
                    refine ⟨20801164300597911784897397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55469771468261098093059725 20801164300597911784897397)
                    ·
                      refine ⟨1950109153181054229834131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20801164300597911784897397 1950109153181054229834131)
                      ·
                        rfl

theorem cell23_3797824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_3797824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797824 prefixEnd_3797824 := by exact prefixLift 3797824
  have htrace : WordTrace (prefixWord ++ tailWord_3797824) baseStart_3797824 baseEnd_3797824 := by
    simpa [prefixWord, tailWord_3797824, baseEnd_3797824] using wordTrace_append hprefix tailTrace_3797824
  have hstable : (prefixWord ++ tailWord_3797824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797824).length < 2 ^ (prefixWord ++ tailWord_3797824).sum := by decide
  have hdescent : baseEnd_3797824 < baseStart_3797824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797878 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_3797878 : Nat := 118140960795 + 3797878 * 2 ^ 59
def prefixEnd_3797878 : Nat := 4983230072969 + 3 ^ 40 * 3797878 * 2
def baseEnd_3797878 : Nat := 216681875681821890950987

theorem tailTrace_3797878 : CollatzResearch.WordTrace tailWord_3797878 prefixEnd_3797878 216681875681821890950987 := by
  unfold tailWord_3797878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8657499408434006672985143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92346660356629404511841525 8657499408434006672985143)
  ·
    refine ⟨12986249112651010009477715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8657499408434006672985143 12986249112651010009477715)
    ·
      refine ⟨19479373668976515014216573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12986249112651010009477715 19479373668976515014216573)
      ·
        refine ⟨7304765125866193130331215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19479373668976515014216573 7304765125866193130331215)
        ·
          refine ⟨10957147688799289695496823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7304765125866193130331215 10957147688799289695496823)
          ·
            refine ⟨16435721533198934543245235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10957147688799289695496823 16435721533198934543245235)
            ·
              refine ⟨24653582299798401814867853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16435721533198934543245235 24653582299798401814867853)
              ·
                refine ⟨9245093362424400680575445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24653582299798401814867853 9245093362424400680575445)
                ·
                  refine ⟨216681875681821890950987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9245093362424400680575445 216681875681821890950987)
                  ·
                    rfl

theorem cell23_3797878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_3797878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797878 prefixEnd_3797878 := by exact prefixLift 3797878
  have htrace : WordTrace (prefixWord ++ tailWord_3797878) baseStart_3797878 baseEnd_3797878 := by
    simpa [prefixWord, tailWord_3797878, baseEnd_3797878] using wordTrace_append hprefix tailTrace_3797878
  have hstable : (prefixWord ++ tailWord_3797878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797878).length < 2 ^ (prefixWord ++ tailWord_3797878).sum := by decide
  have hdescent : baseEnd_3797878 < baseStart_3797878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797908 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_3797908 : Nat := 118140960795 + 3797908 * 2 ^ 59
def prefixEnd_3797908 : Nat := 4983230072969 + 3 ^ 40 * 3797908 * 2
def baseEnd_3797908 : Nat := 650050761852010633727915

theorem tailTrace_3797908 : CollatzResearch.WordTrace tailWord_3797908 prefixEnd_3797908 650050761852010633727915 := by
  unfold tailWord_3797908
  simp only [CollatzResearch.WordTrace]
  refine ⟨69260542362417710945677189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92347389816556947927569585 69260542362417710945677189)
  ·
    refine ⟨12986351692953320802314473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69260542362417710945677189 12986351692953320802314473)
    ·
      refine ⟨9739763769714990601735855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12986351692953320802314473 9739763769714990601735855)
      ·
        refine ⟨14609645654572485902603783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9739763769714990601735855 14609645654572485902603783)
        ·
          refine ⟨21914468481858728853905675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14609645654572485902603783 21914468481858728853905675)
          ·
            refine ⟨32871702722788093280858513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21914468481858728853905675 32871702722788093280858513)
            ·
              refine ⟨24653777042091069960643885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32871702722788093280858513 24653777042091069960643885)
              ·
                refine ⟨9245166390784151235241457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24653777042091069960643885 9245166390784151235241457)
                ·
                  refine ⟨6933874793088113426431093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9245166390784151235241457 6933874793088113426431093)
                  ·
                    refine ⟨650050761852010633727915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6933874793088113426431093 650050761852010633727915)
                    ·
                      rfl

theorem cell23_3797908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_3797908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797908 prefixEnd_3797908 := by exact prefixLift 3797908
  have htrace : WordTrace (prefixWord ++ tailWord_3797908) baseStart_3797908 baseEnd_3797908 := by
    simpa [prefixWord, tailWord_3797908, baseEnd_3797908] using wordTrace_append hprefix tailTrace_3797908
  have hstable : (prefixWord ++ tailWord_3797908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797908).length < 2 ^ (prefixWord ++ tailWord_3797908).sum := by decide
  have hdescent : baseEnd_3797908 < baseStart_3797908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797911 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_3797911 : Nat := 118140960795 + 3797911 * 2 ^ 59
def prefixEnd_3797911 : Nat := 4983230072969 + 3 ^ 40 * 3797911 * 2
def baseEnd_3797911 : Nat := 1950153825997995389446231

theorem tailTrace_3797911 : CollatzResearch.WordTrace tailWord_3797911 prefixEnd_3797911 1950153825997995389446231 := by
  unfold tailWord_3797911
  simp only [CollatzResearch.WordTrace]
  refine ⟨138521194143824553403713587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92347462762549702269142391 138521194143824553403713587)
  ·
    refine ⟨207781791215736830105570381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138521194143824553403713587 207781791215736830105570381)
    ·
      refine ⟨77918171705901311289588893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207781791215736830105570381 77918171705901311289588893)
      ·
        refine ⟨29219314389712991733595835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77918171705901311289588893 29219314389712991733595835)
        ·
          refine ⟨43828971584569487600393753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29219314389712991733595835 43828971584569487600393753)
          ·
            refine ⟨32871728688427115700295315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43828971584569487600393753 32871728688427115700295315)
            ·
              refine ⟨49307593032640673550442973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32871728688427115700295315 49307593032640673550442973)
              ·
                refine ⟨18490347387240252581416115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49307593032640673550442973 18490347387240252581416115)
                ·
                  refine ⟨27735521080860378872124173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18490347387240252581416115 27735521080860378872124173)
                  ·
                    refine ⟨10400820405322642077046565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27735521080860378872124173 10400820405322642077046565)
                    ·
                      refine ⟨1950153825997995389446231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10400820405322642077046565 1950153825997995389446231)
                      ·
                        rfl

theorem cell23_3797911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_3797911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797911 prefixEnd_3797911 := by exact prefixLift 3797911
  have htrace : WordTrace (prefixWord ++ tailWord_3797911) baseStart_3797911 baseEnd_3797911 := by
    simpa [prefixWord, tailWord_3797911, baseEnd_3797911] using wordTrace_append hprefix tailTrace_3797911
  have hstable : (prefixWord ++ tailWord_3797911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797911).length < 2 ^ (prefixWord ++ tailWord_3797911).sum := by decide
  have hdescent : baseEnd_3797911 < baseStart_3797911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797989 : List Nat := [1, 3, 1, 6, 1, 1, 1, 4, 1, 4]
def baseStart_3797989 : Nat := 118140960795 + 3797989 * 2 ^ 59
def prefixEnd_3797989 : Nat := 4983230072969 + 3 ^ 40 * 3797989 * 2
def baseEnd_3797989 : Nat := 650064625829682028090291

theorem tailTrace_3797989 : CollatzResearch.WordTrace tailWord_3797989 prefixEnd_3797989 650064625829682028090291 := by
  unfold tailWord_3797989
  simp only [CollatzResearch.WordTrace]
  refine ⟨138524039037541972725053021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92349359358361315150035347 138524039037541972725053021)
  ·
    refine ⟨51946514639078239771894883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138524039037541972725053021 51946514639078239771894883)
    ·
      refine ⟨77919771958617359657842325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51946514639078239771894883 77919771958617359657842325)
      ·
        refine ⟨3652489310560188733961359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77919771958617359657842325 3652489310560188733961359)
        ·
          refine ⟨5478733965840283100942039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652489310560188733961359 5478733965840283100942039)
          ·
            refine ⟨8218100948760424651413059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5478733965840283100942039 8218100948760424651413059)
            ·
              refine ⟨12327151423140636977119589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218100948760424651413059 12327151423140636977119589)
              ·
                refine ⟨2311340891838869433209923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12327151423140636977119589 2311340891838869433209923)
                ·
                  refine ⟨3467011337758304149814885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311340891838869433209923 3467011337758304149814885)
                  ·
                    refine ⟨650064625829682028090291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3467011337758304149814885 650064625829682028090291)
                    ·
                      rfl

theorem cell23_3797989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_3797989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3797989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3797989 prefixEnd_3797989 := by exact prefixLift 3797989
  have htrace : WordTrace (prefixWord ++ tailWord_3797989) baseStart_3797989 baseEnd_3797989 := by
    simpa [prefixWord, tailWord_3797989, baseEnd_3797989] using wordTrace_append hprefix tailTrace_3797989
  have hstable : (prefixWord ++ tailWord_3797989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797989).length < 2 ^ (prefixWord ++ tailWord_3797989).sum := by decide
  have hdescent : baseEnd_3797989 < baseStart_3797989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798028 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 1, 6]
def baseStart_3798028 : Nat := 118140960795 + 3798028 * 2 ^ 59
def prefixEnd_3798028 : Nat := 4983230072969 + 3 ^ 40 * 3798028 * 2
def baseEnd_3798028 : Nat := 650071301078190477227731

theorem tailTrace_3798028 : CollatzResearch.WordTrace tailWord_3798028 prefixEnd_3798028 650071301078190477227731 := by
  unfold tailWord_3798028
  simp only [CollatzResearch.WordTrace]
  refine ⟨69262730742200341192861369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92350307656267121590481825 69262730742200341192861369)
  ·
    refine ⟨51947048056650255894646027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69262730742200341192861369 51947048056650255894646027)
    ·
      refine ⟨77920572084975383841969041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51947048056650255894646027 77920572084975383841969041)
      ·
        refine ⟨58440429063731537881476781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77920572084975383841969041 58440429063731537881476781)
        ·
          refine ⟨21915160898899326705553793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58440429063731537881476781 21915160898899326705553793)
          ·
            refine ⟨16436370674174495029165345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21915160898899326705553793 16436370674174495029165345)
            ·
              refine ⟨12327278005630871271874009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16436370674174495029165345 12327278005630871271874009)
              ·
                refine ⟨9245458504223153453905507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12327278005630871271874009 9245458504223153453905507)
                ·
                  refine ⟨13868187756334730180858261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9245458504223153453905507 13868187756334730180858261)
                  ·
                    refine ⟨650071301078190477227731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13868187756334730180858261 650071301078190477227731)
                    ·
                      rfl

theorem cell23_3798028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_3798028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798028 prefixEnd_3798028 := by exact prefixLift 3798028
  have htrace : WordTrace (prefixWord ++ tailWord_3798028) baseStart_3798028 baseEnd_3798028 := by
    simpa [prefixWord, tailWord_3798028, baseEnd_3798028] using wordTrace_append hprefix tailTrace_3798028
  have hstable : (prefixWord ++ tailWord_3798028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798028).length < 2 ^ (prefixWord ++ tailWord_3798028).sum := by decide
  have hdescent : baseEnd_3798028 < baseStart_3798028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798035 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 7, 2, 2]
def baseStart_3798035 : Nat := 118140960795 + 3798035 * 2 ^ 59
def prefixEnd_3798035 : Nat := 4983230072969 + 3 ^ 40 * 3798035 * 2
def baseEnd_3798035 : Nat := 1950217497599152904295661

theorem tailTrace_3798035 : CollatzResearch.WordTrace tailWord_3798035 prefixEnd_3798035 1950217497599152904295661 := by
  unfold tailWord_3798035
  simp only [CollatzResearch.WordTrace]
  refine ⟨138525716795375322581227559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92350477863583548387485039 138525716795375322581227559)
  ·
    refine ⟨207788575193062983871841339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138525716795375322581227559 207788575193062983871841339)
    ·
      refine ⟨311682862789594475807762009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207788575193062983871841339 311682862789594475807762009)
      ·
        refine ⟨233762147092195856855821507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311682862789594475807762009 233762147092195856855821507)
        ·
          refine ⟨350643220638293785283732261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233762147092195856855821507 350643220638293785283732261)
          ·
            refine ⟨65745603869680084740699799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 350643220638293785283732261 65745603869680084740699799)
            ·
              refine ⟨98618405804520127111049699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65745603869680084740699799 98618405804520127111049699)
              ·
                refine ⟨147927608706780190666574549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98618405804520127111049699 147927608706780190666574549)
                ·
                  refine ⟨3467053329065160718747841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 147927608706780190666574549 3467053329065160718747841)
                  ·
                    refine ⟨2600289996798870539060881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3467053329065160718747841 2600289996798870539060881)
                    ·
                      refine ⟨1950217497599152904295661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2600289996798870539060881 1950217497599152904295661)
                      ·
                        rfl

theorem cell23_3798035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 2, 2].length) (baseStart_3798035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798035 prefixEnd_3798035 := by exact prefixLift 3798035
  have htrace : WordTrace (prefixWord ++ tailWord_3798035) baseStart_3798035 baseEnd_3798035 := by
    simpa [prefixWord, tailWord_3798035, baseEnd_3798035] using wordTrace_append hprefix tailTrace_3798035
  have hstable : (prefixWord ++ tailWord_3798035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798035).length < 2 ^ (prefixWord ++ tailWord_3798035).sum := by decide
  have hdescent : baseEnd_3798035 < baseStart_3798035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798055 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3798055 : Nat := 118140960795 + 3798055 * 2 ^ 59
def prefixEnd_3798055 : Nat := 4983230072969 + 3 ^ 40 * 3798055 * 2
def baseEnd_3798055 : Nat := 1950227767212242826045569

theorem tailTrace_3798055 : CollatzResearch.WordTrace tailWord_3798055 prefixEnd_3798055 1950227767212242826045569 := by
  unfold tailWord_3798055
  simp only [CollatzResearch.WordTrace]
  refine ⟨138526446255302865996955619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92350964170201910664637079 138526446255302865996955619)
  ·
    refine ⟨207789669382954298995433429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138526446255302865996955619 207789669382954298995433429)
    ·
      refine ⟨4870070376162991382705471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 207789669382954298995433429 4870070376162991382705471)
      ·
        refine ⟨7305105564244487074058207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4870070376162991382705471 7305105564244487074058207)
        ·
          refine ⟨10957658346366730611087311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7305105564244487074058207 10957658346366730611087311)
          ·
            refine ⟨16436487519550095916630967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10957658346366730611087311 16436487519550095916630967)
            ·
              refine ⟨24654731279325143874946451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16436487519550095916630967 24654731279325143874946451)
              ·
                refine ⟨36982096918987715812419677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24654731279325143874946451 36982096918987715812419677)
                ·
                  refine ⟨13868286344620393429657379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36982096918987715812419677 13868286344620393429657379)
                  ·
                    refine ⟨20802429516930590144486069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13868286344620393429657379 20802429516930590144486069)
                    ·
                      refine ⟨1950227767212242826045569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20802429516930590144486069 1950227767212242826045569)
                      ·
                        rfl

theorem cell23_3798055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3798055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798055 prefixEnd_3798055 := by exact prefixLift 3798055
  have htrace : WordTrace (prefixWord ++ tailWord_3798055) baseStart_3798055 baseEnd_3798055 := by
    simpa [prefixWord, tailWord_3798055, baseEnd_3798055] using wordTrace_append hprefix tailTrace_3798055
  have hstable : (prefixWord ++ tailWord_3798055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798055).length < 2 ^ (prefixWord ++ tailWord_3798055).sum := by decide
  have hdescent : baseEnd_3798055 < baseStart_3798055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798072 : List Nat := [2, 1, 2, 1, 5, 2, 2, 2, 1, 2, 3]
def baseStart_3798072 : Nat := 118140960795 + 3798072 * 2 ^ 59
def prefixEnd_3798072 : Nat := 4983230072969 + 3 ^ 40 * 3798072 * 2
def baseEnd_3798072 : Nat := 1950236496383369259532991

theorem tailTrace_3798072 : CollatzResearch.WordTrace tailWord_3798072 prefixEnd_3798072 1950236496383369259532991 := by
  unfold tailWord_3798072
  simp only [CollatzResearch.WordTrace]
  refine ⟨69263533148120638950162235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92351377530827518600216313 69263533148120638950162235)
  ·
    refine ⟨103895299722180958425243353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69263533148120638950162235 103895299722180958425243353)
    ·
      refine ⟨77921474791635718818932515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103895299722180958425243353 77921474791635718818932515)
      ·
        refine ⟨116882212187453578228398773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77921474791635718818932515 116882212187453578228398773)
        ·
          refine ⟨10957707392573772958912385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116882212187453578228398773 10957707392573772958912385)
          ·
            refine ⟨8218280544430329719184289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10957707392573772958912385 8218280544430329719184289)
            ·
              refine ⟨6163710408322747289388217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8218280544430329719184289 6163710408322747289388217)
              ·
                refine ⟨4622782806242060467041163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6163710408322747289388217 4622782806242060467041163)
                ·
                  refine ⟨6934174209363090700561745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4622782806242060467041163 6934174209363090700561745)
                  ·
                    refine ⟨5200630657022318025421309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6934174209363090700561745 5200630657022318025421309)
                    ·
                      refine ⟨1950236496383369259532991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5200630657022318025421309 1950236496383369259532991)
                      ·
                        rfl

theorem cell23_3798072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_3798072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798072 prefixEnd_3798072 := by exact prefixLift 3798072
  have htrace : WordTrace (prefixWord ++ tailWord_3798072) baseStart_3798072 baseEnd_3798072 := by
    simpa [prefixWord, tailWord_3798072, baseEnd_3798072] using wordTrace_append hprefix tailTrace_3798072
  have hstable : (prefixWord ++ tailWord_3798072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798072).length < 2 ^ (prefixWord ++ tailWord_3798072).sum := by decide
  have hdescent : baseEnd_3798072 < baseStart_3798072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798085 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 4, 1, 3]
def baseStart_3798085 : Nat := 118140960795 + 3798085 * 2 ^ 59
def prefixEnd_3798085 : Nat := 4983230072969 + 3 ^ 40 * 3798085 * 2
def baseEnd_3798085 : Nat := 1950243171631877708670431

theorem tailTrace_3798085 : CollatzResearch.WordTrace tailWord_3798085 prefixEnd_3798085 1950243171631877708670431 := by
  unfold tailWord_3798085
  simp only [CollatzResearch.WordTrace]
  refine ⟨138527540445194181120547709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92351693630129454080365139 138527540445194181120547709)
  ·
    refine ⟨51947827666947817920205391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138527540445194181120547709 51947827666947817920205391)
    ·
      refine ⟨77921741500421726880308087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51947827666947817920205391 77921741500421726880308087)
      ·
        refine ⟨116882612250632590320462131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77921741500421726880308087 116882612250632590320462131)
        ·
          refine ⟨175323918375948885480693197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116882612250632590320462131 175323918375948885480693197)
          ·
            refine ⟨65746469390980832055259949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175323918375948885480693197 65746469390980832055259949)
            ·
              refine ⟨24654926021617812020722481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65746469390980832055259949 24654926021617812020722481)
              ·
                refine ⟨18491194516213359015541861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24654926021617812020722481 18491194516213359015541861)
                ·
                  refine ⟨3467098971790004815414099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18491194516213359015541861 3467098971790004815414099)
                  ·
                    refine ⟨5200648457685007223121149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3467098971790004815414099 5200648457685007223121149)
                    ·
                      refine ⟨1950243171631877708670431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5200648457685007223121149 1950243171631877708670431)
                      ·
                        rfl

theorem cell23_3798085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_3798085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798085 prefixEnd_3798085 := by exact prefixLift 3798085
  have htrace : WordTrace (prefixWord ++ tailWord_3798085) baseStart_3798085 baseEnd_3798085 := by
    simpa [prefixWord, tailWord_3798085, baseEnd_3798085] using wordTrace_append hprefix tailTrace_3798085
  have hstable : (prefixWord ++ tailWord_3798085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798085).length < 2 ^ (prefixWord ++ tailWord_3798085).sum := by decide
  have hdescent : baseEnd_3798085 < baseStart_3798085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798119 : List Nat := [1, 1, 5, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_3798119 : Nat := 118140960795 + 3798119 * 2 ^ 59
def prefixEnd_3798119 : Nat := 4983230072969 + 3 ^ 40 * 3798119 * 2
def baseEnd_3798119 : Nat := 1950260629974130575645275

theorem tailTrace_3798119 : CollatzResearch.WordTrace tailWord_3798119 prefixEnd_3798119 1950260629974130575645275 := by
  unfold tailWord_3798119
  simp only [CollatzResearch.WordTrace]
  refine ⟨138528780527071004927285411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92352520351380669951523607 138528780527071004927285411)
  ·
    refine ⟨207793170790606507390928117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138528780527071004927285411 207793170790606507390928117)
    ·
      refine ⟨19480609761619360067899511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207793170790606507390928117 19480609761619360067899511)
      ·
        refine ⟨29220914642429040101849267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19480609761619360067899511 29220914642429040101849267)
        ·
          refine ⟨43831371963643560152773901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29220914642429040101849267 43831371963643560152773901)
          ·
            refine ⟨16436764486366335057290213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43831371963643560152773901 16436764486366335057290213)
            ·
              refine ⟨3081893341193687823241915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16436764486366335057290213 3081893341193687823241915)
              ·
                refine ⟨4622840011790531734862873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081893341193687823241915 4622840011790531734862873)
                ·
                  refine ⟨3467130008842898801147155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4622840011790531734862873 3467130008842898801147155)
                  ·
                    refine ⟨5200695013264348201720733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3467130008842898801147155 5200695013264348201720733)
                    ·
                      refine ⟨1950260629974130575645275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5200695013264348201720733 1950260629974130575645275)
                      ·
                        rfl

theorem cell23_3798119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_3798119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798119 prefixEnd_3798119 := by exact prefixLift 3798119
  have htrace : WordTrace (prefixWord ++ tailWord_3798119) baseStart_3798119 baseEnd_3798119 := by
    simpa [prefixWord, tailWord_3798119, baseEnd_3798119] using wordTrace_append hprefix tailTrace_3798119
  have hstable : (prefixWord ++ tailWord_3798119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798119).length < 2 ^ (prefixWord ++ tailWord_3798119).sum := by decide
  have hdescent : baseEnd_3798119 < baseStart_3798119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798128 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 5]
def baseStart_3798128 : Nat := 118140960795 + 3798128 * 2 ^ 59
def prefixEnd_3798128 : Nat := 4983230072969 + 3 ^ 40 * 3798128 * 2
def baseEnd_3798128 : Nat := 1950265251300021040432733

theorem tailTrace_3798128 : CollatzResearch.WordTrace tailWord_3798128 prefixEnd_3798128 1950265251300021040432733 := by
  unfold tailWord_3798128
  simp only [CollatzResearch.WordTrace]
  refine ⟨69264554392019199732181519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92352739189358932976242025 69264554392019199732181519)
  ·
    refine ⟨103896831588028799598272279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69264554392019199732181519 103896831588028799598272279)
    ·
      refine ⟨155845247382043199397408419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103896831588028799598272279 155845247382043199397408419)
      ·
        refine ⟨233767871073064799096112629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155845247382043199397408419 233767871073064799096112629)
        ·
          refine ⟨21915737913099824915260559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233767871073064799096112629 21915737913099824915260559)
          ·
            refine ⟨32873606869649737372890839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21915737913099824915260559 32873606869649737372890839)
            ·
              refine ⟨49310410304474606059336259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32873606869649737372890839 49310410304474606059336259)
              ·
                refine ⟨73965615456711909089004389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49310410304474606059336259 73965615456711909089004389)
                ·
                  refine ⟨13868552898133482954188323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73965615456711909089004389 13868552898133482954188323)
                  ·
                    refine ⟨20802829347200224431282485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13868552898133482954188323 20802829347200224431282485)
                    ·
                      refine ⟨1950265251300021040432733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20802829347200224431282485 1950265251300021040432733)
                      ·
                        rfl

theorem cell23_3798128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_3798128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798128 prefixEnd_3798128 := by exact prefixLift 3798128
  have htrace : WordTrace (prefixWord ++ tailWord_3798128) baseStart_3798128 baseEnd_3798128 := by
    simpa [prefixWord, tailWord_3798128, baseEnd_3798128] using wordTrace_append hprefix tailTrace_3798128
  have hstable : (prefixWord ++ tailWord_3798128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798128).length < 2 ^ (prefixWord ++ tailWord_3798128).sum := by decide
  have hdescent : baseEnd_3798128 < baseStart_3798128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798145 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_3798145 : Nat := 118140960795 + 3798145 * 2 ^ 59
def prefixEnd_3798145 : Nat := 4983230072969 + 3 ^ 40 * 3798145 * 2
def baseEnd_3798145 : Nat := 1950273980471147473920155

theorem tailTrace_3798145 : CollatzResearch.WordTrace tailWord_3798145 prefixEnd_3798145 1950273980471147473920155 := by
  unfold tailWord_3798145
  simp only [CollatzResearch.WordTrace]
  refine ⟨138529728824976811367731889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92353152549984540911821259 138529728824976811367731889)
  ·
    refine ⟨103897296618732608525798917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138529728824976811367731889 103897296618732608525798917)
    ·
      refine ⟨19480743116012364098587297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103897296618732608525798917 19480743116012364098587297)
      ·
        refine ⟨14610557337009273073940473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19480743116012364098587297 14610557337009273073940473)
        ·
          refine ⟨10957918002756954805455355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14610557337009273073940473 10957918002756954805455355)
          ·
            refine ⟨16436877004135432208183033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10957918002756954805455355 16436877004135432208183033)
            ·
              refine ⟨12327657753101574156137275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16436877004135432208183033 12327657753101574156137275)
              ·
                refine ⟨18491486629652361234205913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12327657753101574156137275 18491486629652361234205913)
                ·
                  refine ⟨13868614972239270925654435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18491486629652361234205913 13868614972239270925654435)
                  ·
                    refine ⟨20802922458358906388481653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13868614972239270925654435 20802922458358906388481653)
                    ·
                      refine ⟨1950273980471147473920155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20802922458358906388481653 1950273980471147473920155)
                      ·
                        rfl

theorem cell23_3798145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_3798145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798145 prefixEnd_3798145 := by exact prefixLift 3798145
  have htrace : WordTrace (prefixWord ++ tailWord_3798145) baseStart_3798145 baseEnd_3798145 := by
    simpa [prefixWord, tailWord_3798145, baseEnd_3798145] using wordTrace_append hprefix tailTrace_3798145
  have hstable : (prefixWord ++ tailWord_3798145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798145).length < 2 ^ (prefixWord ++ tailWord_3798145).sum := by decide
  have hdescent : baseEnd_3798145 < baseStart_3798145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798188 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_3798188 : Nat := 118140960795 + 3798188 * 2 ^ 59
def prefixEnd_3798188 : Nat := 4983230072969 + 3 ^ 40 * 3798188 * 2
def baseEnd_3798188 : Nat := 1950296060139290805682457

theorem tailTrace_3798188 : CollatzResearch.WordTrace tailWord_3798188 prefixEnd_3798188 1950296060139290805682457 := by
  unfold tailWord_3798188
  simp only [CollatzResearch.WordTrace]
  refine ⟨69265648581910514855773609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92354198109214019807698145 69265648581910514855773609)
  ·
    refine ⟨51949236436432886141830207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69265648581910514855773609 51949236436432886141830207)
    ·
      refine ⟨77923854654649329212745311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51949236436432886141830207 77923854654649329212745311)
      ·
        refine ⟨116885781981973993819117967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77923854654649329212745311 116885781981973993819117967)
        ·
          refine ⟨175328672972960990728676951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116885781981973993819117967 175328672972960990728676951)
          ·
            refine ⟨262993009459441486093015427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175328672972960990728676951 262993009459441486093015427)
            ·
              refine ⟨394489514189162229139523141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262993009459441486093015427 394489514189162229139523141)
              ·
                refine ⟨73966783910467917963660589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394489514189162229139523141 73966783910467917963660589)
                ·
                  refine ⟨27737543966425469236372721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73966783910467917963660589 27737543966425469236372721)
                  ·
                    refine ⟨20803157974819101927279541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27737543966425469236372721 20803157974819101927279541)
                    ·
                      refine ⟨1950296060139290805682457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20803157974819101927279541 1950296060139290805682457)
                      ·
                        rfl

theorem cell23_3798188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_3798188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798188 prefixEnd_3798188 := by exact prefixLift 3798188
  have htrace : WordTrace (prefixWord ++ tailWord_3798188) baseStart_3798188 baseEnd_3798188 := by
    simpa [prefixWord, tailWord_3798188, baseEnd_3798188] using wordTrace_append hprefix tailTrace_3798188
  have hstable : (prefixWord ++ tailWord_3798188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798188).length < 2 ^ (prefixWord ++ tailWord_3798188).sum := by decide
  have hdescent : baseEnd_3798188 < baseStart_3798188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798195 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 2, 5]
def baseStart_3798195 : Nat := 118140960795 + 3798195 * 2 ^ 59
def prefixEnd_3798195 : Nat := 4983230072969 + 3 ^ 40 * 3798195 * 2
def baseEnd_3798195 : Nat := 650099884834624092764975

theorem tailTrace_3798195 : CollatzResearch.WordTrace tailWord_3798195 prefixEnd_3798195 650099884834624092764975 := by
  unfold tailWord_3798195
  simp only [CollatzResearch.WordTrace]
  refine ⟨138531552474795669907052039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92354368316530446604701359 138531552474795669907052039)
  ·
    refine ⟨207797328712193504860578059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138531552474795669907052039 207797328712193504860578059)
    ·
      refine ⟨311695993068290257290867089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207797328712193504860578059 311695993068290257290867089)
      ·
        refine ⟨233771994801217692968150317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311695993068290257290867089 233771994801217692968150317)
        ·
          refine ⟨87664498050456634863056369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233771994801217692968150317 87664498050456634863056369)
          ·
            refine ⟨65748373537842476147292277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87664498050456634863056369 65748373537842476147292277)
            ·
              refine ⟨6163910019172732138808651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65748373537842476147292277 6163910019172732138808651)
              ·
                refine ⟨9245865028759098208212977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6163910019172732138808651 9245865028759098208212977)
                ·
                  refine ⟨6934398771569323656159733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9245865028759098208212977 6934398771569323656159733)
                  ·
                    refine ⟨650099884834624092764975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6934398771569323656159733 650099884834624092764975)
                    ·
                      rfl

theorem cell23_3798195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 5].length) (baseStart_3798195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798195 prefixEnd_3798195 := by exact prefixLift 3798195
  have htrace : WordTrace (prefixWord ++ tailWord_3798195) baseStart_3798195 baseEnd_3798195 := by
    simpa [prefixWord, tailWord_3798195, baseEnd_3798195] using wordTrace_append hprefix tailTrace_3798195
  have hstable : (prefixWord ++ tailWord_3798195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798195).length < 2 ^ (prefixWord ++ tailWord_3798195).sum := by decide
  have hdescent : baseEnd_3798195 < baseStart_3798195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798215 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_3798215 : Nat := 118140960795 + 3798215 * 2 ^ 59
def prefixEnd_3798215 : Nat := 4983230072969 + 3 ^ 40 * 3798215 * 2
def baseEnd_3798215 : Nat := 1950309924116962200044833

theorem tailTrace_3798215 : CollatzResearch.WordTrace tailWord_3798215 prefixEnd_3798215 1950309924116962200044833 := by
  unfold tailWord_3798215
  simp only [CollatzResearch.WordTrace]
  refine ⟨138532281934723213322780099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92354854623148808881853399 138532281934723213322780099)
  ·
    refine ⟨207798422902084819984170149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138532281934723213322780099 207798422902084819984170149)
    ·
      refine ⟨38962204294140903747031903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207798422902084819984170149 38962204294140903747031903)
      ·
        refine ⟨58443306441211355620547855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38962204294140903747031903 58443306441211355620547855)
        ·
          refine ⟨87664959661817033430821783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58443306441211355620547855 87664959661817033430821783)
          ·
            refine ⟨131497439492725550146232675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87664959661817033430821783 131497439492725550146232675)
            ·
              refine ⟨197246159239088325219349013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131497439492725550146232675 197246159239088325219349013)
              ·
                refine ⟨9245913714332265244656985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197246159239088325219349013 9245913714332265244656985)
                ·
                  refine ⟨6934435285749198933492739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9245913714332265244656985 6934435285749198933492739)
                  ·
                    refine ⟨10401652928623798400239109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6934435285749198933492739 10401652928623798400239109)
                    ·
                      refine ⟨1950309924116962200044833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10401652928623798400239109 1950309924116962200044833)
                      ·
                        rfl

theorem cell23_3798215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_3798215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798215 prefixEnd_3798215 := by exact prefixLift 3798215
  have htrace : WordTrace (prefixWord ++ tailWord_3798215) baseStart_3798215 baseEnd_3798215 := by
    simpa [prefixWord, tailWord_3798215, baseEnd_3798215] using wordTrace_append hprefix tailTrace_3798215
  have hstable : (prefixWord ++ tailWord_3798215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798215).length < 2 ^ (prefixWord ++ tailWord_3798215).sum := by decide
  have hdescent : baseEnd_3798215 < baseStart_3798215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798259 : List Nat := [1, 1, 1, 2, 2, 5, 3, 3, 1, 4]
def baseStart_3798259 : Nat := 118140960795 + 3798259 * 2 ^ 59
def prefixEnd_3798259 : Nat := 4983230072969 + 3 ^ 40 * 3798259 * 2
def baseEnd_3798259 : Nat := 650110839088586675964877

theorem tailTrace_3798259 : CollatzResearch.WordTrace tailWord_3798259 prefixEnd_3798259 650110839088586675964877 := by
  unfold tailWord_3798259
  simp only [CollatzResearch.WordTrace]
  refine ⟨138533886746563808837381831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92355924497709205891587887 138533886746563808837381831)
  ·
    refine ⟨207800830119845713256072747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138533886746563808837381831 207800830119845713256072747)
    ·
      refine ⟨311701245179768569884109121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207800830119845713256072747 311701245179768569884109121)
      ·
        refine ⟨233775933884826427413081841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311701245179768569884109121 233775933884826427413081841)
        ·
          refine ⟨175331950413619820559811381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233775933884826427413081841 175331950413619820559811381)
          ·
            refine ⟨16437370351276858177482317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175331950413619820559811381 16437370351276858177482317)
            ·
              refine ⟨6164013881728821816555869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16437370351276858177482317 6164013881728821816555869)
              ·
                refine ⟨2311505205648308181208451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6164013881728821816555869 2311505205648308181208451)
                ·
                  refine ⟨3467257808472462271812677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311505205648308181208451 3467257808472462271812677)
                  ·
                    refine ⟨650110839088586675964877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3467257808472462271812677 650110839088586675964877)
                    ·
                      rfl

theorem cell23_3798259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 1, 4].length) (baseStart_3798259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798259 prefixEnd_3798259 := by exact prefixLift 3798259
  have htrace : WordTrace (prefixWord ++ tailWord_3798259) baseStart_3798259 baseEnd_3798259 := by
    simpa [prefixWord, tailWord_3798259, baseEnd_3798259] using wordTrace_append hprefix tailTrace_3798259
  have hstable : (prefixWord ++ tailWord_3798259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798259).length < 2 ^ (prefixWord ++ tailWord_3798259).sum := by decide
  have hdescent : baseEnd_3798259 < baseStart_3798259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798309 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 2, 3, 2]
def baseStart_3798309 : Nat := 118140960795 + 3798309 * 2 ^ 59
def prefixEnd_3798309 : Nat := 4983230072969 + 3 ^ 40 * 3798309 * 2
def baseEnd_3798309 : Nat := 1950358191298484832269401

theorem tailTrace_3798309 : CollatzResearch.WordTrace tailWord_3798309 prefixEnd_3798309 1950358191298484832269401 := by
  unfold tailWord_3798309
  simp only [CollatzResearch.WordTrace]
  refine ⟨138535710396382667376701981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92357140264255111584467987 138535710396382667376701981)
  ·
    refine ⟨51950891398643500266263243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138535710396382667376701981 51950891398643500266263243)
    ·
      refine ⟨77926337097965250399394865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51950891398643500266263243 77926337097965250399394865)
      ·
        refine ⟨58444752823473937799546149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77926337097965250399394865 58444752823473937799546149)
        ·
          refine ⟨10958391154401363337414903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58444752823473937799546149 10958391154401363337414903)
          ·
            refine ⟨16437586731602045006122355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10958391154401363337414903 16437586731602045006122355)
            ·
              refine ⟨24656380097403067509183533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16437586731602045006122355 24656380097403067509183533)
              ·
                refine ⟨9246142536526150315943825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24656380097403067509183533 9246142536526150315943825)
                ·
                  refine ⟨6934606902394612736957869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9246142536526150315943825 6934606902394612736957869)
                  ·
                    refine ⟨2600477588397979776359201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6934606902394612736957869 2600477588397979776359201)
                    ·
                      refine ⟨1950358191298484832269401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2600477588397979776359201 1950358191298484832269401)
                      ·
                        rfl

theorem cell23_3798309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_3798309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798309 prefixEnd_3798309 := by exact prefixLift 3798309
  have htrace : WordTrace (prefixWord ++ tailWord_3798309) baseStart_3798309 baseEnd_3798309 := by
    simpa [prefixWord, tailWord_3798309, baseEnd_3798309] using wordTrace_append hprefix tailTrace_3798309
  have hstable : (prefixWord ++ tailWord_3798309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798309).length < 2 ^ (prefixWord ++ tailWord_3798309).sum := by decide
  have hdescent : baseEnd_3798309 < baseStart_3798309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798339 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 3, 2, 2]
def baseStart_3798339 : Nat := 118140960795 + 3798339 * 2 ^ 59
def prefixEnd_3798339 : Nat := 4983230072969 + 3 ^ 40 * 3798339 * 2
def baseEnd_3798339 : Nat := 1950373595718119714894263

theorem tailTrace_3798339 : CollatzResearch.WordTrace tailWord_3798339 prefixEnd_3798339 1950373595718119714894263 := by
  unfold tailWord_3798339
  simp only [CollatzResearch.WordTrace]
  refine ⟨138536804586273982500294071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92357869724182655000196047 138536804586273982500294071)
  ·
    refine ⟨207805206879410973750441107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138536804586273982500294071 207805206879410973750441107)
    ·
      refine ⟨311707810319116460625661661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207805206879410973750441107 311707810319116460625661661)
      ·
        refine ⟨116890428869668672734623123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311707810319116460625661661 116890428869668672734623123)
        ·
          refine ⟨175335643304503009101934685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116890428869668672734623123 175335643304503009101934685)
          ·
            refine ⟨65750866239188628413225507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175335643304503009101934685 65750866239188628413225507)
            ·
              refine ⟨98626299358782942619838261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65750866239188628413225507 98626299358782942619838261)
              ·
                refine ⟨9246215564885900870609837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98626299358782942619838261 9246215564885900870609837)
                ·
                  refine ⟨3467330836832212826478689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9246215564885900870609837 3467330836832212826478689)
                  ·
                    refine ⟨2600498127624159619859017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3467330836832212826478689 2600498127624159619859017)
                    ·
                      refine ⟨1950373595718119714894263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2600498127624159619859017 1950373595718119714894263)
                      ·
                        rfl

theorem cell23_3798339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 2, 2].length) (baseStart_3798339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798339 prefixEnd_3798339 := by exact prefixLift 3798339
  have htrace : WordTrace (prefixWord ++ tailWord_3798339) baseStart_3798339 baseEnd_3798339 := by
    simpa [prefixWord, tailWord_3798339, baseEnd_3798339] using wordTrace_append hprefix tailTrace_3798339
  have hstable : (prefixWord ++ tailWord_3798339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798339).length < 2 ^ (prefixWord ++ tailWord_3798339).sum := by decide
  have hdescent : baseEnd_3798339 < baseStart_3798339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798345 : List Nat := [1, 2, 1, 1, 2, 3, 5, 8]
def baseStart_3798345 : Nat := 118140960795 + 3798345 * 2 ^ 59
def prefixEnd_3798345 : Nat := 4983230072969 + 3 ^ 40 * 3798345 * 2
def baseEnd_3798345 : Nat := 72236173207483210793305

theorem tailTrace_3798345 : CollatzResearch.WordTrace tailWord_3798345 prefixEnd_3798345 72236173207483210793305 := by
  unfold tailWord_3798345
  simp only [CollatzResearch.WordTrace]
  refine ⟨138537023424252245525012489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92358015616168163683341659 138537023424252245525012489)
  ·
    refine ⟨103902767568189184143759367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138537023424252245525012489 103902767568189184143759367)
    ·
      refine ⟨155854151352283776215639051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103902767568189184143759367 155854151352283776215639051)
      ·
        refine ⟨233781227028425664323458577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155854151352283776215639051 233781227028425664323458577)
        ·
          refine ⟨175335920271319248242593933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233781227028425664323458577 175335920271319248242593933)
          ·
            refine ⟨65750970101744718090972725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175335920271319248242593933 65750970101744718090972725)
            ·
              refine ⟨6164153447038567321028693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65750970101744718090972725 6164153447038567321028693)
              ·
                refine ⟨72236173207483210793305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6164153447038567321028693 72236173207483210793305)
                ·
                  rfl

theorem cell23_3798345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 8].length) (baseStart_3798345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798345 prefixEnd_3798345 := by exact prefixLift 3798345
  have htrace : WordTrace (prefixWord ++ tailWord_3798345) baseStart_3798345 baseEnd_3798345 := by
    simpa [prefixWord, tailWord_3798345, baseEnd_3798345] using wordTrace_append hprefix tailTrace_3798345
  have hstable : (prefixWord ++ tailWord_3798345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798345).length < 2 ^ (prefixWord ++ tailWord_3798345).sum := by decide
  have hdescent : baseEnd_3798345 < baseStart_3798345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798352 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 4]
def baseStart_3798352 : Nat := 118140960795 + 3798352 * 2 ^ 59
def prefixEnd_3798352 : Nat := 4983230072969 + 3 ^ 40 * 3798352 * 2
def baseEnd_3798352 : Nat := 1950380270966628164031703

theorem tailTrace_3798352 : CollatzResearch.WordTrace tailWord_3798352 prefixEnd_3798352 1950380270966628164031703 := by
  unfold tailWord_3798352
  simp only [CollatzResearch.WordTrace]
  refine ⟨69268639367613442860258655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92358185823484590480344873 69268639367613442860258655)
  ·
    refine ⟨103902959051420164290387983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69268639367613442860258655 103902959051420164290387983)
    ·
      refine ⟨155854438577130246435581975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103902959051420164290387983 155854438577130246435581975)
      ·
        refine ⟨233781657865695369653372963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155854438577130246435581975 233781657865695369653372963)
        ·
          refine ⟨350672486798543054480059445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233781657865695369653372963 350672486798543054480059445)
          ·
            refine ⟨32875545637363411357505573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 350672486798543054480059445 32875545637363411357505573)
            ·
              refine ⟨6164164807005639629532295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32875545637363411357505573 6164164807005639629532295)
              ·
                refine ⟨9246247210508459444298443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6164164807005639629532295 9246247210508459444298443)
                ·
                  refine ⟨13869370815762689166447665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9246247210508459444298443 13869370815762689166447665)
                  ·
                    refine ⟨10402028111822016874835749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13869370815762689166447665 10402028111822016874835749)
                    ·
                      refine ⟨1950380270966628164031703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10402028111822016874835749 1950380270966628164031703)
                      ·
                        rfl

theorem cell23_3798352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 4].length) (baseStart_3798352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798352 prefixEnd_3798352 := by exact prefixLift 3798352
  have htrace : WordTrace (prefixWord ++ tailWord_3798352) baseStart_3798352 baseEnd_3798352 := by
    simpa [prefixWord, tailWord_3798352, baseEnd_3798352] using wordTrace_append hprefix tailTrace_3798352
  have hstable : (prefixWord ++ tailWord_3798352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798352).length < 2 ^ (prefixWord ++ tailWord_3798352).sum := by decide
  have hdescent : baseEnd_3798352 < baseStart_3798352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798356 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_3798356 : Nat := 118140960795 + 3798356 * 2 ^ 59
def prefixEnd_3798356 : Nat := 4983230072969 + 3 ^ 40 * 3798356 * 2
def baseEnd_3798356 : Nat := 1950382324889246148381685

theorem tailTrace_3798356 : CollatzResearch.WordTrace tailWord_3798356 prefixEnd_3798356 1950382324889246148381685 := by
  unfold tailWord_3798356
  simp only [CollatzResearch.WordTrace]
  refine ⟨69268712313606197201831461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92358283084808262935775281 69268712313606197201831461)
  ·
    refine ⟨12987883558801161975343399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69268712313606197201831461 12987883558801161975343399)
    ·
      refine ⟨19481825338201742963015099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12987883558801161975343399 19481825338201742963015099)
      ·
        refine ⟨29222738007302614444522649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19481825338201742963015099 29222738007302614444522649)
        ·
          refine ⟨21917053505476960833391987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29222738007302614444522649 21917053505476960833391987)
          ·
            refine ⟨32875580258215441250087981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21917053505476960833391987 32875580258215441250087981)
            ·
              refine ⟨12328342596830790468782993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32875580258215441250087981 12328342596830790468782993)
              ·
                refine ⟨9246256947623092851587245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12328342596830790468782993 9246256947623092851587245)
                ·
                  refine ⟨3467346355358659819345217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9246256947623092851587245 3467346355358659819345217)
                  ·
                    refine ⟨2600509766518994864508913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3467346355358659819345217 2600509766518994864508913)
                    ·
                      refine ⟨1950382324889246148381685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2600509766518994864508913 1950382324889246148381685)
                      ·
                        rfl

theorem cell23_3798356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_3798356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798356 prefixEnd_3798356 := by exact prefixLift 3798356
  have htrace : WordTrace (prefixWord ++ tailWord_3798356) baseStart_3798356 baseEnd_3798356 := by
    simpa [prefixWord, tailWord_3798356, baseEnd_3798356] using wordTrace_append hprefix tailTrace_3798356
  have hstable : (prefixWord ++ tailWord_3798356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798356).length < 2 ^ (prefixWord ++ tailWord_3798356).sum := by decide
  have hdescent : baseEnd_3798356 < baseStart_3798356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798373 : List Nat := [1, 3, 1, 3, 1, 2, 4, 3, 1, 2, 2]
def baseStart_3798373 : Nat := 118140960795 + 3798373 * 2 ^ 59
def prefixEnd_3798373 : Nat := 4983230072969 + 3 ^ 40 * 3798373 * 2
def baseEnd_3798373 : Nat := 1950391054060372581869107

theorem tailTrace_3798373 : CollatzResearch.WordTrace tailWord_3798373 prefixEnd_3798373 1950391054060372581869107 := by
  unfold tailWord_3798373
  simp only [CollatzResearch.WordTrace]
  refine ⟨138538044668150806307031773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92358696445433870871354515 138538044668150806307031773)
  ·
    refine ⟨51951766750556552365136915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138538044668150806307031773 51951766750556552365136915)
    ·
      refine ⟨77927650125834828547705373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51951766750556552365136915 77927650125834828547705373)
      ·
        refine ⟨29222868797188060705389515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77927650125834828547705373 29222868797188060705389515)
        ·
          refine ⟨43834303195782091058084273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29222868797188060705389515 43834303195782091058084273)
          ·
            refine ⟨32875727396836568293563205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43834303195782091058084273 32875727396836568293563205)
            ·
              refine ⟨6164198886906856555043101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32875727396836568293563205 6164198886906856555043101)
              ·
                refine ⟨2311574582590071208141163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6164198886906856555043101 2311574582590071208141163)
                ·
                  refine ⟨3467361873885106812211745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311574582590071208141163 3467361873885106812211745)
                  ·
                    refine ⟨2600521405413830109158809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3467361873885106812211745 2600521405413830109158809)
                    ·
                      refine ⟨1950391054060372581869107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2600521405413830109158809 1950391054060372581869107)
                      ·
                        rfl

theorem cell23_3798373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_3798373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798373 prefixEnd_3798373 := by exact prefixLift 3798373
  have htrace : WordTrace (prefixWord ++ tailWord_3798373) baseStart_3798373 baseEnd_3798373 := by
    simpa [prefixWord, tailWord_3798373, baseEnd_3798373] using wordTrace_append hprefix tailTrace_3798373
  have hstable : (prefixWord ++ tailWord_3798373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798373).length < 2 ^ (prefixWord ++ tailWord_3798373).sum := by decide
  have hdescent : baseEnd_3798373 < baseStart_3798373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798376 : List Nat := [2, 1, 4, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3798376 : Nat := 118140960795 + 3798376 * 2 ^ 59
def prefixEnd_3798376 : Nat := 4983230072969 + 3 ^ 40 * 3798376 * 2
def baseEnd_3798376 : Nat := 1950392594502336070131593

theorem tailTrace_3798376 : CollatzResearch.WordTrace tailWord_3798376 prefixEnd_3798376 1950392594502336070131593 := by
  unfold tailWord_3798376
  simp only [CollatzResearch.WordTrace]
  refine ⟨69269077043569968909695491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92358769391426625212927321 69269077043569968909695491)
  ·
    refine ⟨103903615565354953364543237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69269077043569968909695491 103903615565354953364543237)
    ·
      refine ⟨19481927918504053755851857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103903615565354953364543237 19481927918504053755851857)
      ·
        refine ⟨14611445938878040316888893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19481927918504053755851857 14611445938878040316888893)
        ·
          refine ⟨5479292227079265118833335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14611445938878040316888893 5479292227079265118833335)
          ·
            refine ⟨8218938340618897678250003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5479292227079265118833335 8218938340618897678250003)
            ·
              refine ⟨12328407510928346517375005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218938340618897678250003 12328407510928346517375005)
              ·
                refine ⟨4623152816598129944015627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12328407510928346517375005 4623152816598129944015627)
                ·
                  refine ⟨6934729224897194916023441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4623152816598129944015627 6934729224897194916023441)
                  ·
                    refine ⟨5201046918672896187017581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6934729224897194916023441 5201046918672896187017581)
                    ·
                      refine ⟨1950392594502336070131593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5201046918672896187017581 1950392594502336070131593)
                      ·
                        rfl

theorem cell23_3798376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3798376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798376 prefixEnd_3798376 := by exact prefixLift 3798376
  have htrace : WordTrace (prefixWord ++ tailWord_3798376) baseStart_3798376 baseEnd_3798376 := by
    simpa [prefixWord, tailWord_3798376, baseEnd_3798376] using wordTrace_append hprefix tailTrace_3798376
  have hstable : (prefixWord ++ tailWord_3798376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798376).length < 2 ^ (prefixWord ++ tailWord_3798376).sum := by decide
  have hdescent : baseEnd_3798376 < baseStart_3798376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798432 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 5]
def baseStart_3798432 : Nat := 118140960795 + 3798432 * 2 ^ 59
def prefixEnd_3798432 : Nat := 4983230072969 + 3 ^ 40 * 3798432 * 2
def baseEnd_3798432 : Nat := 1950421349418987851031335

theorem tailTrace_3798432 : CollatzResearch.WordTrace tailWord_3798432 prefixEnd_3798432 1950421349418987851031335 := by
  unfold tailWord_3798432
  simp only [CollatzResearch.WordTrace]
  refine ⟨69270098287468529691714775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92360131049958039588953033 69270098287468529691714775)
  ·
    refine ⟨103905147431202794537572163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69270098287468529691714775 103905147431202794537572163)
    ·
      refine ⟨155857721146804191806358245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103905147431202794537572163 155857721146804191806358245)
      ·
        refine ⟨29223322715025785963692171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155857721146804191806358245 29223322715025785963692171)
        ·
          refine ⟨43834984072538678945538257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29223322715025785963692171 43834984072538678945538257)
          ·
            refine ⟨32876238054404009209153693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43834984072538678945538257 32876238054404009209153693)
            ·
              refine ⟨12328589270401503453432635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32876238054404009209153693 12328589270401503453432635)
              ·
                refine ⟨18492883905602255180148953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12328589270401503453432635 18492883905602255180148953)
                ·
                  refine ⟨13869662929201691385111715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18492883905602255180148953 13869662929201691385111715)
                  ·
                    refine ⟨20804494393802537077667573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13869662929201691385111715 20804494393802537077667573)
                    ·
                      refine ⟨1950421349418987851031335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20804494393802537077667573 1950421349418987851031335)
                      ·
                        rfl

theorem cell23_3798432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_3798432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798432 prefixEnd_3798432 := by exact prefixLift 3798432
  have htrace : WordTrace (prefixWord ++ tailWord_3798432) baseStart_3798432 baseEnd_3798432 := by
    simpa [prefixWord, tailWord_3798432, baseEnd_3798432] using wordTrace_append hprefix tailTrace_3798432
  have hstable : (prefixWord ++ tailWord_3798432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798432).length < 2 ^ (prefixWord ++ tailWord_3798432).sum := by decide
  have hdescent : baseEnd_3798432 < baseStart_3798432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798499 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 2, 5]
def baseStart_3798499 : Nat := 118140960795 + 3798499 * 2 ^ 59
def prefixEnd_3798499 : Nat := 4983230072969 + 3 ^ 40 * 3798499 * 2
def baseEnd_3798499 : Nat := 650151917540946362964509

theorem tailTrace_3798499 : CollatzResearch.WordTrace tailWord_3798499 prefixEnd_3798499 650151917540946362964509 := by
  unfold tailWord_3798499
  simp only [CollatzResearch.WordTrace]
  refine ⟨138542640265694329826118551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92361760177129553217412367 138542640265694329826118551)
  ·
    refine ⟨207813960398541494739177827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138542640265694329826118551 207813960398541494739177827)
    ·
      refine ⟨311720940597812242108766741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207813960398541494739177827 311720940597812242108766741)
      ·
        refine ⟨14611919090522448848848441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 311720940597812242108766741 14611919090522448848848441)
        ·
          refine ⟨10958939317891836636636331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14611919090522448848848441 10958939317891836636636331)
          ·
            refine ⟨16438408976837754954954497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10958939317891836636636331 16438408976837754954954497)
            ·
              refine ⟨12328806732628316216215873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16438408976837754954954497 12328806732628316216215873)
              ·
                refine ⟨9246605049471237162161905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12328806732628316216215873 9246605049471237162161905)
                ·
                  refine ⟨6934953787103427871621429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9246605049471237162161905 6934953787103427871621429)
                  ·
                    refine ⟨650151917540946362964509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6934953787103427871621429 650151917540946362964509)
                    ·
                      rfl

theorem cell23_3798499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 5].length) (baseStart_3798499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798499 prefixEnd_3798499 := by exact prefixLift 3798499
  have htrace : WordTrace (prefixWord ++ tailWord_3798499) baseStart_3798499 baseEnd_3798499 := by
    simpa [prefixWord, tailWord_3798499, baseEnd_3798499] using wordTrace_append hprefix tailTrace_3798499
  have hstable : (prefixWord ++ tailWord_3798499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798499).length < 2 ^ (prefixWord ++ tailWord_3798499).sum := by decide
  have hdescent : baseEnd_3798499 < baseStart_3798499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798503 : List Nat := [1, 1, 5, 2, 1, 4, 2, 2, 5]
def baseStart_3798503 : Nat := 118140960795 + 3798503 * 2 ^ 59
def prefixEnd_3798503 : Nat := 4983230072969 + 3 ^ 40 * 3798503 * 2
def baseEnd_3798503 : Nat := 216717534060606341471501

theorem tailTrace_3798503 : CollatzResearch.WordTrace tailWord_3798503 prefixEnd_3798503 216717534060606341471501 := by
  unfold tailWord_3798503
  simp only [CollatzResearch.WordTrace]
  refine ⟨138542786157679838509264163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92361857438453225672842775 138542786157679838509264163)
  ·
    refine ⟨207814179236519757763896245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138542786157679838509264163 207814179236519757763896245)
    ·
      refine ⟨19482579303423727290365273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207814179236519757763896245 19482579303423727290365273)
      ·
        refine ⟨14611934477567795467773955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19482579303423727290365273 14611934477567795467773955)
        ·
          refine ⟨21917901716351693201660933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14611934477567795467773955 21917901716351693201660933)
          ·
            refine ⟨4109606571815942475311425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21917901716351693201660933 4109606571815942475311425)
            ·
              refine ⟨3082204928861956856483569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4109606571815942475311425 3082204928861956856483569)
              ·
                refine ⟨2311653696646467642362677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3082204928861956856483569 2311653696646467642362677)
                ·
                  refine ⟨216717534060606341471501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2311653696646467642362677 216717534060606341471501)
                  ·
                    rfl

theorem cell23_3798503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 5].length) (baseStart_3798503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798503 prefixEnd_3798503 := by exact prefixLift 3798503
  have htrace : WordTrace (prefixWord ++ tailWord_3798503) baseStart_3798503 baseEnd_3798503 := by
    simpa [prefixWord, tailWord_3798503, baseEnd_3798503] using wordTrace_append hprefix tailTrace_3798503
  have hstable : (prefixWord ++ tailWord_3798503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798503).length < 2 ^ (prefixWord ++ tailWord_3798503).sum := by decide
  have hdescent : baseEnd_3798503 < baseStart_3798503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798559 : List Nat := [1, 1, 2, 4, 1, 1, 5, 2, 6]
def baseStart_3798559 : Nat := 118140960795 + 3798559 * 2 ^ 59
def prefixEnd_3798559 : Nat := 4983230072969 + 3 ^ 40 * 3798559 * 2
def baseEnd_3798559 : Nat := 216720729051345428238139

theorem tailTrace_3798559 : CollatzResearch.WordTrace tailWord_3798559 prefixEnd_3798559 216720729051345428238139 := by
  unfold tailWord_3798559
  simp only [CollatzResearch.WordTrace]
  refine ⟨138544828645476960073302731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92363219096984640048868487 138544828645476960073302731)
  ·
    refine ⟨207817242968215440109954097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138544828645476960073302731 207817242968215440109954097)
    ·
      refine ⟨155862932226161580082465573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207817242968215440109954097 155862932226161580082465573)
      ·
        refine ⟨29224299792405296265462295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155862932226161580082465573 29224299792405296265462295)
        ·
          refine ⟨43836449688607944398193443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29224299792405296265462295 43836449688607944398193443)
          ·
            refine ⟨65754674532911916597290165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43836449688607944398193443 65754674532911916597290165)
            ·
              refine ⟨6164500737460492180995953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65754674532911916597290165 6164500737460492180995953)
              ·
                refine ⟨4623375553095369135746965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6164500737460492180995953 4623375553095369135746965)
                ·
                  refine ⟨216720729051345428238139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4623375553095369135746965 216720729051345428238139)
                  ·
                    rfl

theorem cell23_3798559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 6].length) (baseStart_3798559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798559 prefixEnd_3798559 := by exact prefixLift 3798559
  have htrace : WordTrace (prefixWord ++ tailWord_3798559) baseStart_3798559 baseEnd_3798559 := by
    simpa [prefixWord, tailWord_3798559, baseEnd_3798559] using wordTrace_append hprefix tailTrace_3798559
  have hstable : (prefixWord ++ tailWord_3798559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798559).length < 2 ^ (prefixWord ++ tailWord_3798559).sum := by decide
  have hdescent : baseEnd_3798559 < baseStart_3798559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798586 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3]
def baseStart_3798586 : Nat := 118140960795 + 3798586 * 2 ^ 59
def prefixEnd_3798586 : Nat := 4983230072969 + 3 ^ 40 * 3798586 * 2
def baseEnd_3798586 : Nat := 1950500425439780248505627

theorem tailTrace_3798586 : CollatzResearch.WordTrace tailWord_3798586 prefixEnd_3798586 1950500425439780248505627 := by
  unfold tailWord_3798586
  simp only [CollatzResearch.WordTrace]
  refine ⟨34636453354094785921133903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92363875610919429123023741 34636453354094785921133903)
  ·
    refine ⟨51954680031142178881700855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34636453354094785921133903 51954680031142178881700855)
    ·
      refine ⟨77932020046713268322551283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51954680031142178881700855 77932020046713268322551283)
      ·
        refine ⟨116898030070069902483826925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77932020046713268322551283 116898030070069902483826925)
        ·
          refine ⟨43836761276276213431435097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116898030070069902483826925 43836761276276213431435097)
          ·
            refine ⟨32877570957207160073576323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43836761276276213431435097 32877570957207160073576323)
            ·
              refine ⟨49316356435810740110364485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32877570957207160073576323 49316356435810740110364485)
              ·
                refine ⟨9246816831714513770693341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49316356435810740110364485 9246816831714513770693341)
                ·
                  refine ⟨3467556311892942664010003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9246816831714513770693341 3467556311892942664010003)
                  ·
                    refine ⟨5201334467839413996015005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3467556311892942664010003 5201334467839413996015005)
                    ·
                      refine ⟨1950500425439780248505627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5201334467839413996015005 1950500425439780248505627)
                      ·
                        rfl

theorem cell23_3798586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_3798586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798586 prefixEnd_3798586 := by exact prefixLift 3798586
  have htrace : WordTrace (prefixWord ++ tailWord_3798586) baseStart_3798586 baseEnd_3798586 := by
    simpa [prefixWord, tailWord_3798586, baseEnd_3798586] using wordTrace_append hprefix tailTrace_3798586
  have hstable : (prefixWord ++ tailWord_3798586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798586).length < 2 ^ (prefixWord ++ tailWord_3798586).sum := by decide
  have hdescent : baseEnd_3798586 < baseStart_3798586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798614 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3798614 : Nat := 118140960795 + 3798614 * 2 ^ 59
def prefixEnd_3798614 : Nat := 4983230072969 + 3 ^ 40 * 3798614 * 2
def baseEnd_3798614 : Nat := 650171600966035379651833

theorem tailTrace_3798614 : CollatzResearch.WordTrace tailWord_3798614 prefixEnd_3798614 650171600966035379651833 := by
  unfold tailWord_3798614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8659177166267356529159681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92364556440185136311036597 8659177166267356529159681)
  ·
    refine ⟨6494382874700517396869761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8659177166267356529159681 6494382874700517396869761)
    ·
      refine ⟨4870787156025388047652321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6494382874700517396869761 4870787156025388047652321)
      ·
        refine ⟨3653090367019041035739241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4870787156025388047652321 3653090367019041035739241)
        ·
          refine ⟨2739817775264280776804431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3653090367019041035739241 2739817775264280776804431)
          ·
            refine ⟨4109726662896421165206647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739817775264280776804431 4109726662896421165206647)
            ·
              refine ⟨6164589994344631747809971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4109726662896421165206647 6164589994344631747809971)
              ·
                refine ⟨9246884991516947621714957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6164589994344631747809971 9246884991516947621714957)
                ·
                  refine ⟨3467581871818855358143109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9246884991516947621714957 3467581871818855358143109)
                  ·
                    refine ⟨650171600966035379651833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3467581871818855358143109 650171600966035379651833)
                    ·
                      rfl

theorem cell23_3798614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3798614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798614 prefixEnd_3798614 := by exact prefixLift 3798614
  have htrace : WordTrace (prefixWord ++ tailWord_3798614) baseStart_3798614 baseEnd_3798614 := by
    simpa [prefixWord, tailWord_3798614, baseEnd_3798614] using wordTrace_append hprefix tailTrace_3798614
  have hstable : (prefixWord ++ tailWord_3798614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798614).length < 2 ^ (prefixWord ++ tailWord_3798614).sum := by decide
  have hdescent : baseEnd_3798614 < baseStart_3798614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798620 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_3798620 : Nat := 118140960795 + 3798620 * 2 ^ 59
def prefixEnd_3798620 : Nat := 4983230072969 + 3 ^ 40 * 3798620 * 2
def baseEnd_3798620 : Nat := 1950517883782033115480471

theorem tailTrace_3798620 : CollatzResearch.WordTrace tailWord_3798620 prefixEnd_3798620 1950517883782033115480471 := by
  unfold tailWord_3798620
  simp only [CollatzResearch.WordTrace]
  refine ⟨69273526749127983745636657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92364702332170644994182209 69273526749127983745636657)
  ·
    refine ⟨51955145061845987809227493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69273526749127983745636657 51955145061845987809227493)
    ·
      refine ⟨9741589699096122714230155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51955145061845987809227493 9741589699096122714230155)
      ·
        refine ⟨14612384548644184071345233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9741589699096122714230155 14612384548644184071345233)
        ·
          refine ⟨10959288411483138053508925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14612384548644184071345233 10959288411483138053508925)
          ·
            refine ⟨4109733154306176770065847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10959288411483138053508925 4109733154306176770065847)
            ·
              refine ⟨6164599731459265155098771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4109733154306176770065847 6164599731459265155098771)
              ·
                refine ⟨9246899597188897732648157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6164599731459265155098771 9246899597188897732648157)
                ·
                  refine ⟨3467587348945836649743059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9246899597188897732648157 3467587348945836649743059)
                  ·
                    refine ⟨5201381023418754974614589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3467587348945836649743059 5201381023418754974614589)
                    ·
                      refine ⟨1950517883782033115480471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5201381023418754974614589 1950517883782033115480471)
                      ·
                        rfl

theorem cell23_3798620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_3798620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798620 prefixEnd_3798620 := by exact prefixLift 3798620
  have htrace : WordTrace (prefixWord ++ tailWord_3798620) baseStart_3798620 baseEnd_3798620 := by
    simpa [prefixWord, tailWord_3798620, baseEnd_3798620] using wordTrace_append hprefix tailTrace_3798620
  have hstable : (prefixWord ++ tailWord_3798620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798620).length < 2 ^ (prefixWord ++ tailWord_3798620).sum := by decide
  have hdescent : baseEnd_3798620 < baseStart_3798620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798639 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 4]
def baseStart_3798639 : Nat := 118140960795 + 3798639 * 2 ^ 59
def prefixEnd_3798639 : Nat := 4983230072969 + 3 ^ 40 * 3798639 * 2
def baseEnd_3798639 : Nat := 1950527639914468541142883

theorem tailTrace_3798639 : CollatzResearch.WordTrace tailWord_3798639 prefixEnd_3798639 1950527639914468541142883 := by
  unfold tailWord_3798639
  simp only [CollatzResearch.WordTrace]
  refine ⟨138547746485187133736214971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92365164323458089157476647 138547746485187133736214971)
  ·
    refine ⟨207821619727780700604322457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138547746485187133736214971 207821619727780700604322457)
    ·
      refine ⟨155866214795835525453241843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207821619727780700604322457 155866214795835525453241843)
      ·
        refine ⟨233799322193753288179862765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155866214795835525453241843 233799322193753288179862765)
        ·
          refine ⟨87674745822657483067448537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233799322193753288179862765 87674745822657483067448537)
          ·
            refine ⟨65756059366993112300586403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87674745822657483067448537 65756059366993112300586403)
            ·
              refine ⟨98634089050489668450879605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65756059366993112300586403 98634089050489668450879605)
              ·
                refine ⟨9246945848483406417269963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98634089050489668450879605 9246945848483406417269963)
                ·
                  refine ⟨13870418772725109625904945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9246945848483406417269963 13870418772725109625904945)
                  ·
                    refine ⟨10402814079543832219428709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13870418772725109625904945 10402814079543832219428709)
                    ·
                      refine ⟨1950527639914468541142883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10402814079543832219428709 1950527639914468541142883)
                      ·
                        rfl

theorem cell23_3798639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_3798639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798639 prefixEnd_3798639 := by exact prefixLift 3798639
  have htrace : WordTrace (prefixWord ++ tailWord_3798639) baseStart_3798639 baseEnd_3798639 := by
    simpa [prefixWord, tailWord_3798639, baseEnd_3798639] using wordTrace_append hprefix tailTrace_3798639
  have hstable : (prefixWord ++ tailWord_3798639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798639).length < 2 ^ (prefixWord ++ tailWord_3798639).sum := by decide
  have hdescent : baseEnd_3798639 < baseStart_3798639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798660 : List Nat := [2, 3, 2, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_3798660 : Nat := 118140960795 + 3798660 * 2 ^ 59
def prefixEnd_3798660 : Nat := 4983230072969 + 3 ^ 40 * 3798660 * 2
def baseEnd_3798660 : Nat := 1950538423008212958980287

theorem tailTrace_3798660 : CollatzResearch.WordTrace tailWord_3798660 prefixEnd_3798660 1950538423008212958980287 := by
  unfold tailWord_3798660
  simp only [CollatzResearch.WordTrace]
  refine ⟨69274256209055527161364717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92365674945407369548486289 69274256209055527161364717)
  ·
    refine ⟨25977846078395822685511769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69274256209055527161364717 25977846078395822685511769)
    ·
      refine ⟨19483384558796867014133827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25977846078395822685511769 19483384558796867014133827)
      ·
        refine ⟨29225076838195300521200741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19483384558796867014133827 29225076838195300521200741)
        ·
          refine ⟨5479701907161618847725139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29225076838195300521200741 5479701907161618847725139)
          ·
            refine ⟨8219552860742428271587709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5479701907161618847725139 8219552860742428271587709)
            ·
              refine ⟨3082332322778410601845391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8219552860742428271587709 3082332322778410601845391)
              ·
                refine ⟨4623498484167615902768087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3082332322778410601845391 4623498484167615902768087)
                ·
                  refine ⟨6935247726251423854152131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4623498484167615902768087 6935247726251423854152131)
                  ·
                    refine ⟨10402871589377135781228197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6935247726251423854152131 10402871589377135781228197)
                    ·
                      refine ⟨1950538423008212958980287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10402871589377135781228197 1950538423008212958980287)
                      ·
                        rfl

theorem cell23_3798660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_3798660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798660 prefixEnd_3798660 := by exact prefixLift 3798660
  have htrace : WordTrace (prefixWord ++ tailWord_3798660) baseStart_3798660 baseEnd_3798660 := by
    simpa [prefixWord, tailWord_3798660, baseEnd_3798660] using wordTrace_append hprefix tailTrace_3798660
  have hstable : (prefixWord ++ tailWord_3798660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798660).length < 2 ^ (prefixWord ++ tailWord_3798660).sum := by decide
  have hdescent : baseEnd_3798660 < baseStart_3798660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798679 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 2, 7]
def baseStart_3798679 : Nat := 118140960795 + 3798679 * 2 ^ 59
def prefixEnd_3798679 : Nat := 4983230072969 + 3 ^ 40 * 3798679 * 2
def baseEnd_3798679 : Nat := 650182726380216128214233

theorem tailTrace_3798679 : CollatzResearch.WordTrace tailWord_3798679 prefixEnd_3798679 650182726380216128214233 := by
  unfold tailWord_3798679
  simp only [CollatzResearch.WordTrace]
  refine ⟨138549205405042220567671091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92366136936694813711780727 138549205405042220567671091)
  ·
    refine ⟨207823808107563330851506637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138549205405042220567671091 207823808107563330851506637)
    ·
      refine ⟨77933928040336249069314989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207823808107563330851506637 77933928040336249069314989)
      ·
        refine ⟨29225223015126093400993121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77933928040336249069314989 29225223015126093400993121)
        ·
          refine ⟨21918917261344570050744841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29225223015126093400993121 21918917261344570050744841)
          ·
            refine ⟨16439187946008427538058631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21918917261344570050744841 16439187946008427538058631)
            ·
              refine ⟨24658781919012641307087947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16439187946008427538058631 24658781919012641307087947)
              ·
                refine ⟨36988172878518961960631921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24658781919012641307087947 36988172878518961960631921)
                ·
                  refine ⟨27741129658889221470473941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36988172878518961960631921 27741129658889221470473941)
                  ·
                    refine ⟨650182726380216128214233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27741129658889221470473941 650182726380216128214233)
                    ·
                      rfl

theorem cell23_3798679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_3798679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798679 prefixEnd_3798679 := by exact prefixLift 3798679
  have htrace : WordTrace (prefixWord ++ tailWord_3798679) baseStart_3798679 baseEnd_3798679 := by
    simpa [prefixWord, tailWord_3798679, baseEnd_3798679] using wordTrace_append hprefix tailTrace_3798679
  have hstable : (prefixWord ++ tailWord_3798679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798679).length < 2 ^ (prefixWord ++ tailWord_3798679).sum := by decide
  have hdescent : baseEnd_3798679 < baseStart_3798679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798690 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3798690 : Nat := 118140960795 + 3798690 * 2 ^ 59
def prefixEnd_3798690 : Nat := 4983230072969 + 3 ^ 40 * 3798690 * 2
def baseEnd_3798690 : Nat := 1950553827427847841605149

theorem tailTrace_3798690 : CollatzResearch.WordTrace tailWord_3798690 prefixEnd_3798690 1950553827427847841605149 := by
  unfold tailWord_3798690
  simp only [CollatzResearch.WordTrace]
  refine ⟨34637401652000592361580381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92366404405334912964214349 34637401652000592361580381)
  ·
    refine ⟨12989025619500222135592643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34637401652000592361580381 12989025619500222135592643)
    ·
      refine ⟨19483538429250333203388965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12989025619500222135592643 19483538429250333203388965)
      ·
        refine ⟨3653163455484437475635431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19483538429250333203388965 3653163455484437475635431)
        ·
          refine ⟨5479745183226656213453147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653163455484437475635431 5479745183226656213453147)
          ·
            refine ⟨8219617774839984320179721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5479745183226656213453147 8219617774839984320179721)
            ·
              refine ⟨6164713331129988240134791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8219617774839984320179721 6164713331129988240134791)
              ·
                refine ⟨9247069996694982360202187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6164713331129988240134791 9247069996694982360202187)
                ·
                  refine ⟨13870604995042473540303281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9247069996694982360202187 13870604995042473540303281)
                  ·
                    refine ⟨10402953746281855155227461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13870604995042473540303281 10402953746281855155227461)
                    ·
                      refine ⟨1950553827427847841605149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10402953746281855155227461 1950553827427847841605149)
                      ·
                        rfl

theorem cell23_3798690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3798690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798690 prefixEnd_3798690 := by exact prefixLift 3798690
  have htrace : WordTrace (prefixWord ++ tailWord_3798690) baseStart_3798690 baseEnd_3798690 := by
    simpa [prefixWord, tailWord_3798690, baseEnd_3798690] using wordTrace_append hprefix tailTrace_3798690
  have hstable : (prefixWord ++ tailWord_3798690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798690).length < 2 ^ (prefixWord ++ tailWord_3798690).sum := by decide
  have hdescent : baseEnd_3798690 < baseStart_3798690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798693 : List Nat := [1, 3, 1, 2, 1, 2, 4, 3, 2, 1, 3]
def baseStart_3798693 : Nat := 118140960795 + 3798693 * 2 ^ 59
def prefixEnd_3798693 : Nat := 4983230072969 + 3 ^ 40 * 3798693 * 2
def baseEnd_3798693 : Nat := 1950555367869811329867635

theorem tailTrace_3798693 : CollatzResearch.WordTrace tailWord_3798693 prefixEnd_3798693 1950555367869811329867635 := by
  unfold tailWord_3798693
  simp only [CollatzResearch.WordTrace]
  refine ⟨138549716026991500958680733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92366477351327667305787155 138549716026991500958680733)
  ·
    refine ⟨51956143510121812859505275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138549716026991500958680733 51956143510121812859505275)
    ·
      refine ⟨77934215265182719289257913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51956143510121812859505275 77934215265182719289257913)
      ·
        refine ⟨58450661448887039466943435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77934215265182719289257913 58450661448887039466943435)
        ·
          refine ⟨87675992173330559200415153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58450661448887039466943435 87675992173330559200415153)
          ·
            refine ⟨65756994129997919400311365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87675992173330559200415153 65756994129997919400311365)
            ·
              refine ⟨12329436399374609887558381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65756994129997919400311365 12329436399374609887558381)
              ·
                refine ⟨4623538649765478707834393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12329436399374609887558381 4623538649765478707834393)
                ·
                  refine ⟨3467653987324109030875795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4623538649765478707834393 3467653987324109030875795)
                  ·
                    refine ⟨5201480980986163546313693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3467653987324109030875795 5201480980986163546313693)
                    ·
                      refine ⟨1950555367869811329867635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5201480980986163546313693 1950555367869811329867635)
                      ·
                        rfl

theorem cell23_3798693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_3798693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798693 prefixEnd_3798693 := by exact prefixLift 3798693
  have htrace : WordTrace (prefixWord ++ tailWord_3798693) baseStart_3798693 baseEnd_3798693 := by
    simpa [prefixWord, tailWord_3798693, baseEnd_3798693] using wordTrace_append hprefix tailTrace_3798693
  have hstable : (prefixWord ++ tailWord_3798693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798693).length < 2 ^ (prefixWord ++ tailWord_3798693).sum := by decide
  have hdescent : baseEnd_3798693 < baseStart_3798693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798703 : List Nat := [1, 1, 2, 1, 2, 4, 2, 4, 1, 3, 2]
def baseStart_3798703 : Nat := 118140960795 + 3798703 * 2 ^ 59
def prefixEnd_3798703 : Nat := 4983230072969 + 3 ^ 40 * 3798703 * 2
def baseEnd_3798703 : Nat := 1950560502676356290742589

theorem tailTrace_3798703 : CollatzResearch.WordTrace tailWord_3798703 prefixEnd_3798703 1950560502676356290742589 := by
  unfold tailWord_3798703
  simp only [CollatzResearch.WordTrace]
  refine ⟨138550080756955272666544763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92366720504636848444363175 138550080756955272666544763)
  ·
    refine ⟨207825121135432908999817145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138550080756955272666544763 207825121135432908999817145)
    ·
      refine ⟨155868840851574681749862859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207825121135432908999817145 155868840851574681749862859)
      ·
        refine ⟨233803261277362022624794289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155868840851574681749862859 233803261277362022624794289)
        ·
          refine ⟨175352445958021516968595717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233803261277362022624794289 175352445958021516968595717)
          ·
            refine ⟨32878583617129034431611697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175352445958021516968595717 32878583617129034431611697)
            ·
              refine ⟨24658937712846775823708773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32878583617129034431611697 24658937712846775823708773)
              ·
                refine ⟨4623550821158770466945395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24658937712846775823708773 4623550821158770466945395)
                ·
                  refine ⟨6935326231738155700418093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4623550821158770466945395 6935326231738155700418093)
                  ·
                    refine ⟨2600747336901808387656785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6935326231738155700418093 2600747336901808387656785)
                    ·
                      refine ⟨1950560502676356290742589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2600747336901808387656785 1950560502676356290742589)
                      ·
                        rfl

theorem cell23_3798703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 3, 2].length) (baseStart_3798703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798703 prefixEnd_3798703 := by exact prefixLift 3798703
  have htrace : WordTrace (prefixWord ++ tailWord_3798703) baseStart_3798703 baseEnd_3798703 := by
    simpa [prefixWord, tailWord_3798703, baseEnd_3798703] using wordTrace_append hprefix tailTrace_3798703
  have hstable : (prefixWord ++ tailWord_3798703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798703).length < 2 ^ (prefixWord ++ tailWord_3798703).sum := by decide
  have hdescent : baseEnd_3798703 < baseStart_3798703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798710 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_3798710 : Nat := 118140960795 + 3798710 * 2 ^ 59
def prefixEnd_3798710 : Nat := 4983230072969 + 3 ^ 40 * 3798710 * 2
def baseEnd_3798710 : Nat := 1950564097040937763355057

theorem tailTrace_3798710 : CollatzResearch.WordTrace tailWord_3798710 prefixEnd_3798710 1950564097040937763355057 := by
  unfold tailWord_3798710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8659396004245619553878099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92366890711953275241366389 8659396004245619553878099)
  ·
    refine ⟨12989094006368429330817149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8659396004245619553878099 12989094006368429330817149)
    ·
      refine ⟨4870910252388160999056431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12989094006368429330817149 4870910252388160999056431)
      ·
        refine ⟨7306365378582241498584647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4870910252388160999056431 7306365378582241498584647)
        ·
          refine ⟨10959548067873362247876971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7306365378582241498584647 10959548067873362247876971)
          ·
            refine ⟨16439322101810043371815457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10959548067873362247876971 16439322101810043371815457)
            ·
              refine ⟨12329491576357532528861593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16439322101810043371815457 12329491576357532528861593)
              ·
                refine ⟨9247118682268149396646195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12329491576357532528861593 9247118682268149396646195)
                ·
                  refine ⟨13870678023402224094969293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9247118682268149396646195 13870678023402224094969293)
                  ·
                    refine ⟨5201504258775834035613485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13870678023402224094969293 5201504258775834035613485)
                    ·
                      refine ⟨1950564097040937763355057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5201504258775834035613485 1950564097040937763355057)
                      ·
                        rfl

theorem cell23_3798710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_3798710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798710 prefixEnd_3798710 := by exact prefixLift 3798710
  have htrace : WordTrace (prefixWord ++ tailWord_3798710) baseStart_3798710 baseEnd_3798710 := by
    simpa [prefixWord, tailWord_3798710, baseEnd_3798710] using wordTrace_append hprefix tailTrace_3798710
  have hstable : (prefixWord ++ tailWord_3798710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798710).length < 2 ^ (prefixWord ++ tailWord_3798710).sum := by decide
  have hdescent : baseEnd_3798710 < baseStart_3798710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798719 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 5]
def baseStart_3798719 : Nat := 118140960795 + 3798719 * 2 ^ 59
def prefixEnd_3798719 : Nat := 4983230072969 + 3 ^ 40 * 3798719 * 2
def baseEnd_3798719 : Nat := 1950568718366828228142515

theorem tailTrace_3798719 : CollatzResearch.WordTrace tailWord_3798719 prefixEnd_3798719 1950568718366828228142515 := by
  unfold tailWord_3798719
  simp only [CollatzResearch.WordTrace]
  refine ⟨138550664324897307399127211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92367109549931538266084807 138550664324897307399127211)
  ·
    refine ⟨207825996487345961098690817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138550664324897307399127211 207825996487345961098690817)
    ·
      refine ⟨155869497365509470824018113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207825996487345961098690817 155869497365509470824018113)
      ·
        refine ⟨116902123024132103118013585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155869497365509470824018113 116902123024132103118013585)
        ·
          refine ⟨87676592268099077338510189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116902123024132103118013585 87676592268099077338510189)
          ·
            refine ⟨32878722100537154001941321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87676592268099077338510189 32878722100537154001941321)
            ·
              refine ⟨24659041575402865501455991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32878722100537154001941321 24659041575402865501455991)
              ·
                refine ⟨36988562363104298252183987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24659041575402865501455991 36988562363104298252183987)
                ·
                  refine ⟨55482843544656447378275981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36988562363104298252183987 55482843544656447378275981)
                  ·
                    refine ⟨20806066329246167766853493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55482843544656447378275981 20806066329246167766853493)
                    ·
                      refine ⟨1950568718366828228142515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20806066329246167766853493 1950568718366828228142515)
                      ·
                        rfl

theorem cell23_3798719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_3798719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798719 prefixEnd_3798719 := by exact prefixLift 3798719
  have htrace : WordTrace (prefixWord ++ tailWord_3798719) baseStart_3798719 baseEnd_3798719 := by
    simpa [prefixWord, tailWord_3798719, baseEnd_3798719] using wordTrace_append hprefix tailTrace_3798719
  have hstable : (prefixWord ++ tailWord_3798719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798719).length < 2 ^ (prefixWord ++ tailWord_3798719).sum := by decide
  have hdescent : baseEnd_3798719 < baseStart_3798719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798746 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_3798746 : Nat := 118140960795 + 3798746 * 2 ^ 59
def prefixEnd_3798746 : Nat := 4983230072969 + 3 ^ 40 * 3798746 * 2
def baseEnd_3798746 : Nat := 1950582582344499622504891

theorem tailTrace_3798746 : CollatzResearch.WordTrace tailWord_3798746 prefixEnd_3798746 1950582582344499622504891 := by
  unfold tailWord_3798746
  simp only [CollatzResearch.WordTrace]
  refine ⟨34637912273949872752590023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92367766063866327340240061 34637912273949872752590023)
  ·
    refine ⟨51956868410924809128885035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34637912273949872752590023 51956868410924809128885035)
    ·
      refine ⟨77935302616387213693327553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51956868410924809128885035 77935302616387213693327553)
      ·
        refine ⟨58451476962290410269995665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77935302616387213693327553 58451476962290410269995665)
        ·
          refine ⟨43838607721717807702496749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58451476962290410269995665 43838607721717807702496749)
          ·
            refine ⟨16439477895644177888436281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43838607721717807702496749 16439477895644177888436281)
            ·
              refine ⟨12329608421733133416327211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16439477895644177888436281 12329608421733133416327211)
              ·
                refine ⟨18494412632599700124490817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12329608421733133416327211 18494412632599700124490817)
                ·
                  refine ⟨13870809474449775093368113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18494412632599700124490817 13870809474449775093368113)
                  ·
                    refine ⟨10403107105837331320026085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13870809474449775093368113 10403107105837331320026085)
                    ·
                      refine ⟨1950582582344499622504891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10403107105837331320026085 1950582582344499622504891)
                      ·
                        rfl

theorem cell23_3798746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_3798746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798746 prefixEnd_3798746 := by exact prefixLift 3798746
  have htrace : WordTrace (prefixWord ++ tailWord_3798746) baseStart_3798746 baseEnd_3798746 := by
    simpa [prefixWord, tailWord_3798746, baseEnd_3798746] using wordTrace_append hprefix tailTrace_3798746
  have hstable : (prefixWord ++ tailWord_3798746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798746).length < 2 ^ (prefixWord ++ tailWord_3798746).sum := by decide
  have hdescent : baseEnd_3798746 < baseStart_3798746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798789 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_3798789 : Nat := 118140960795 + 3798789 * 2 ^ 59
def prefixEnd_3798789 : Nat := 4983230072969 + 3 ^ 40 * 3798789 * 2
def baseEnd_3798789 : Nat := 1950604662012642954267193

theorem tailTrace_3798789 : CollatzResearch.WordTrace tailWord_3798789 prefixEnd_3798789 1950604662012642954267193 := by
  unfold tailWord_3798789
  simp only [CollatzResearch.WordTrace]
  refine ⟨138553217434643709354175421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92368811623095806236116947 138553217434643709354175421)
  ·
    refine ⟨51957456537991391007815783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138553217434643709354175421 51957456537991391007815783)
    ·
      refine ⟨77936184806987086511723675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51957456537991391007815783 77936184806987086511723675)
      ·
        refine ⟨116904277210480629767585513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77936184806987086511723675 116904277210480629767585513)
        ·
          refine ⟨87678207907860472325689135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116904277210480629767585513 87678207907860472325689135)
          ·
            refine ⟨131517311861790708488533703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87678207907860472325689135 131517311861790708488533703)
            ·
              refine ⟨197275967792686062732800555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131517311861790708488533703 197275967792686062732800555)
              ·
                refine ⟨295913951689029094099200833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197275967792686062732800555 295913951689029094099200833)
                ·
                  refine ⟨221935463766771820574400625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295913951689029094099200833 221935463766771820574400625)
                  ·
                    refine ⟨166451597825078865430800469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 221935463766771820574400625 166451597825078865430800469)
                    ·
                      refine ⟨1950604662012642954267193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 166451597825078865430800469 1950604662012642954267193)
                      ·
                        rfl

theorem cell23_3798789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_3798789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798789 prefixEnd_3798789 := by exact prefixLift 3798789
  have htrace : WordTrace (prefixWord ++ tailWord_3798789) baseStart_3798789 baseEnd_3798789 := by
    simpa [prefixWord, tailWord_3798789, baseEnd_3798789] using wordTrace_append hprefix tailTrace_3798789
  have hstable : (prefixWord ++ tailWord_3798789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798789).length < 2 ^ (prefixWord ++ tailWord_3798789).sum := by decide
  have hdescent : baseEnd_3798789 < baseStart_3798789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798799 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 2, 8]
def baseStart_3798799 : Nat := 118140960795 + 3798799 * 2 ^ 59
def prefixEnd_3798799 : Nat := 4983230072969 + 3 ^ 40 * 3798799 * 2
def baseEnd_3798799 : Nat := 650203265606395971714049

theorem tailTrace_3798799 : CollatzResearch.WordTrace tailWord_3798799 prefixEnd_3798799 650203265606395971714049 := by
  unfold tailWord_3798799
  simp only [CollatzResearch.WordTrace]
  refine ⟨138553582164607481062039451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92369054776404987374692967 138553582164607481062039451)
  ·
    refine ⟨207830373246911221593059177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138553582164607481062039451 207830373246911221593059177)
    ·
      refine ⟨155872779935183416194794383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207830373246911221593059177 155872779935183416194794383)
      ·
        refine ⟨233809169902775124292191575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155872779935183416194794383 233809169902775124292191575)
        ·
          refine ⟨350713754854162686438287363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233809169902775124292191575 350713754854162686438287363)
          ·
            refine ⟨526070632281244029657431045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350713754854162686438287363 526070632281244029657431045)
            ·
              refine ⟨98638243552733255560768321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 526070632281244029657431045 98638243552733255560768321)
              ·
                refine ⟨73978682664549941670576241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98638243552733255560768321 73978682664549941670576241)
                ·
                  refine ⟨55484011998412456252932181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73978682664549941670576241 55484011998412456252932181)
                  ·
                    refine ⟨650203265606395971714049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55484011998412456252932181 650203265606395971714049)
                    ·
                      rfl

theorem cell23_3798799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_3798799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798799 prefixEnd_3798799 := by exact prefixLift 3798799
  have htrace : WordTrace (prefixWord ++ tailWord_3798799) baseStart_3798799 baseEnd_3798799 := by
    simpa [prefixWord, tailWord_3798799, baseEnd_3798799] using wordTrace_append hprefix tailTrace_3798799
  have hstable : (prefixWord ++ tailWord_3798799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798799).length < 2 ^ (prefixWord ++ tailWord_3798799).sum := by decide
  have hdescent : baseEnd_3798799 < baseStart_3798799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798809 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 9]
def baseStart_3798809 : Nat := 118140960795 + 3798809 * 2 ^ 59
def prefixEnd_3798809 : Nat := 4983230072969 + 3 ^ 40 * 3798809 * 2
def baseEnd_3798809 : Nat := 1950614931625732876017101

theorem tailTrace_3798809 : CollatzResearch.WordTrace tailWord_3798809 prefixEnd_3798809 1950614931625732876017101 := by
  unfold tailWord_3798809
  simp only [CollatzResearch.WordTrace]
  refine ⟨138553946894571252769903481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92369297929714168513268987 138553946894571252769903481)
  ·
    refine ⟨103915460170928439577427611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138553946894571252769903481 103915460170928439577427611)
    ·
      refine ⟨155873190256392659366141417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103915460170928439577427611 155873190256392659366141417)
      ·
        refine ⟨116904892692294494524606063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155873190256392659366141417 116904892692294494524606063)
        ·
          refine ⟨175357339038441741786909095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116904892692294494524606063 175357339038441741786909095)
          ·
            refine ⟨263036008557662612680363643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175357339038441741786909095 263036008557662612680363643)
            ·
              refine ⟨394554012836493919020545465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263036008557662612680363643 394554012836493919020545465)
              ·
                refine ⟨295915509627370439265409099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394554012836493919020545465 295915509627370439265409099)
                ·
                  refine ⟨443873264441055658898113649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295915509627370439265409099 443873264441055658898113649)
                  ·
                    refine ⟨332904948330791744173585237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 443873264441055658898113649 332904948330791744173585237)
                    ·
                      refine ⟨1950614931625732876017101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 332904948330791744173585237 1950614931625732876017101)
                      ·
                        rfl

theorem cell23_3798809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_3798809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798809 prefixEnd_3798809 := by exact prefixLift 3798809
  have htrace : WordTrace (prefixWord ++ tailWord_3798809) baseStart_3798809 baseEnd_3798809 := by
    simpa [prefixWord, tailWord_3798809, baseEnd_3798809] using wordTrace_append hprefix tailTrace_3798809
  have hstable : (prefixWord ++ tailWord_3798809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798809).length < 2 ^ (prefixWord ++ tailWord_3798809).sum := by decide
  have hdescent : baseEnd_3798809 < baseStart_3798809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798906 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 3, 6]
def baseStart_3798906 : Nat := 118140960795 + 3798906 * 2 ^ 59
def prefixEnd_3798906 : Nat := 4983230072969 + 3 ^ 40 * 3798906 * 2
def baseEnd_3798906 : Nat := 650221579749739665501385

theorem tailTrace_3798906 : CollatzResearch.WordTrace tailWord_3798906 prefixEnd_3798906 650221579749739665501385 := by
  unfold tailWord_3798906
  simp only [CollatzResearch.WordTrace]
  refine ⟨34639371193804959584046143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92371656516813225557456381 34639371193804959584046143)
  ·
    refine ⟨51959056790707439376069215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34639371193804959584046143 51959056790707439376069215)
    ·
      refine ⟨77938585186061159064103823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51959056790707439376069215 77938585186061159064103823)
      ·
        refine ⟨116907877779091738596155735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77938585186061159064103823 116907877779091738596155735)
        ·
          refine ⟨175361816668637607894233603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116907877779091738596155735 175361816668637607894233603)
          ·
            refine ⟨263042725002956411841350405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175361816668637607894233603 263042725002956411841350405)
            ·
              refine ⟨49320510938054327220253201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263042725002956411841350405 49320510938054327220253201)
              ·
                refine ⟨36990383203540745415189901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49320510938054327220253201 36990383203540745415189901)
                ·
                  refine ⟨13871393701327779530696213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36990383203540745415189901 13871393701327779530696213)
                  ·
                    refine ⟨650221579749739665501385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13871393701327779530696213 650221579749739665501385)
                    ·
                      rfl

theorem cell23_3798906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_3798906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798906 prefixEnd_3798906 := by exact prefixLift 3798906
  have htrace : WordTrace (prefixWord ++ tailWord_3798906) baseStart_3798906 baseEnd_3798906 := by
    simpa [prefixWord, tailWord_3798906, baseEnd_3798906] using wordTrace_append hprefix tailTrace_3798906
  have hstable : (prefixWord ++ tailWord_3798906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798906).length < 2 ^ (prefixWord ++ tailWord_3798906).sum := by decide
  have hdescent : baseEnd_3798906 < baseStart_3798906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798940 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 4, 4]
def baseStart_3798940 : Nat := 118140960795 + 3798940 * 2 ^ 59
def prefixEnd_3798940 : Nat := 4983230072969 + 3 ^ 40 * 3798940 * 2
def baseEnd_3798940 : Nat := 650227399197157287826333

theorem tailTrace_3798940 : CollatzResearch.WordTrace tailWord_3798940 prefixEnd_3798940 650227399197157287826333 := by
  unfold tailWord_3798940
  simp only [CollatzResearch.WordTrace]
  refine ⟨69279362428548331071461137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92372483238064441428614849 69279362428548331071461137)
  ·
    refine ⟨51959521821411248303595853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69279362428548331071461137 51959521821411248303595853)
    ·
      refine ⟨19484820683029218113848445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51959521821411248303595853 19484820683029218113848445)
      ·
        refine ⟨7306807756135956792693167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19484820683029218113848445 7306807756135956792693167)
        ·
          refine ⟨10960211634203935189039751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7306807756135956792693167 10960211634203935189039751)
          ·
            refine ⟨16440317451305902783559627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10960211634203935189039751 16440317451305902783559627)
            ·
              refine ⟨24660476176958854175339441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16440317451305902783559627 24660476176958854175339441)
              ·
                refine ⟨18495357132719140631504581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24660476176958854175339441 18495357132719140631504581)
                ·
                  refine ⟨3467879462384838868407109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18495357132719140631504581 3467879462384838868407109)
                  ·
                    refine ⟨650227399197157287826333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3467879462384838868407109 650227399197157287826333)
                    ·
                      rfl

theorem cell23_3798940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_3798940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798940 prefixEnd_3798940 := by exact prefixLift 3798940
  have htrace : WordTrace (prefixWord ++ tailWord_3798940) baseStart_3798940 baseEnd_3798940 := by
    simpa [prefixWord, tailWord_3798940, baseEnd_3798940] using wordTrace_append hprefix tailTrace_3798940
  have hstable : (prefixWord ++ tailWord_3798940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798940).length < 2 ^ (prefixWord ++ tailWord_3798940).sum := by decide
  have hdescent : baseEnd_3798940 < baseStart_3798940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798956 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_3798956 : Nat := 118140960795 + 3798956 * 2 ^ 59
def prefixEnd_3798956 : Nat := 4983230072969 + 3 ^ 40 * 3798956 * 2
def baseEnd_3798956 : Nat := 1950690413281943800878925

theorem tailTrace_3798956 : CollatzResearch.WordTrace tailWord_3798956 prefixEnd_3798956 1950690413281943800878925 := by
  unfold tailWord_3798956
  simp only [CollatzResearch.WordTrace]
  refine ⟨69279654212519348437752361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92372872283359131250336481 69279654212519348437752361)
  ·
    refine ⟨51959740659389511328314271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69279654212519348437752361 51959740659389511328314271)
    ·
      refine ⟨77939610989084266992471407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51959740659389511328314271 77939610989084266992471407)
      ·
        refine ⟨116909416483626400488707111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77939610989084266992471407 116909416483626400488707111)
        ·
          refine ⟨175364124725439600733060667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116909416483626400488707111 175364124725439600733060667)
          ·
            refine ⟨263046187088159401099591001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175364124725439600733060667 263046187088159401099591001)
            ·
              refine ⟨197284640316119550824693251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263046187088159401099591001 197284640316119550824693251)
              ·
                refine ⟨295926960474179326237039877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197284640316119550824693251 295926960474179326237039877)
                ·
                  refine ⟨55486305088908623669444977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295926960474179326237039877 55486305088908623669444977)
                  ·
                    refine ⟨41614728816681467752083733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55486305088908623669444977 41614728816681467752083733)
                    ·
                      refine ⟨1950690413281943800878925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41614728816681467752083733 1950690413281943800878925)
                      ·
                        rfl

theorem cell23_3798956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_3798956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798956 prefixEnd_3798956 := by exact prefixLift 3798956
  have htrace : WordTrace (prefixWord ++ tailWord_3798956) baseStart_3798956 baseEnd_3798956 := by
    simpa [prefixWord, tailWord_3798956, baseEnd_3798956] using wordTrace_append hprefix tailTrace_3798956
  have hstable : (prefixWord ++ tailWord_3798956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798956).length < 2 ^ (prefixWord ++ tailWord_3798956).sum := by decide
  have hdescent : baseEnd_3798956 < baseStart_3798956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798958 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3798958 : Nat := 118140960795 + 3798958 * 2 ^ 59
def prefixEnd_3798958 : Nat := 4983230072969 + 3 ^ 40 * 3798958 * 2
def baseEnd_3798958 : Nat := 1950691440243252793053917

theorem tailTrace_3798958 : CollatzResearch.WordTrace tailWord_3798958 prefixEnd_3798958 1950691440243252793053917 := by
  unfold tailWord_3798958
  simp only [CollatzResearch.WordTrace]
  refine ⟨17319922671378931402134691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92372920914020967478051685 17319922671378931402134691)
  ·
    refine ⟨25979884007068397103202037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17319922671378931402134691 25979884007068397103202037)
    ·
      refine ⟨2435614125662662228425191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25979884007068397103202037 2435614125662662228425191)
      ·
        refine ⟨3653421188493993342637787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435614125662662228425191 3653421188493993342637787)
        ·
          refine ⟨5480131782740990013956681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653421188493993342637787 5480131782740990013956681)
          ·
            refine ⟨4110098837055742510467511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5480131782740990013956681 4110098837055742510467511)
            ·
              refine ⟨6165148255583613765701267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4110098837055742510467511 6165148255583613765701267)
              ·
                refine ⟨9247722383375420648551901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6165148255583613765701267 9247722383375420648551901)
                ·
                  refine ⟨3467895893765782743206963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9247722383375420648551901 3467895893765782743206963)
                  ·
                    refine ⟨5201843840648674114810445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3467895893765782743206963 5201843840648674114810445)
                    ·
                      refine ⟨1950691440243252793053917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5201843840648674114810445 1950691440243252793053917)
                      ·
                        rfl

theorem cell23_3798958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3798958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798958 prefixEnd_3798958 := by exact prefixLift 3798958
  have htrace : WordTrace (prefixWord ++ tailWord_3798958) baseStart_3798958 baseEnd_3798958 := by
    simpa [prefixWord, tailWord_3798958, baseEnd_3798958] using wordTrace_append hprefix tailTrace_3798958
  have hstable : (prefixWord ++ tailWord_3798958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798958).length < 2 ^ (prefixWord ++ tailWord_3798958).sum := by decide
  have hdescent : baseEnd_3798958 < baseStart_3798958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798974 : List Nat := [4, 2, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_3798974 : Nat := 118140960795 + 3798974 * 2 ^ 59
def prefixEnd_3798974 : Nat := 4983230072969 + 3 ^ 40 * 3798974 * 2
def baseEnd_3798974 : Nat := 650233218644574910151281

theorem tailTrace_3798974 : CollatzResearch.WordTrace tailWord_3798974 prefixEnd_3798974 650233218644574910151281 := by
  unfold tailWord_3798974
  simp only [CollatzResearch.WordTrace]
  refine ⟨17319995617371685743707497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92373309959315657299773317 17319995617371685743707497)
  ·
    refine ⟨12989996713028764307780623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17319995617371685743707497 12989996713028764307780623)
    ·
      refine ⟨19484995069543146461670935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12989996713028764307780623 19484995069543146461670935)
      ·
        refine ⟨29227492604314719692506403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19484995069543146461670935 29227492604314719692506403)
        ·
          refine ⟨43841238906472079538759605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29227492604314719692506403 43841238906472079538759605)
          ·
            refine ⟨4110116147481757456758713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43841238906472079538759605 4110116147481757456758713)
            ·
              refine ⟨3082587110611318092569035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4110116147481757456758713 3082587110611318092569035)
              ·
                refine ⟨4623880665916977138853553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3082587110611318092569035 4623880665916977138853553)
                ·
                  refine ⟨3467910499437732854140165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4623880665916977138853553 3467910499437732854140165)
                  ·
                    refine ⟨650233218644574910151281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3467910499437732854140165 650233218644574910151281)
                    ·
                      rfl

theorem cell23_3798974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_3798974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3798974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3798974 prefixEnd_3798974 := by exact prefixLift 3798974
  have htrace : WordTrace (prefixWord ++ tailWord_3798974) baseStart_3798974 baseEnd_3798974 := by
    simpa [prefixWord, tailWord_3798974, baseEnd_3798974] using wordTrace_append hprefix tailTrace_3798974
  have hstable : (prefixWord ++ tailWord_3798974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798974).length < 2 ^ (prefixWord ++ tailWord_3798974).sum := by decide
  have hdescent : baseEnd_3798974 < baseStart_3798974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799015 : List Nat := [1, 1, 5, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_3799015 : Nat := 118140960795 + 3799015 * 2 ^ 59
def prefixEnd_3799015 : Nat := 4983230072969 + 3 ^ 40 * 3799015 * 2
def baseEnd_3799015 : Nat := 1950720708640559070041155

theorem tailTrace_3799015 : CollatzResearch.WordTrace tailWord_3799015 prefixEnd_3799015 1950720708640559070041155 := by
  unfold tailWord_3799015
  simp only [CollatzResearch.WordTrace]
  refine ⟨138561460331824949951902499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92374306887883299967934999 138561460331824949951902499)
  ·
    refine ⟨207842190497737424927853749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138561460331824949951902499 207842190497737424927853749)
    ·
      refine ⟨19485205359162883586986289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207842190497737424927853749 19485205359162883586986289)
      ·
        refine ⟨14613904019372162690239717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19485205359162883586986289 14613904019372162690239717)
        ·
          refine ⟨2740107003632280504419947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14613904019372162690239717 2740107003632280504419947)
          ·
            refine ⟨4110160505448420756629921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2740107003632280504419947 4110160505448420756629921)
            ·
              refine ⟨3082620379086315567472441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4110160505448420756629921 3082620379086315567472441)
              ·
                refine ⟨2311965284314736675604331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3082620379086315567472441 2311965284314736675604331)
                ·
                  refine ⟨3467947926472105013406497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311965284314736675604331 3467947926472105013406497)
                  ·
                    refine ⟨2600960944854078760054873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3467947926472105013406497 2600960944854078760054873)
                    ·
                      refine ⟨1950720708640559070041155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2600960944854078760054873 1950720708640559070041155)
                      ·
                        rfl

theorem cell23_3799015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_3799015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799015 prefixEnd_3799015 := by exact prefixLift 3799015
  have htrace : WordTrace (prefixWord ++ tailWord_3799015) baseStart_3799015 baseEnd_3799015 := by
    simpa [prefixWord, tailWord_3799015, baseEnd_3799015] using wordTrace_append hprefix tailTrace_3799015
  have hstable : (prefixWord ++ tailWord_3799015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799015).length < 2 ^ (prefixWord ++ tailWord_3799015).sum := by decide
  have hdescent : baseEnd_3799015 < baseStart_3799015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799023 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 3]
def baseStart_3799023 : Nat := 118140960795 + 3799023 * 2 ^ 59
def prefixEnd_3799023 : Nat := 4983230072969 + 3 ^ 40 * 3799023 * 2
def baseEnd_3799023 : Nat := 1950724816485795038741117

theorem tailTrace_3799023 : CollatzResearch.WordTrace tailWord_3799023 prefixEnd_3799023 1950724816485795038741117 := by
  unfold tailWord_3799023
  simp only [CollatzResearch.WordTrace]
  refine ⟨138561752115795967318193723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92374501410530644878795815 138561752115795967318193723)
  ·
    refine ⟨207842628173693950977290585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138561752115795967318193723 207842628173693950977290585)
    ·
      refine ⟨155881971130270463232967939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207842628173693950977290585 155881971130270463232967939)
      ·
        refine ⟨233822956695405694849451909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155881971130270463232967939 233822956695405694849451909)
        ·
          refine ⟨43841804380388567784272233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233822956695405694849451909 43841804380388567784272233)
          ·
            refine ⟨32881353285291425838204175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43841804380388567784272233 32881353285291425838204175)
            ·
              refine ⟨49322029927937138757306263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32881353285291425838204175 49322029927937138757306263)
              ·
                refine ⟨73983044891905708135959395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49322029927937138757306263 73983044891905708135959395)
                ·
                  refine ⟨110974567337858562203939093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73983044891905708135959395 110974567337858562203939093)
                  ·
                    refine ⟨5201932843962120103309645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110974567337858562203939093 5201932843962120103309645)
                    ·
                      refine ⟨1950724816485795038741117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5201932843962120103309645 1950724816485795038741117)
                      ·
                        rfl

theorem cell23_3799023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 3].length) (baseStart_3799023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799023 prefixEnd_3799023 := by exact prefixLift 3799023
  have htrace : WordTrace (prefixWord ++ tailWord_3799023) baseStart_3799023 baseEnd_3799023 := by
    simpa [prefixWord, tailWord_3799023, baseEnd_3799023] using wordTrace_append hprefix tailTrace_3799023
  have hstable : (prefixWord ++ tailWord_3799023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799023).length < 2 ^ (prefixWord ++ tailWord_3799023).sum := by decide
  have hdescent : baseEnd_3799023 < baseStart_3799023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799033 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 1, 4, 4]
def baseStart_3799033 : Nat := 118140960795 + 3799033 * 2 ^ 59
def prefixEnd_3799033 : Nat := 4983230072969 + 3 ^ 40 * 3799033 * 2
def baseEnd_3799033 : Nat := 1950729951292339999616071

theorem tailTrace_3799033 : CollatzResearch.WordTrace tailWord_3799033 prefixEnd_3799033 1950729951292339999616071 := by
  unfold tailWord_3799033
  simp only [CollatzResearch.WordTrace]
  refine ⟨138562116845759739026057753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92374744563839826017371835 138562116845759739026057753)
  ·
    refine ⟨103921587634319804269543315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138562116845759739026057753 103921587634319804269543315)
    ·
      refine ⟨155882381451479706404314973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103921587634319804269543315 155882381451479706404314973)
      ·
        refine ⟨58455893044304889901618115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155882381451479706404314973 58455893044304889901618115)
        ·
          refine ⟨87683839566457334852427173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58455893044304889901618115 87683839566457334852427173)
          ·
            refine ⟨16440719918710750284830095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87683839566457334852427173 16440719918710750284830095)
            ·
              refine ⟨24661079878066125427245143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16440719918710750284830095 24661079878066125427245143)
              ·
                refine ⟨36991619817099188140867715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24661079878066125427245143 36991619817099188140867715)
                ·
                  refine ⟨55487429725648782211301573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36991619817099188140867715 55487429725648782211301573)
                  ·
                    refine ⟨10403893073559146664619045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55487429725648782211301573 10403893073559146664619045)
                    ·
                      refine ⟨1950729951292339999616071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10403893073559146664619045 1950729951292339999616071)
                      ·
                        rfl

theorem cell23_3799033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_3799033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799033 prefixEnd_3799033 := by exact prefixLift 3799033
  have htrace : WordTrace (prefixWord ++ tailWord_3799033) baseStart_3799033 baseEnd_3799033 := by
    simpa [prefixWord, tailWord_3799033, baseEnd_3799033] using wordTrace_append hprefix tailTrace_3799033
  have hstable : (prefixWord ++ tailWord_3799033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799033).length < 2 ^ (prefixWord ++ tailWord_3799033).sum := by decide
  have hdescent : baseEnd_3799033 < baseStart_3799033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799123 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 4]
def baseStart_3799123 : Nat := 118140960795 + 3799123 * 2 ^ 59
def prefixEnd_3799123 : Nat := 4983230072969 + 3 ^ 40 * 3799123 * 2
def baseEnd_3799123 : Nat := 1950776164551244647490657

theorem tailTrace_3799123 : CollatzResearch.WordTrace tailWord_3799123 prefixEnd_3799123 1950776164551244647490657 := by
  unfold tailWord_3799123
  simp only [CollatzResearch.WordTrace]
  refine ⟨138565399415433684396834023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92376932943622456264556015 138565399415433684396834023)
  ·
    refine ⟨207848099123150526595251035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138565399415433684396834023 207848099123150526595251035)
    ·
      refine ⟨311772148684725789892876553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207848099123150526595251035 311772148684725789892876553)
      ·
        refine ⟨233829111513544342419657415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311772148684725789892876553 233829111513544342419657415)
        ·
          refine ⟨350743667270316513629486123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233829111513544342419657415 350743667270316513629486123)
          ·
            refine ⟨526115500905474770444229185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350743667270316513629486123 526115500905474770444229185)
            ·
              refine ⟨394586625679106077833171889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526115500905474770444229185 394586625679106077833171889)
              ·
                refine ⟨295939969259329558374878917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394586625679106077833171889 295939969259329558374878917)
                ·
                  refine ⟨55488744236124292195289797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295939969259329558374878917 55488744236124292195289797)
                  ·
                    refine ⟨10404139544273304786616837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55488744236124292195289797 10404139544273304786616837)
                    ·
                      refine ⟨1950776164551244647490657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10404139544273304786616837 1950776164551244647490657)
                      ·
                        rfl

theorem cell23_3799123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_3799123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799123 prefixEnd_3799123 := by exact prefixLift 3799123
  have htrace : WordTrace (prefixWord ++ tailWord_3799123) baseStart_3799123 baseEnd_3799123 := by
    simpa [prefixWord, tailWord_3799123, baseEnd_3799123] using wordTrace_append hprefix tailTrace_3799123
  have hstable : (prefixWord ++ tailWord_3799123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799123).length < 2 ^ (prefixWord ++ tailWord_3799123).sum := by decide
  have hdescent : baseEnd_3799123 < baseStart_3799123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799188 : List Nat := [2, 4, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_3799188 : Nat := 118140960795 + 3799188 * 2 ^ 59
def prefixEnd_3799188 : Nat := 4983230072969 + 3 ^ 40 * 3799188 * 2
def baseEnd_3799188 : Nat := 650269846931262297725953

theorem tailTrace_3799188 : CollatzResearch.WordTrace tailWord_3799188 prefixEnd_3799188 650269846931262297725953 := by
  unfold tailWord_3799188
  simp only [CollatzResearch.WordTrace]
  refine ⟨69283885080099100248975109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92378513440132133665300145 69283885080099100248975109)
  ·
    refine ⟨12990728452518581296682833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69283885080099100248975109 12990728452518581296682833)
    ·
      refine ⟨9743046339388935972512125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12990728452518581296682833 9743046339388935972512125)
      ·
        refine ⟨3653642377270850989692047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9743046339388935972512125 3653642377270850989692047)
        ·
          refine ⟨5480463565906276484538071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653642377270850989692047 5480463565906276484538071)
          ·
            refine ⟨8220695348859414726807107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5480463565906276484538071 8220695348859414726807107)
            ·
              refine ⟨12331043023289122090210661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8220695348859414726807107 12331043023289122090210661)
              ·
                refine ⟨2312070566866710391914499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12331043023289122090210661 2312070566866710391914499)
                ·
                  refine ⟨3468105850300065587871749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312070566866710391914499 3468105850300065587871749)
                  ·
                    refine ⟨650269846931262297725953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3468105850300065587871749 650269846931262297725953)
                    ·
                      rfl

theorem cell23_3799188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_3799188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799188 prefixEnd_3799188 := by exact prefixLift 3799188
  have htrace : WordTrace (prefixWord ++ tailWord_3799188) baseStart_3799188 baseEnd_3799188 := by
    simpa [prefixWord, tailWord_3799188, baseEnd_3799188] using wordTrace_append hprefix tailTrace_3799188
  have hstable : (prefixWord ++ tailWord_3799188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799188).length < 2 ^ (prefixWord ++ tailWord_3799188).sum := by decide
  have hdescent : baseEnd_3799188 < baseStart_3799188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799221 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_3799221 : Nat := 118140960795 + 3799221 * 2 ^ 59
def prefixEnd_3799221 : Nat := 4983230072969 + 3 ^ 40 * 3799221 * 2
def baseEnd_3799221 : Nat := 1950826485655385264065207

theorem tailTrace_3799221 : CollatzResearch.WordTrace tailWord_3799221 prefixEnd_3799221 1950826485655385264065207 := by
  unfold tailWord_3799221
  simp only [CollatzResearch.WordTrace]
  refine ⟨138568973769078647133901517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92379315846052431422601011 138568973769078647133901517)
  ·
    refine ⟨51963365163404492675213069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138568973769078647133901517 51963365163404492675213069)
    ·
      refine ⟨19486261936276684753204901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51963365163404492675213069 19486261936276684753204901)
      ·
        refine ⟨3653674113051878391225919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19486261936276684753204901 3653674113051878391225919)
        ·
          refine ⟨5480511169577817586838879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653674113051878391225919 5480511169577817586838879)
          ·
            refine ⟨8220766754366726380258319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5480511169577817586838879 8220766754366726380258319)
            ·
              refine ⟨12331150131550089570387479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8220766754366726380258319 12331150131550089570387479)
              ·
                refine ⟨18496725197325134355581219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12331150131550089570387479 18496725197325134355581219)
                ·
                  refine ⟨27745087795987701533371829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18496725197325134355581219 27745087795987701533371829)
                  ·
                    refine ⟨2601101980873847018753609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27745087795987701533371829 2601101980873847018753609)
                    ·
                      refine ⟨1950826485655385264065207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2601101980873847018753609 1950826485655385264065207)
                      ·
                        rfl

theorem cell23_3799221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_3799221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799221 prefixEnd_3799221 := by exact prefixLift 3799221
  have htrace : WordTrace (prefixWord ++ tailWord_3799221) baseStart_3799221 baseEnd_3799221 := by
    simpa [prefixWord, tailWord_3799221, baseEnd_3799221] using wordTrace_append hprefix tailTrace_3799221
  have hstable : (prefixWord ++ tailWord_3799221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799221).length < 2 ^ (prefixWord ++ tailWord_3799221).sum := by decide
  have hdescent : baseEnd_3799221 < baseStart_3799221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799228 : List Nat := [2, 2, 2, 3, 3, 1, 2, 3, 1, 1, 3]
def baseStart_3799228 : Nat := 118140960795 + 3799228 * 2 ^ 59
def prefixEnd_3799228 : Nat := 4983230072969 + 3 ^ 40 * 3799228 * 2
def baseEnd_3799228 : Nat := 1950830080019966736677675

theorem tailTrace_3799228 : CollatzResearch.WordTrace tailWord_3799228 prefixEnd_3799228 1950830080019966736677675 := by
  unfold tailWord_3799228
  simp only [CollatzResearch.WordTrace]
  refine ⟨69284614540026643664703169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92379486053368858219604225 69284614540026643664703169)
  ·
    refine ⟨51963460905019982748527377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69284614540026643664703169 51963460905019982748527377)
    ·
      refine ⟨38972595678764987061395533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51963460905019982748527377 38972595678764987061395533)
      ·
        refine ⟨14614723379536870148023325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38972595678764987061395533 14614723379536870148023325)
        ·
          refine ⟨5480521267326326305508747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14614723379536870148023325 5480521267326326305508747)
          ·
            refine ⟨8220781900989489458263121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5480521267326326305508747 8220781900989489458263121)
            ·
              refine ⟨6165586425742117093697341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8220781900989489458263121 6165586425742117093697341)
              ·
                refine ⟨2312094909653293910136503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6165586425742117093697341 2312094909653293910136503)
                ·
                  refine ⟨3468142364479940865204755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312094909653293910136503 3468142364479940865204755)
                  ·
                    refine ⟨5202213546719911297807133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3468142364479940865204755 5202213546719911297807133)
                    ·
                      refine ⟨1950830080019966736677675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5202213546719911297807133 1950830080019966736677675)
                      ·
                        rfl

theorem cell23_3799228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_3799228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799228 prefixEnd_3799228 := by exact prefixLift 3799228
  have htrace : WordTrace (prefixWord ++ tailWord_3799228) baseStart_3799228 baseEnd_3799228 := by
    simpa [prefixWord, tailWord_3799228, baseEnd_3799228] using wordTrace_append hprefix tailTrace_3799228
  have hstable : (prefixWord ++ tailWord_3799228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799228).length < 2 ^ (prefixWord ++ tailWord_3799228).sum := by decide
  have hdescent : baseEnd_3799228 < baseStart_3799228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799254 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3799254 : Nat := 118140960795 + 3799254 * 2 ^ 59
def prefixEnd_3799254 : Nat := 4983230072969 + 3 ^ 40 * 3799254 * 2
def baseEnd_3799254 : Nat := 1950843430516983634952555

theorem tailTrace_3799254 : CollatzResearch.WordTrace tailWord_3799254 prefixEnd_3799254 1950843430516983634952555 := by
  unfold tailWord_3799254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8660636086122443360615801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92380118251972729179901877 8660636086122443360615801)
  ·
    refine ⟨6495477064591832520461851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8660636086122443360615801 6495477064591832520461851)
    ·
      refine ⟨9743215596887748780692777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6495477064591832520461851 9743215596887748780692777)
      ·
        refine ⟨7307411697665811585519583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9743215596887748780692777 7307411697665811585519583)
        ·
          refine ⟨10961117546498717378279375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7307411697665811585519583 10961117546498717378279375)
          ·
            refine ⟨16441676319748076067419063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10961117546498717378279375 16441676319748076067419063)
            ·
              refine ⟨24662514479622114101128595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16441676319748076067419063 24662514479622114101128595)
              ·
                refine ⟨36993771719433171151692893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24662514479622114101128595 36993771719433171151692893)
                ·
                  refine ⟨13872664394787439181884835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36993771719433171151692893 13872664394787439181884835)
                  ·
                    refine ⟨20808996592181158772827253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13872664394787439181884835 20808996592181158772827253)
                    ·
                      refine ⟨1950843430516983634952555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20808996592181158772827253 1950843430516983634952555)
                      ·
                        rfl

theorem cell23_3799254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3799254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799254 prefixEnd_3799254 := by exact prefixLift 3799254
  have htrace : WordTrace (prefixWord ++ tailWord_3799254) baseStart_3799254 baseEnd_3799254 := by
    simpa [prefixWord, tailWord_3799254, baseEnd_3799254] using wordTrace_append hprefix tailTrace_3799254
  have hstable : (prefixWord ++ tailWord_3799254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799254).length < 2 ^ (prefixWord ++ tailWord_3799254).sum := by decide
  have hdescent : baseEnd_3799254 < baseStart_3799254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799271 : List Nat := [1, 1, 5, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3799271 : Nat := 118140960795 + 3799271 * 2 ^ 59
def prefixEnd_3799271 : Nat := 4983230072969 + 3 ^ 40 * 3799271 * 2
def baseEnd_3799271 : Nat := 1950852159688110068439977

theorem tailTrace_3799271 : CollatzResearch.WordTrace tailWord_3799271 prefixEnd_3799271 1950852159688110068439977 := by
  unfold tailWord_3799271
  simp only [CollatzResearch.WordTrace]
  refine ⟨138570797418897505673221667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92380531612598337115481111 138570797418897505673221667)
  ·
    refine ⟨207856196128346258509832501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138570797418897505673221667 207856196128346258509832501)
    ·
      refine ⟨19486518387032461735296797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207856196128346258509832501 19486518387032461735296797)
      ·
        refine ⟨7307444395137173150736299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19486518387032461735296797 7307444395137173150736299)
        ·
          refine ⟨10961166592705759726104449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7307444395137173150736299 10961166592705759726104449)
          ·
            refine ⟨8220874944529319794578337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10961166592705759726104449 8220874944529319794578337)
            ·
              refine ⟨6165656208396989845933753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8220874944529319794578337 6165656208396989845933753)
              ·
                refine ⟨4624242156297742384450315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6165656208396989845933753 4624242156297742384450315)
                ·
                  refine ⟨6936363234446613576675473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624242156297742384450315 6936363234446613576675473)
                  ·
                    refine ⟨5202272425834960182506605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6936363234446613576675473 5202272425834960182506605)
                    ·
                      refine ⟨1950852159688110068439977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5202272425834960182506605 1950852159688110068439977)
                      ·
                        rfl

theorem cell23_3799271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3799271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799271 prefixEnd_3799271 := by exact prefixLift 3799271
  have htrace : WordTrace (prefixWord ++ tailWord_3799271) baseStart_3799271 baseEnd_3799271 := by
    simpa [prefixWord, tailWord_3799271, baseEnd_3799271] using wordTrace_append hprefix tailTrace_3799271
  have hstable : (prefixWord ++ tailWord_3799271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799271).length < 2 ^ (prefixWord ++ tailWord_3799271).sum := by decide
  have hdescent : baseEnd_3799271 < baseStart_3799271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799324 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_3799324 : Nat := 118140960795 + 3799324 * 2 ^ 59
def prefixEnd_3799324 : Nat := 4983230072969 + 3 ^ 40 * 3799324 * 2
def baseEnd_3799324 : Nat := 1950879374162798361077233

theorem tailTrace_3799324 : CollatzResearch.WordTrace tailWord_3799324 prefixEnd_3799324 1950879374162798361077233 := by
  unfold tailWord_3799324
  simp only [CollatzResearch.WordTrace]
  refine ⟨69286365243852747862450513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92381820325136997149934017 69286365243852747862450513)
  ·
    refine ⟨51964773932889560896837885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69286365243852747862450513 51964773932889560896837885)
    ·
      refine ⟨19486790224833585336314207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51964773932889560896837885 19486790224833585336314207)
      ·
        refine ⟨29230185337250378004471311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19486790224833585336314207 29230185337250378004471311)
        ·
          refine ⟨43845278005875567006706967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29230185337250378004471311 43845278005875567006706967)
          ·
            refine ⟨65767917008813350510060451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43845278005875567006706967 65767917008813350510060451)
            ·
              refine ⟨98651875513220025765090677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65767917008813350510060451 98651875513220025765090677)
              ·
                refine ⟨9248613329364377415477251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98651875513220025765090677 9248613329364377415477251)
                ·
                  refine ⟨13872919994046566123215877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9248613329364377415477251 13872919994046566123215877)
                  ·
                    refine ⟨2601172498883731148102977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13872919994046566123215877 2601172498883731148102977)
                    ·
                      refine ⟨1950879374162798361077233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2601172498883731148102977 1950879374162798361077233)
                      ·
                        rfl

theorem cell23_3799324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_3799324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799324 prefixEnd_3799324 := by exact prefixLift 3799324
  have htrace : WordTrace (prefixWord ++ tailWord_3799324) baseStart_3799324 baseEnd_3799324 := by
    simpa [prefixWord, tailWord_3799324, baseEnd_3799324] using wordTrace_append hprefix tailTrace_3799324
  have hstable : (prefixWord ++ tailWord_3799324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799324).length < 2 ^ (prefixWord ++ tailWord_3799324).sum := by decide
  have hdescent : baseEnd_3799324 < baseStart_3799324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799327 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 5]
def baseStart_3799327 : Nat := 118140960795 + 3799327 * 2 ^ 59
def prefixEnd_3799327 : Nat := 4983230072969 + 3 ^ 40 * 3799327 * 2
def baseEnd_3799327 : Nat := 1950880914604761849339719

theorem tailTrace_3799327 : CollatzResearch.WordTrace tailWord_3799327 prefixEnd_3799327 1950880914604761849339719 := by
  unfold tailWord_3799327
  simp only [CollatzResearch.WordTrace]
  refine ⟨138572839906694627237260235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92381893271129751491506823 138572839906694627237260235)
  ·
    refine ⟨207859259860041940855890353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138572839906694627237260235 207859259860041940855890353)
    ·
      refine ⟨155894444895031455641917765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207859259860041940855890353 155894444895031455641917765)
      ·
        refine ⟨29230208417818397932859581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155894444895031455641917765 29230208417818397932859581)
        ·
          refine ⟨10961328156681899224822343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29230208417818397932859581 10961328156681899224822343)
          ·
            refine ⟨16441992235022848837233515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10961328156681899224822343 16441992235022848837233515)
            ·
              refine ⟨24662988352534273255850273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16441992235022848837233515 24662988352534273255850273)
              ·
                refine ⟨18497241264400704941887705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24662988352534273255850273 18497241264400704941887705)
                ·
                  refine ⟨13872930948300528706415779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18497241264400704941887705 13872930948300528706415779)
                  ·
                    refine ⟨20809396422450793059623669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13872930948300528706415779 20809396422450793059623669)
                    ·
                      refine ⟨1950880914604761849339719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20809396422450793059623669 1950880914604761849339719)
                      ·
                        rfl

theorem cell23_3799327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_3799327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799327 prefixEnd_3799327 := by exact prefixLift 3799327
  have htrace : WordTrace (prefixWord ++ tailWord_3799327) baseStart_3799327 baseEnd_3799327 := by
    simpa [prefixWord, tailWord_3799327, baseEnd_3799327] using wordTrace_append hprefix tailTrace_3799327
  have hstable : (prefixWord ++ tailWord_3799327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799327).length < 2 ^ (prefixWord ++ tailWord_3799327).sum := by decide
  have hdescent : baseEnd_3799327 < baseStart_3799327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799328 : List Nat := [2, 1, 1, 5, 2, 3, 1, 2, 1, 3, 2]
def baseStart_3799328 : Nat := 118140960795 + 3799328 * 2 ^ 59
def prefixEnd_3799328 : Nat := 4983230072969 + 3 ^ 40 * 3799328 * 2
def baseEnd_3799328 : Nat := 1950881428085416345427215

theorem tailTrace_3799328 : CollatzResearch.WordTrace tailWord_3799328 prefixEnd_3799328 1950881428085416345427215 := by
  unfold tailWord_3799328
  simp only [CollatzResearch.WordTrace]
  refine ⟨69286438189845502204023319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92381917586460669605364425 69286438189845502204023319)
  ·
    refine ⟨103929657284768253306034979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69286438189845502204023319 103929657284768253306034979)
    ·
      refine ⟨155894485927152379959052469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103929657284768253306034979 155894485927152379959052469)
      ·
        refine ⟨14615108055670535621161169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155894485927152379959052469 14615108055670535621161169)
        ·
          refine ⟨10961331041752901715870877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14615108055670535621161169 10961331041752901715870877)
          ·
            refine ⟨4110499140657338143451579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10961331041752901715870877 4110499140657338143451579)
            ·
              refine ⟨6165748710986007215177369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4110499140657338143451579 6165748710986007215177369)
              ·
                refine ⟨4624311533239505411383027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6165748710986007215177369 4624311533239505411383027)
                ·
                  refine ⟨6936467299859258117074541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624311533239505411383027 6936467299859258117074541)
                  ·
                    refine ⟨2601175237447221793902953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6936467299859258117074541 2601175237447221793902953)
                    ·
                      refine ⟨1950881428085416345427215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2601175237447221793902953 1950881428085416345427215)
                      ·
                        rfl

theorem cell23_3799328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_3799328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799328 prefixEnd_3799328 := by exact prefixLift 3799328
  have htrace : WordTrace (prefixWord ++ tailWord_3799328) baseStart_3799328 baseEnd_3799328 := by
    simpa [prefixWord, tailWord_3799328, baseEnd_3799328] using wordTrace_append hprefix tailTrace_3799328
  have hstable : (prefixWord ++ tailWord_3799328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799328).length < 2 ^ (prefixWord ++ tailWord_3799328).sum := by decide
  have hdescent : baseEnd_3799328 < baseStart_3799328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799358 : List Nat := [4, 2, 1, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_3799358 : Nat := 118140960795 + 3799358 * 2 ^ 59
def prefixEnd_3799358 : Nat := 4983230072969 + 3 ^ 40 * 3799358 * 2
def baseEnd_3799358 : Nat := 1950896832505051228052077

theorem tailTrace_3799358 : CollatzResearch.WordTrace tailWord_3799358 prefixEnd_3799358 1950896832505051228052077 := by
  unfold tailWord_3799358
  simp only [CollatzResearch.WordTrace]
  refine ⟨17321746321197789941454841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92382647046388213021092485 17321746321197789941454841)
  ·
    refine ⟨12991309740898342456091131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17321746321197789941454841 12991309740898342456091131)
    ·
      refine ⟨19486964611347513684136697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12991309740898342456091131 19486964611347513684136697)
      ·
        refine ⟨14615223458510635263102523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19486964611347513684136697 14615223458510635263102523)
        ·
          refine ⟨21922835187765952894653785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14615223458510635263102523 21922835187765952894653785)
          ·
            refine ⟨16442126390824464670990339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21922835187765952894653785 16442126390824464670990339)
            ·
              refine ⟨24663189586236697006485509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16442126390824464670990339 24663189586236697006485509)
              ·
                refine ⟨4624348047419380688716033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24663189586236697006485509 4624348047419380688716033)
                ·
                  refine ⟨3468261035564535516537025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4624348047419380688716033 3468261035564535516537025)
                  ·
                    refine ⟨2601195776673401637402769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3468261035564535516537025 2601195776673401637402769)
                    ·
                      refine ⟨1950896832505051228052077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2601195776673401637402769 1950896832505051228052077)
                      ·
                        rfl

theorem cell23_3799358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_3799358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799358 prefixEnd_3799358 := by exact prefixLift 3799358
  have htrace : WordTrace (prefixWord ++ tailWord_3799358) baseStart_3799358 baseEnd_3799358 := by
    simpa [prefixWord, tailWord_3799358, baseEnd_3799358] using wordTrace_append hprefix tailTrace_3799358
  have hstable : (prefixWord ++ tailWord_3799358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799358).length < 2 ^ (prefixWord ++ tailWord_3799358).sum := by decide
  have hdescent : baseEnd_3799358 < baseStart_3799358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799394 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_3799394 : Nat := 118140960795 + 3799394 * 2 ^ 59
def prefixEnd_3799394 : Nat := 4983230072969 + 3 ^ 40 * 3799394 * 2
def baseEnd_3799394 : Nat := 650305105936204362400637

theorem tailTrace_3799394 : CollatzResearch.WordTrace tailWord_3799394 prefixEnd_3799394 650305105936204362400637 := by
  unfold tailWord_3799394
  simp only [CollatzResearch.WordTrace]
  refine ⟨34643820899362974419987309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92383522398301265119966157 34643820899362974419987309)
  ·
    refine ⟨12991432837261115407495241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34643820899362974419987309 12991432837261115407495241)
    ·
      refine ⟨9743574627945836555621431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12991432837261115407495241 9743574627945836555621431)
      ·
        refine ⟨14615361941918754833432147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9743574627945836555621431 14615361941918754833432147)
        ·
          refine ⟨21923042912878132250148221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14615361941918754833432147 21923042912878132250148221)
          ·
            refine ⟨8221141092329299593805583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21923042912878132250148221 8221141092329299593805583)
            ·
              refine ⟨12331711638493949390708375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8221141092329299593805583 12331711638493949390708375)
              ·
                refine ⟨18497567457740924086062563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12331711638493949390708375 18497567457740924086062563)
                ·
                  refine ⟨27746351186611386129093845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18497567457740924086062563 27746351186611386129093845)
                  ·
                    refine ⟨650305105936204362400637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27746351186611386129093845 650305105936204362400637)
                    ·
                      rfl

theorem cell23_3799394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_3799394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799394 prefixEnd_3799394 := by exact prefixLift 3799394
  have htrace : WordTrace (prefixWord ++ tailWord_3799394) baseStart_3799394 baseEnd_3799394 := by
    simpa [prefixWord, tailWord_3799394, baseEnd_3799394] using wordTrace_append hprefix tailTrace_3799394
  have hstable : (prefixWord ++ tailWord_3799394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799394).length < 2 ^ (prefixWord ++ tailWord_3799394).sum := by decide
  have hdescent : baseEnd_3799394 < baseStart_3799394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799487 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 4]
def baseStart_3799487 : Nat := 118140960795 + 3799487 * 2 ^ 59
def prefixEnd_3799487 : Nat := 4983230072969 + 3 ^ 40 * 3799487 * 2
def baseEnd_3799487 : Nat := 1950963071509481223338983

theorem tailTrace_3799487 : CollatzResearch.WordTrace tailWord_3799487 prefixEnd_3799487 1950963071509481223338983 := by
  unfold tailWord_3799487
  simp only [CollatzResearch.WordTrace]
  refine ⟨138578675586114974563084715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92385783724076649708723143 138578675586114974563084715)
  ·
    refine ⟨207868013379172461844627073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138578675586114974563084715 207868013379172461844627073)
    ·
      refine ⟨155901010034379346383470305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207868013379172461844627073 155901010034379346383470305)
      ·
        refine ⟨116925757525784509787602729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155901010034379346383470305 116925757525784509787602729)
        ·
          refine ⟨87694318144338382340702047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116925757525784509787602729 87694318144338382340702047)
          ·
            refine ⟨131541477216507573511053071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87694318144338382340702047 131541477216507573511053071)
            ·
              refine ⟨197312215824761360266579607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131541477216507573511053071 197312215824761360266579607)
              ·
                refine ⟨295968323737142040399869411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197312215824761360266579607 295968323737142040399869411)
                ·
                  refine ⟨443952485605713060599804117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295968323737142040399869411 443952485605713060599804117)
                  ·
                    refine ⟨10405136381383899857807909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 443952485605713060599804117 10405136381383899857807909)
                    ·
                      refine ⟨1950963071509481223338983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10405136381383899857807909 1950963071509481223338983)
                      ·
                        rfl

theorem cell23_3799487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_3799487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799487 prefixEnd_3799487 := by exact prefixLift 3799487
  have htrace : WordTrace (prefixWord ++ tailWord_3799487) baseStart_3799487 baseEnd_3799487 := by
    simpa [prefixWord, tailWord_3799487, baseEnd_3799487] using wordTrace_append hprefix tailTrace_3799487
  have hstable : (prefixWord ++ tailWord_3799487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799487).length < 2 ^ (prefixWord ++ tailWord_3799487).sum := by decide
  have hdescent : baseEnd_3799487 < baseStart_3799487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799508 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_3799508 : Nat := 118140960795 + 3799508 * 2 ^ 59
def prefixEnd_3799508 : Nat := 4983230072969 + 3 ^ 40 * 3799508 * 2
def baseEnd_3799508 : Nat := 1950973854603225641176387

theorem tailTrace_3799508 : CollatzResearch.WordTrace tailWord_3799508 prefixEnd_3799508 1950973854603225641176387 := by
  unfold tailWord_3799508
  simp only [CollatzResearch.WordTrace]
  refine ⟨69289720759519447574799589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92386294346025930099732785 69289720759519447574799589)
  ·
    refine ⟨12991822642409896420274923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69289720759519447574799589 12991822642409896420274923)
    ·
      refine ⟨19487733963614844630412385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12991822642409896420274923 19487733963614844630412385)
      ·
        refine ⟨14615800472711133472809289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19487733963614844630412385 14615800472711133472809289)
        ·
          refine ⟨10961850354533350104606967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14615800472711133472809289 10961850354533350104606967)
          ·
            refine ⟨16442775531800025156910451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10961850354533350104606967 16442775531800025156910451)
            ·
              refine ⟨24664163297700037735365677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16442775531800025156910451 24664163297700037735365677)
              ·
                refine ⟨9249061236637514150762129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24664163297700037735365677 9249061236637514150762129)
                ·
                  refine ⟨6936795927478135613071597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9249061236637514150762129 6936795927478135613071597)
                  ·
                    refine ⟨2601298472804300854901849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6936795927478135613071597 2601298472804300854901849)
                    ·
                      refine ⟨1950973854603225641176387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2601298472804300854901849 1950973854603225641176387)
                      ·
                        rfl

theorem cell23_3799508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_3799508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799508 prefixEnd_3799508 := by exact prefixLift 3799508
  have htrace : WordTrace (prefixWord ++ tailWord_3799508) baseStart_3799508 baseEnd_3799508 := by
    simpa [prefixWord, tailWord_3799508, baseEnd_3799508] using wordTrace_append hprefix tailTrace_3799508
  have hstable : (prefixWord ++ tailWord_3799508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799508).length < 2 ^ (prefixWord ++ tailWord_3799508).sum := by decide
  have hdescent : baseEnd_3799508 < baseStart_3799508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799514 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 1, 6]
def baseStart_3799514 : Nat := 118140960795 + 3799514 * 2 ^ 59
def prefixEnd_3799514 : Nat := 4983230072969 + 3 ^ 40 * 3799514 * 2
def baseEnd_3799514 : Nat := 650325645162384205900453

theorem tailTrace_3799514 : CollatzResearch.WordTrace tailWord_3799514 prefixEnd_3799514 650325645162384205900453 := by
  unfold tailWord_3799514
  simp only [CollatzResearch.WordTrace]
  refine ⟨34644915089254289543579399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92386440238011438782878397 34644915089254289543579399)
  ·
    refine ⟨51967372633881434315369099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34644915089254289543579399 51967372633881434315369099)
    ·
      refine ⟨77951058950822151473053649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51967372633881434315369099 77951058950822151473053649)
      ·
        refine ⟨58463294213116613604790237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77951058950822151473053649 58463294213116613604790237)
        ·
          refine ⟨21923735329918730101796339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58463294213116613604790237 21923735329918730101796339)
          ·
            refine ⟨32885602994878095152694509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21923735329918730101796339 32885602994878095152694509)
            ·
              refine ⟨12332101123079285682260441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32885602994878095152694509 12332101123079285682260441)
              ·
                refine ⟨9249075842309464261695331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12332101123079285682260441 9249075842309464261695331)
                ·
                  refine ⟨13873613763464196392542997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9249075842309464261695331 13873613763464196392542997)
                  ·
                    refine ⟨650325645162384205900453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13873613763464196392542997 650325645162384205900453)
                    ·
                      rfl

theorem cell23_3799514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_3799514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799514 prefixEnd_3799514 := by exact prefixLift 3799514
  have htrace : WordTrace (prefixWord ++ tailWord_3799514) baseStart_3799514 baseEnd_3799514 := by
    simpa [prefixWord, tailWord_3799514, baseEnd_3799514] using wordTrace_append hprefix tailTrace_3799514
  have hstable : (prefixWord ++ tailWord_3799514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799514).length < 2 ^ (prefixWord ++ tailWord_3799514).sum := by decide
  have hdescent : baseEnd_3799514 < baseStart_3799514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799531 : List Nat := [1, 1, 1, 1, 2, 3, 6, 2, 2, 4]
def baseStart_3799531 : Nat := 118140960795 + 3799531 * 2 ^ 59
def prefixEnd_3799531 : Nat := 4983230072969 + 3 ^ 40 * 3799531 * 2
def baseEnd_3799531 : Nat := 650328554886093017062927

theorem tailTrace_3799531 : CollatzResearch.WordTrace tailWord_3799531 prefixEnd_3799531 650328554886093017062927 := by
  unfold tailWord_3799531
  simp only [CollatzResearch.WordTrace]
  refine ⟨138580280397955570077686447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92386853598637046718457631 138580280397955570077686447)
  ·
    refine ⟨207870420596933355116529671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138580280397955570077686447 207870420596933355116529671)
    ·
      refine ⟨311805630895400032674794507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207870420596933355116529671 311805630895400032674794507)
      ·
        refine ⟨467708446343100049012191761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311805630895400032674794507 467708446343100049012191761)
        ·
          refine ⟨350781334757325036759143821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467708446343100049012191761 350781334757325036759143821)
          ·
            refine ⟨131543000533996888784678933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350781334757325036759143821 131543000533996888784678933)
            ·
              refine ⟨6166078150031104161781825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131543000533996888784678933 6166078150031104161781825)
              ·
                refine ⟨4624558612523328121336369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6166078150031104161781825 4624558612523328121336369)
                ·
                  refine ⟨3468418959392496091002277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4624558612523328121336369 3468418959392496091002277)
                  ·
                    refine ⟨650328554886093017062927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3468418959392496091002277 650328554886093017062927)
                    ·
                      rfl

theorem cell23_3799531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 4].length) (baseStart_3799531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799531 prefixEnd_3799531 := by exact prefixLift 3799531
  have htrace : WordTrace (prefixWord ++ tailWord_3799531) baseStart_3799531 baseEnd_3799531 := by
    simpa [prefixWord, tailWord_3799531, baseEnd_3799531] using wordTrace_append hprefix tailTrace_3799531
  have hstable : (prefixWord ++ tailWord_3799531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799531).length < 2 ^ (prefixWord ++ tailWord_3799531).sum := by decide
  have hdescent : baseEnd_3799531 < baseStart_3799531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799571 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 4, 1, 3]
def baseStart_3799571 : Nat := 118140960795 + 3799571 * 2 ^ 59
def prefixEnd_3799571 : Nat := 4983230072969 + 3 ^ 40 * 3799571 * 2
def baseEnd_3799571 : Nat := 1951006203884458894688597

theorem tailTrace_3799571 : CollatzResearch.WordTrace tailWord_3799571 prefixEnd_3799571 1951006203884458894688597 := by
  unfold tailWord_3799571
  simp only [CollatzResearch.WordTrace]
  refine ⟨138581739317810656909142567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92387826211873771272761711 138581739317810656909142567)
  ·
    refine ⟨207872608976715985363713851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138581739317810656909142567 207872608976715985363713851)
    ·
      refine ⟨311808913465073978045570777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207872608976715985363713851 311808913465073978045570777)
      ·
        refine ⟨233856685098805483534178083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311808913465073978045570777 233856685098805483534178083)
        ·
          refine ⟨350785027648208225301267125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233856685098805483534178083 350785027648208225301267125)
          ·
            refine ⟨32886096342019521121993793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 350785027648208225301267125 32886096342019521121993793)
            ·
              refine ⟨24664572256514640841495345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32886096342019521121993793 24664572256514640841495345)
              ·
                refine ⟨18498429192385980631121509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24664572256514640841495345 18498429192385980631121509)
                ·
                  refine ⟨3468455473572371368335283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18498429192385980631121509 3468455473572371368335283)
                  ·
                    refine ⟨5202683210358557052502925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3468455473572371368335283 5202683210358557052502925)
                    ·
                      refine ⟨1951006203884458894688597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5202683210358557052502925 1951006203884458894688597)
                      ·
                        rfl

theorem cell23_3799571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 1, 3].length) (baseStart_3799571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799571 prefixEnd_3799571 := by exact prefixLift 3799571
  have htrace : WordTrace (prefixWord ++ tailWord_3799571) baseStart_3799571 baseEnd_3799571 := by
    simpa [prefixWord, tailWord_3799571, baseEnd_3799571] using wordTrace_append hprefix tailTrace_3799571
  have hstable : (prefixWord ++ tailWord_3799571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799571).length < 2 ^ (prefixWord ++ tailWord_3799571).sum := by decide
  have hdescent : baseEnd_3799571 < baseStart_3799571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799572 : List Nat := [2, 4, 3, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_3799572 : Nat := 118140960795 + 3799572 * 2 ^ 59
def prefixEnd_3799572 : Nat := 4983230072969 + 3 ^ 40 * 3799572 * 2
def baseEnd_3799572 : Nat := 1951006717365113390776093

theorem tailTrace_3799572 : CollatzResearch.WordTrace tailWord_3799572 prefixEnd_3799572 1951006717365113390776093 := by
  unfold tailWord_3799572
  simp only [CollatzResearch.WordTrace]
  refine ⟨69290887895403517039964485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92387850527204689386619313 69290887895403517039964485)
  ·
    refine ⟨12992041480388159444993341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69290887895403517039964485 12992041480388159444993341)
    ·
      refine ⟨4872015555145559791872503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12992041480388159444993341 4872015555145559791872503)
      ·
        refine ⟨7308023332718339687808755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4872015555145559791872503 7308023332718339687808755)
        ·
          refine ⟨10962034999077509531713133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7308023332718339687808755 10962034999077509531713133)
          ·
            refine ⟨4110763124654066074392425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10962034999077509531713133 4110763124654066074392425)
            ·
              refine ⟨3083072343490549555794319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4110763124654066074392425 3083072343490549555794319)
              ·
                refine ⟨4624608515235824333691479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3083072343490549555794319 4624608515235824333691479)
                ·
                  refine ⟨6936912772853736500537219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624608515235824333691479 6936912772853736500537219)
                  ·
                    refine ⟨10405369159280604750805829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6936912772853736500537219 10405369159280604750805829)
                    ·
                      refine ⟨1951006717365113390776093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10405369159280604750805829 1951006717365113390776093)
                      ·
                        rfl

theorem cell23_3799572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_3799572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799572 prefixEnd_3799572 := by exact prefixLift 3799572
  have htrace : WordTrace (prefixWord ++ tailWord_3799572) baseStart_3799572 baseEnd_3799572 := by
    simpa [prefixWord, tailWord_3799572, baseEnd_3799572] using wordTrace_append hprefix tailTrace_3799572
  have hstable : (prefixWord ++ tailWord_3799572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799572).length < 2 ^ (prefixWord ++ tailWord_3799572).sum := by decide
  have hdescent : baseEnd_3799572 < baseStart_3799572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799575 : List Nat := [1, 1, 3, 6, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3799575 : Nat := 118140960795 + 3799575 * 2 ^ 59
def prefixEnd_3799575 : Nat := 4983230072969 + 3 ^ 40 * 3799575 * 2
def baseEnd_3799575 : Nat := 1951008257807076879038579

theorem tailTrace_3799575 : CollatzResearch.WordTrace tailWord_3799575 prefixEnd_3799575 1951008257807076879038579 := by
  unfold tailWord_3799575
  simp only [CollatzResearch.WordTrace]
  refine ⟨138581885209796165592288179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92387923473197443728192119 138581885209796165592288179)
  ·
    refine ⟨207872827814694248388432269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138581885209796165592288179 207872827814694248388432269)
    ·
      refine ⟨77952310430510343145662101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207872827814694248388432269 77952310430510343145662101)
      ·
        refine ⟨3654014551430172334952911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77952310430510343145662101 3654014551430172334952911)
        ·
          refine ⟨5481021827145258502429367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654014551430172334952911 5481021827145258502429367)
          ·
            refine ⟨8221532740717887753644051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5481021827145258502429367 8221532740717887753644051)
            ·
              refine ⟨12332299111076831630466077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8221532740717887753644051 12332299111076831630466077)
              ·
                refine ⟨4624612166653811861424779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12332299111076831630466077 4624612166653811861424779)
                ·
                  refine ⟨6936918249980717792137169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624612166653811861424779 6936918249980717792137169)
                  ·
                    refine ⟨5202688687485538344102877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6936918249980717792137169 5202688687485538344102877)
                    ·
                      refine ⟨1951008257807076879038579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5202688687485538344102877 1951008257807076879038579)
                      ·
                        rfl

theorem cell23_3799575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3799575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799575 prefixEnd_3799575 := by exact prefixLift 3799575
  have htrace : WordTrace (prefixWord ++ tailWord_3799575) baseStart_3799575 baseEnd_3799575 := by
    simpa [prefixWord, tailWord_3799575, baseEnd_3799575] using wordTrace_append hprefix tailTrace_3799575
  have hstable : (prefixWord ++ tailWord_3799575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799575).length < 2 ^ (prefixWord ++ tailWord_3799575).sum := by decide
  have hdescent : baseEnd_3799575 < baseStart_3799575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799605 : List Nat := [1, 3, 3, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_3799605 : Nat := 118140960795 + 3799605 * 2 ^ 59
def prefixEnd_3799605 : Nat := 4983230072969 + 3 ^ 40 * 3799605 * 2
def baseEnd_3799605 : Nat := 1951023662226711761663441

theorem tailTrace_3799605 : CollatzResearch.WordTrace tailWord_3799605 prefixEnd_3799605 1951023662226711761663441 := by
  unfold tailWord_3799605
  simp only [CollatzResearch.WordTrace]
  refine ⟨138582979399687480715880269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92388652933124987143920179 138582979399687480715880269)
  ·
    refine ⟨51968617274882805268455101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138582979399687480715880269 51968617274882805268455101)
    ·
      refine ⟨19488231478081051975670663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51968617274882805268455101 19488231478081051975670663)
      ·
        refine ⟨29232347217121577963505995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19488231478081051975670663 29232347217121577963505995)
        ·
          refine ⟨43848520825682366945258993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29232347217121577963505995 43848520825682366945258993)
          ·
            refine ⟨32886390619261775208944245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43848520825682366945258993 32886390619261775208944245)
            ·
              refine ⟨3083099120555791425838523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32886390619261775208944245 3083099120555791425838523)
              ·
                refine ⟨4624648680833687138757785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3083099120555791425838523 4624648680833687138757785)
                ·
                  refine ⟨3468486510625265354068339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4624648680833687138757785 3468486510625265354068339)
                  ·
                    refine ⟨5202729765937898031102509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3468486510625265354068339 5202729765937898031102509)
                    ·
                      refine ⟨1951023662226711761663441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5202729765937898031102509 1951023662226711761663441)
                      ·
                        rfl

theorem cell23_3799605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_3799605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799605 prefixEnd_3799605 := by exact prefixLift 3799605
  have htrace : WordTrace (prefixWord ++ tailWord_3799605) baseStart_3799605 baseEnd_3799605 := by
    simpa [prefixWord, tailWord_3799605, baseEnd_3799605] using wordTrace_append hprefix tailTrace_3799605
  have hstable : (prefixWord ++ tailWord_3799605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799605).length < 2 ^ (prefixWord ++ tailWord_3799605).sum := by decide
  have hdescent : baseEnd_3799605 < baseStart_3799605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799624 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_3799624 : Nat := 118140960795 + 3799624 * 2 ^ 59
def prefixEnd_3799624 : Nat := 4983230072969 + 3 ^ 40 * 3799624 * 2
def baseEnd_3799624 : Nat := 1951033418359147187325853

theorem tailTrace_3799624 : CollatzResearch.WordTrace tailWord_3799624 prefixEnd_3799624 1951033418359147187325853 := by
  unfold tailWord_3799624
  simp only [CollatzResearch.WordTrace]
  refine ⟨69291836193309323480410963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92389114924412431307214617 69291836193309323480410963)
  ·
    refine ⟨103937754289963985220616445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69291836193309323480410963 103937754289963985220616445)
    ·
      refine ⟨38976657858736494457731167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103937754289963985220616445 38976657858736494457731167)
      ·
        refine ⟨58464986788104741686596751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38976657858736494457731167 58464986788104741686596751)
        ·
          refine ⟨87697480182157112529895127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58464986788104741686596751 87697480182157112529895127)
          ·
            refine ⟨131546220273235668794842691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87697480182157112529895127 131546220273235668794842691)
            ·
              refine ⟨197319330409853503192264037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131546220273235668794842691 197319330409853503192264037)
              ·
                refine ⟨36997374451847531848549507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197319330409853503192264037 36997374451847531848549507)
                ·
                  refine ⟨55496061677771297772824261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36997374451847531848549507 55496061677771297772824261)
                  ·
                    refine ⟨10405511564582118332404549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55496061677771297772824261 10405511564582118332404549)
                    ·
                      refine ⟨1951033418359147187325853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10405511564582118332404549 1951033418359147187325853)
                      ·
                        rfl

theorem cell23_3799624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_3799624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799624 prefixEnd_3799624 := by exact prefixLift 3799624
  have htrace : WordTrace (prefixWord ++ tailWord_3799624) baseStart_3799624 baseEnd_3799624 := by
    simpa [prefixWord, tailWord_3799624, baseEnd_3799624] using wordTrace_append hprefix tailTrace_3799624
  have hstable : (prefixWord ++ tailWord_3799624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799624).length < 2 ^ (prefixWord ++ tailWord_3799624).sum := by decide
  have hdescent : baseEnd_3799624 < baseStart_3799624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799628 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 6, 2, 2]
def baseStart_3799628 : Nat := 118140960795 + 3799628 * 2 ^ 59
def prefixEnd_3799628 : Nat := 4983230072969 + 3 ^ 40 * 3799628 * 2
def baseEnd_3799628 : Nat := 1951035472281765171675835

theorem tailTrace_3799628 : CollatzResearch.WordTrace tailWord_3799628 prefixEnd_3799628 1951035472281765171675835 := by
  unfold tailWord_3799628
  simp only [CollatzResearch.WordTrace]
  refine ⟨69291909139302077821983769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92389212185736103762645025 69291909139302077821983769)
  ·
    refine ⟨51968931854476558366487827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69291909139302077821983769 51968931854476558366487827)
    ·
      refine ⟨77953397781714837549731741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51968931854476558366487827 77953397781714837549731741)
      ·
        refine ⟨29232524168143064081149403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77953397781714837549731741 29232524168143064081149403)
        ·
          refine ⟨43848786252214596121724105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29232524168143064081149403 43848786252214596121724105)
          ·
            refine ⟨32886589689160947091293079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43848786252214596121724105 32886589689160947091293079)
            ·
              refine ⟨49329884533741420636939619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32886589689160947091293079 49329884533741420636939619)
              ·
                refine ⟨73994826800612130955409429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49329884533741420636939619 73994826800612130955409429)
                ·
                  refine ⟨3468507506278693638534817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73994826800612130955409429 3468507506278693638534817)
                  ·
                    refine ⟨2601380629709020228901113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3468507506278693638534817 2601380629709020228901113)
                    ·
                      refine ⟨1951035472281765171675835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2601380629709020228901113 1951035472281765171675835)
                      ·
                        rfl

theorem cell23_3799628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_3799628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799628 prefixEnd_3799628 := by exact prefixLift 3799628
  have htrace : WordTrace (prefixWord ++ tailWord_3799628) baseStart_3799628 baseEnd_3799628 := by
    simpa [prefixWord, tailWord_3799628, baseEnd_3799628] using wordTrace_append hprefix tailTrace_3799628
  have hstable : (prefixWord ++ tailWord_3799628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799628).length < 2 ^ (prefixWord ++ tailWord_3799628).sum := by decide
  have hdescent : baseEnd_3799628 < baseStart_3799628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799662 : List Nat := [4, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_3799662 : Nat := 118140960795 + 3799662 * 2 ^ 59
def prefixEnd_3799662 : Nat := 4983230072969 + 3 ^ 40 * 3799662 * 2
def baseEnd_3799662 : Nat := 1951052930624018038650679

theorem tailTrace_3799662 : CollatzResearch.WordTrace tailWord_3799662 prefixEnd_3799662 1951052930624018038650679 := by
  unfold tailWord_3799662
  simp only [CollatzResearch.WordTrace]
  refine ⟨17323132295060122431338155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92390038906987319633803493 17323132295060122431338155)
  ·
    refine ⟨25984698442590183647007233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17323132295060122431338155 25984698442590183647007233)
    ·
      refine ⟨19488523831942637735255425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25984698442590183647007233 19488523831942637735255425)
      ·
        refine ⟨14616392873956978301441569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19488523831942637735255425 14616392873956978301441569)
        ·
          refine ⟨10962294655467733726081177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14616392873956978301441569 10962294655467733726081177)
          ·
            refine ⟨8221720991600800294560883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10962294655467733726081177 8221720991600800294560883)
            ·
              refine ⟨12332581487401200441841325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8221720991600800294560883 12332581487401200441841325)
              ·
                refine ⟨4624718057775450165690497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12332581487401200441841325 4624718057775450165690497)
                ·
                  refine ⟨3468538543331587624267873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4624718057775450165690497 3468538543331587624267873)
                  ·
                    refine ⟨2601403907498690718200905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3468538543331587624267873 2601403907498690718200905)
                    ·
                      refine ⟨1951052930624018038650679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2601403907498690718200905 1951052930624018038650679)
                      ·
                        rfl

theorem cell23_3799662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_3799662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799662 prefixEnd_3799662 := by exact prefixLift 3799662
  have htrace : WordTrace (prefixWord ++ tailWord_3799662) baseStart_3799662 baseEnd_3799662 := by
    simpa [prefixWord, tailWord_3799662, baseEnd_3799662] using wordTrace_append hprefix tailTrace_3799662
  have hstable : (prefixWord ++ tailWord_3799662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799662).length < 2 ^ (prefixWord ++ tailWord_3799662).sum := by decide
  have hdescent : baseEnd_3799662 < baseStart_3799662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799698 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3799698 : Nat := 118140960795 + 3799698 * 2 ^ 59
def prefixEnd_3799698 : Nat := 4983230072969 + 3 ^ 40 * 3799698 * 2
def baseEnd_3799698 : Nat := 650357138642526632600171

theorem tailTrace_3799698 : CollatzResearch.WordTrace tailWord_3799698 prefixEnd_3799698 650357138642526632600171 := by
  unfold tailWord_3799698
  simp only [CollatzResearch.WordTrace]
  refine ⟨34646592847087639399753937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92390914258900371732677165 34646592847087639399753937)
  ·
    refine ⟨25984944635315729549815453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34646592847087639399753937 25984944635315729549815453)
    ·
      refine ⟨9744354238243398581180795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25984944635315729549815453 9744354238243398581180795)
      ·
        refine ⟨14616531357365097871771193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9744354238243398581180795 14616531357365097871771193)
        ·
          refine ⟨10962398518023823403828395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14616531357365097871771193 10962398518023823403828395)
          ·
            refine ⟨16443597777035735105742593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10962398518023823403828395 16443597777035735105742593)
            ·
              refine ⟨12332698332776801329306945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16443597777035735105742593 12332698332776801329306945)
              ·
                refine ⟨9249523749582600996980209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12332698332776801329306945 9249523749582600996980209)
                ·
                  refine ⟨6937142812186950747735157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9249523749582600996980209 6937142812186950747735157)
                  ·
                    refine ⟨650357138642526632600171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6937142812186950747735157 650357138642526632600171)
                    ·
                      rfl

theorem cell23_3799698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3799698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799698 prefixEnd_3799698 := by exact prefixLift 3799698
  have htrace : WordTrace (prefixWord ++ tailWord_3799698) baseStart_3799698 baseEnd_3799698 := by
    simpa [prefixWord, tailWord_3799698, baseEnd_3799698] using wordTrace_append hprefix tailTrace_3799698
  have hstable : (prefixWord ++ tailWord_3799698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799698).length < 2 ^ (prefixWord ++ tailWord_3799698).sum := by decide
  have hdescent : baseEnd_3799698 < baseStart_3799698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799721 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 6, 2, 3]
def baseStart_3799721 : Nat := 118140960795 + 3799721 * 2 ^ 59
def prefixEnd_3799721 : Nat := 4983230072969 + 3 ^ 40 * 3799721 * 2
def baseEnd_3799721 : Nat := 1951083225982633307812907

theorem tailTrace_3799721 : CollatzResearch.WordTrace tailWord_3799721 prefixEnd_3799721 1951083225982633307812907 := by
  unfold tailWord_3799721
  simp only [CollatzResearch.WordTrace]
  refine ⟨138587210267267232527103017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92391473511511488351402011 138587210267267232527103017)
  ·
    refine ⟨103940407700450424395327263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138587210267267232527103017 103940407700450424395327263)
    ·
      refine ⟨155910611550675636592990895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103940407700450424395327263 155910611550675636592990895)
      ·
        refine ⟨233865917326013454889486343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155910611550675636592990895 233865917326013454889486343)
        ·
          refine ⟨350798875989020182334229515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233865917326013454889486343 350798875989020182334229515)
          ·
            refine ⟨526198313983530273501344273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350798875989020182334229515 526198313983530273501344273)
            ·
              refine ⟨394648735487647705126008205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526198313983530273501344273 394648735487647705126008205)
              ·
                refine ⟨147993275807867889422253077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394648735487647705126008205 147993275807867889422253077)
                ·
                  refine ⟨6937184803493807316668113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147993275807867889422253077 6937184803493807316668113)
                  ·
                    refine ⟨5202888602620355487501085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6937184803493807316668113 5202888602620355487501085)
                    ·
                      refine ⟨1951083225982633307812907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5202888602620355487501085 1951083225982633307812907)
                      ·
                        rfl

theorem cell23_3799721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 2, 3].length) (baseStart_3799721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799721 prefixEnd_3799721 := by exact prefixLift 3799721
  have htrace : WordTrace (prefixWord ++ tailWord_3799721) baseStart_3799721 baseEnd_3799721 := by
    simpa [prefixWord, tailWord_3799721, baseEnd_3799721] using wordTrace_append hprefix tailTrace_3799721
  have hstable : (prefixWord ++ tailWord_3799721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799721).length < 2 ^ (prefixWord ++ tailWord_3799721).sum := by decide
  have hdescent : baseEnd_3799721 < baseStart_3799721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799735 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 2, 1, 4]
def baseStart_3799735 : Nat := 118140960795 + 3799735 * 2 ^ 59
def prefixEnd_3799735 : Nat := 4983230072969 + 3 ^ 40 * 3799735 * 2
def baseEnd_3799735 : Nat := 1951090414711796253037843

theorem tailTrace_3799735 : CollatzResearch.WordTrace tailWord_3799735 prefixEnd_3799735 1951090414711796253037843 := by
  unfold tailWord_3799735
  simp only [CollatzResearch.WordTrace]
  refine ⟨138587720889216512918112659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92391813926144341945408439 138587720889216512918112659)
  ·
    refine ⟨207881581333824769377168989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138587720889216512918112659 207881581333824769377168989)
    ·
      refine ⟨77955593000184288516438371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207881581333824769377168989 77955593000184288516438371)
      ·
        refine ⟨116933389500276432774657557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77955593000184288516438371 116933389500276432774657557)
        ·
          refine ⟨5481252632825457786312073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116933389500276432774657557 5481252632825457786312073)
          ·
            refine ⟨4110939474619093339734055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5481252632825457786312073 4110939474619093339734055)
            ·
              refine ⟨6166409211928640009601083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4110939474619093339734055 6166409211928640009601083)
              ·
                refine ⟨9249613817892960014401625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166409211928640009601083 9249613817892960014401625)
                ·
                  refine ⟨6937210363419720010801219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9249613817892960014401625 6937210363419720010801219)
                  ·
                    refine ⟨10405815545129580016201829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6937210363419720010801219 10405815545129580016201829)
                    ·
                      refine ⟨1951090414711796253037843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10405815545129580016201829 1951090414711796253037843)
                      ·
                        rfl

theorem cell23_3799735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_3799735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799735 prefixEnd_3799735 := by exact prefixLift 3799735
  have htrace : WordTrace (prefixWord ++ tailWord_3799735) baseStart_3799735 baseEnd_3799735 := by
    simpa [prefixWord, tailWord_3799735, baseEnd_3799735] using wordTrace_append hprefix tailTrace_3799735
  have hstable : (prefixWord ++ tailWord_3799735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799735).length < 2 ^ (prefixWord ++ tailWord_3799735).sum := by decide
  have hdescent : baseEnd_3799735 < baseStart_3799735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799758 : List Nat := [4, 1, 1, 1, 3, 2, 3, 2, 6]
def baseStart_3799758 : Nat := 118140960795 + 3799758 * 2 ^ 59
def prefixEnd_3799758 : Nat := 4983230072969 + 3 ^ 40 * 3799758 * 2
def baseEnd_3799758 : Nat := 216789136085205518116693

theorem tailTrace_3799758 : CollatzResearch.WordTrace tailWord_3799758 prefixEnd_3799758 216789136085205518116693 := by
  unfold tailWord_3799758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17323569971016648480774991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92392373178755458564133285 17323569971016648480774991)
  ·
    refine ⟨25985354956524972721162487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17323569971016648480774991 25985354956524972721162487)
    ·
      refine ⟨38978032434787459081743731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25985354956524972721162487 38978032434787459081743731)
      ·
        refine ⟨58467048652181188622615597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38978032434787459081743731 58467048652181188622615597)
        ·
          refine ⟨21925143244567945733480849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58467048652181188622615597 21925143244567945733480849)
          ·
            refine ⟨16443857433425959300110637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21925143244567945733480849 16443857433425959300110637)
            ·
              refine ⟨6166446537534734737541489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16443857433425959300110637 6166446537534734737541489)
              ·
                refine ⟨4624834903151051053156117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6166446537534734737541489 4624834903151051053156117)
                ·
                  refine ⟨216789136085205518116693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4624834903151051053156117 216789136085205518116693)
                  ·
                    rfl

theorem cell23_3799758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_3799758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799758 prefixEnd_3799758 := by exact prefixLift 3799758
  have htrace : WordTrace (prefixWord ++ tailWord_3799758) baseStart_3799758 baseEnd_3799758 := by
    simpa [prefixWord, tailWord_3799758, baseEnd_3799758] using wordTrace_append hprefix tailTrace_3799758
  have hstable : (prefixWord ++ tailWord_3799758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799758).length < 2 ^ (prefixWord ++ tailWord_3799758).sum := by decide
  have hdescent : baseEnd_3799758 < baseStart_3799758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799801 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 1, 6]
def baseStart_3799801 : Nat := 118140960795 + 3799801 * 2 ^ 59
def prefixEnd_3799801 : Nat := 4983230072969 + 3 ^ 40 * 3799801 * 2
def baseEnd_3799801 : Nat := 650374768144997664937513

theorem tailTrace_3799801 : CollatzResearch.WordTrace tailWord_3799801 prefixEnd_3799801 650374768144997664937513 := by
  unfold tailWord_3799801
  simp only [CollatzResearch.WordTrace]
  refine ⟨138590128106977406190015257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92393418737984937460010171 138590128106977406190015257)
  ·
    refine ⟨103942596080233054642511443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138590128106977406190015257 103942596080233054642511443)
    ·
      refine ⟨155913894120349581963767165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103942596080233054642511443 155913894120349581963767165)
      ·
        refine ⟨58467710295131093236412687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155913894120349581963767165 58467710295131093236412687)
        ·
          refine ⟨87701565442696639854619031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58467710295131093236412687 87701565442696639854619031)
          ·
            refine ⟨131552348164044959781928547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87701565442696639854619031 131552348164044959781928547)
            ·
              refine ⟨197328522246067439672892821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131552348164044959781928547 197328522246067439672892821)
              ·
                refine ⟨9249774480284411234666851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197328522246067439672892821 9249774480284411234666851)
                ·
                  refine ⟨13874661720426616852000277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9249774480284411234666851 13874661720426616852000277)
                  ·
                    refine ⟨650374768144997664937513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13874661720426616852000277 650374768144997664937513)
                    ·
                      rfl

theorem cell23_3799801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 6].length) (baseStart_3799801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799801 prefixEnd_3799801 := by exact prefixLift 3799801
  have htrace : WordTrace (prefixWord ++ tailWord_3799801) baseStart_3799801 baseEnd_3799801 := by
    simpa [prefixWord, tailWord_3799801, baseEnd_3799801] using wordTrace_append hprefix tailTrace_3799801
  have hstable : (prefixWord ++ tailWord_3799801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799801).length < 2 ^ (prefixWord ++ tailWord_3799801).sum := by decide
  have hdescent : baseEnd_3799801 < baseStart_3799801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799802 : List Nat := [3, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3]
def baseStart_3799802 : Nat := 118140960795 + 3799802 * 2 ^ 59
def prefixEnd_3799802 : Nat := 4983230072969 + 3 ^ 40 * 3799802 * 2
def baseEnd_3799802 : Nat := 1951124817915647490900035

theorem tailTrace_3799802 : CollatzResearch.WordTrace tailWord_3799802 prefixEnd_3799802 1951124817915647490900035 := by
  unfold tailWord_3799802
  simp only [CollatzResearch.WordTrace]
  refine ⟨34647541144993445840200415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92393443053315855573867773 34647541144993445840200415)
  ·
    refine ⟨51971311717490168760300623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34647541144993445840200415 51971311717490168760300623)
    ·
      refine ⟨77956967576235253140450935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51971311717490168760300623 77956967576235253140450935)
      ·
        refine ⟨116935451364352879710676403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77956967576235253140450935 116935451364352879710676403)
        ·
          refine ⟨175403177046529319566014605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116935451364352879710676403 175403177046529319566014605)
          ·
            refine ⟨65776191392448494837255477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175403177046529319566014605 65776191392448494837255477)
            ·
              refine ⟨6166517943042046390992701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65776191392448494837255477 6166517943042046390992701)
              ·
                refine ⟨2312444228640767396622263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6166517943042046390992701 2312444228640767396622263)
                ·
                  refine ⟨3468666342961151094933395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312444228640767396622263 3468666342961151094933395)
                  ·
                    refine ⟨5202999514441726642400093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3468666342961151094933395 5202999514441726642400093)
                    ·
                      refine ⟨1951124817915647490900035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5202999514441726642400093 1951124817915647490900035)
                      ·
                        rfl

theorem cell23_3799802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3].length) (baseStart_3799802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799802 prefixEnd_3799802 := by exact prefixLift 3799802
  have htrace : WordTrace (prefixWord ++ tailWord_3799802) baseStart_3799802 baseEnd_3799802 := by
    simpa [prefixWord, tailWord_3799802, baseEnd_3799802] using wordTrace_append hprefix tailTrace_3799802
  have hstable : (prefixWord ++ tailWord_3799802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799802).length < 2 ^ (prefixWord ++ tailWord_3799802).sum := by decide
  have hdescent : baseEnd_3799802 < baseStart_3799802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799818 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 4, 4]
def baseStart_3799818 : Nat := 118140960795 + 3799818 * 2 ^ 59
def prefixEnd_3799818 : Nat := 4983230072969 + 3 ^ 40 * 3799818 * 2
def baseEnd_3799818 : Nat := 650377677868706476099987

theorem tailTrace_3799818 : CollatzResearch.WordTrace tailWord_3799818 prefixEnd_3799818 650377677868706476099987 := by
  unfold tailWord_3799818
  simp only [CollatzResearch.WordTrace]
  refine ⟨34647687036978954523346027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92393832098610545395589405 34647687036978954523346027)
  ·
    refine ⟨51971530555468431785019041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34647687036978954523346027 51971530555468431785019041)
    ·
      refine ⟨38978647916601323838764281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51971530555468431785019041 38978647916601323838764281)
      ·
        refine ⟨29233985937450992879073211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38978647916601323838764281 29233985937450992879073211)
        ·
          refine ⟨43850978906176489318609817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29233985937450992879073211 43850978906176489318609817)
          ·
            refine ⟨32888234179632366988957363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43850978906176489318609817 32888234179632366988957363)
            ·
              refine ⟨49332351269448550483436045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32888234179632366988957363 49332351269448550483436045)
              ·
                refine ⟨18499631726043206431288517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49332351269448550483436045 18499631726043206431288517)
                ·
                  refine ⟨3468680948633101205866597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18499631726043206431288517 3468680948633101205866597)
                  ·
                    refine ⟨650377677868706476099987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3468680948633101205866597 650377677868706476099987)
                    ·
                      rfl

theorem cell23_3799818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_3799818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799818 prefixEnd_3799818 := by exact prefixLift 3799818
  have htrace : WordTrace (prefixWord ++ tailWord_3799818) baseStart_3799818 baseEnd_3799818 := by
    simpa [prefixWord, tailWord_3799818, baseEnd_3799818] using wordTrace_append hprefix tailTrace_3799818
  have hstable : (prefixWord ++ tailWord_3799818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799818).length < 2 ^ (prefixWord ++ tailWord_3799818).sum := by decide
  have hdescent : baseEnd_3799818 < baseStart_3799818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799842 : List Nat := [3, 3, 1, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_3799842 : Nat := 118140960795 + 3799842 * 2 ^ 59
def prefixEnd_3799842 : Nat := 4983230072969 + 3 ^ 40 * 3799842 * 2
def baseEnd_3799842 : Nat := 1951145357141827334399851

theorem tailTrace_3799842 : CollatzResearch.WordTrace tailWord_3799842 prefixEnd_3799842 1951145357141827334399851 := by
  unfold tailWord_3799842
  simp only [CollatzResearch.WordTrace]
  refine ⟨34647905874957217548064445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92394415666552580128171853 34647905874957217548064445)
  ·
    refine ⟨12992964703108956580524167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34647905874957217548064445 12992964703108956580524167)
    ·
      refine ⟨19489447054663434870786251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12992964703108956580524167 19489447054663434870786251)
      ·
        refine ⟨29234170581995152306179377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19489447054663434870786251 29234170581995152306179377)
        ·
          refine ⟨21925627936496364229634533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29234170581995152306179377 21925627936496364229634533)
          ·
            refine ⟨4111055238093068293056475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21925627936496364229634533 4111055238093068293056475)
            ·
              refine ⟨6166582857139602439584713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111055238093068293056475 6166582857139602439584713)
              ·
                refine ⟨4624937142854701829688535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6166582857139602439584713 4624937142854701829688535)
                ·
                  refine ⟨6937405714282052744532803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624937142854701829688535 6937405714282052744532803)
                  ·
                    refine ⟨10406108571423079116799205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6937405714282052744532803 10406108571423079116799205)
                    ·
                      refine ⟨1951145357141827334399851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10406108571423079116799205 1951145357141827334399851)
                      ·
                        rfl

theorem cell23_3799842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_3799842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799842 prefixEnd_3799842 := by exact prefixLift 3799842
  have htrace : WordTrace (prefixWord ++ tailWord_3799842) baseStart_3799842 baseEnd_3799842 := by
    simpa [prefixWord, tailWord_3799842, baseEnd_3799842] using wordTrace_append hprefix tailTrace_3799842
  have hstable : (prefixWord ++ tailWord_3799842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799842).length < 2 ^ (prefixWord ++ tailWord_3799842).sum := by decide
  have hdescent : baseEnd_3799842 < baseStart_3799842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799892 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_3799892 : Nat := 118140960795 + 3799892 * 2 ^ 59
def prefixEnd_3799892 : Nat := 4983230072969 + 3 ^ 40 * 3799892 * 2
def baseEnd_3799892 : Nat := 1951171031174552138774621

theorem tailTrace_3799892 : CollatzResearch.WordTrace tailWord_3799892 prefixEnd_3799892 1951171031174552138774621 := by
  unfold tailWord_3799892
  simp only [CollatzResearch.WordTrace]
  refine ⟨69296723574823864365788965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92395631433098485821051953 69296723574823864365788965)
  ·
    refine ⟨12993135670279474568585431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69296723574823864365788965 12993135670279474568585431)
    ·
      refine ⟨19489703505419211852878147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12993135670279474568585431 19489703505419211852878147)
      ·
        refine ⟨29234555258128817779317221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19489703505419211852878147 29234555258128817779317221)
        ·
          refine ⟨5481479110899153333621979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29234555258128817779317221 5481479110899153333621979)
          ·
            refine ⟨8222218666348730000432969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5481479110899153333621979 8222218666348730000432969)
            ·
              refine ⟨6166663999761547500324727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8222218666348730000432969 6166663999761547500324727)
              ·
                refine ⟨9249995999642321250487091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166663999761547500324727 9249995999642321250487091)
                ·
                  refine ⟨13874993999463481875730637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9249995999642321250487091 13874993999463481875730637)
                  ·
                    refine ⟨5203122749798805703398989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13874993999463481875730637 5203122749798805703398989)
                    ·
                      refine ⟨1951171031174552138774621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5203122749798805703398989 1951171031174552138774621)
                      ·
                        rfl

theorem cell23_3799892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_3799892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799892 prefixEnd_3799892 := by exact prefixLift 3799892
  have htrace : WordTrace (prefixWord ++ tailWord_3799892) baseStart_3799892 baseEnd_3799892 := by
    simpa [prefixWord, tailWord_3799892, baseEnd_3799892] using wordTrace_append hprefix tailTrace_3799892
  have hstable : (prefixWord ++ tailWord_3799892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799892).length < 2 ^ (prefixWord ++ tailWord_3799892).sum := by decide
  have hdescent : baseEnd_3799892 < baseStart_3799892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799915 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 1, 4, 2]
def baseStart_3799915 : Nat := 118140960795 + 3799915 * 2 ^ 59
def prefixEnd_3799915 : Nat := 4983230072969 + 3 ^ 40 * 3799915 * 2
def baseEnd_3799915 : Nat := 1951182841229605548787015

theorem tailTrace_3799915 : CollatzResearch.WordTrace tailWord_3799915 prefixEnd_3799915 1951182841229605548787015 := by
  unfold tailWord_3799915
  simp only [CollatzResearch.WordTrace]
  refine ⟨138594286028564403659665199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92396190685709602439776799 138594286028564403659665199)
  ·
    refine ⟨207891429042846605489497799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138594286028564403659665199 207891429042846605489497799)
    ·
      refine ⟨311837143564269908234246699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207891429042846605489497799 311837143564269908234246699)
      ·
        refine ⟨467755715346404862351370049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311837143564269908234246699 467755715346404862351370049)
        ·
          refine ⟨350816786509803646763527537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467755715346404862351370049 350816786509803646763527537)
          ·
            refine ⟨263112589882352735072645653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350816786509803646763527537 263112589882352735072645653)
            ·
              refine ⟨12333402650735284456530265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263112589882352735072645653 12333402650735284456530265)
              ·
                refine ⟨9250051988051463342397699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12333402650735284456530265 9250051988051463342397699)
                ·
                  refine ⟨13875077982077195013596549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9250051988051463342397699 13875077982077195013596549)
                  ·
                    refine ⟨2601577121639474065049353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13875077982077195013596549 2601577121639474065049353)
                    ·
                      refine ⟨1951182841229605548787015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2601577121639474065049353 1951182841229605548787015)
                      ·
                        rfl

theorem cell23_3799915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 4, 2].length) (baseStart_3799915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799915 prefixEnd_3799915 := by exact prefixLift 3799915
  have htrace : WordTrace (prefixWord ++ tailWord_3799915) baseStart_3799915 baseEnd_3799915 := by
    simpa [prefixWord, tailWord_3799915, baseEnd_3799915] using wordTrace_append hprefix tailTrace_3799915
  have hstable : (prefixWord ++ tailWord_3799915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799915).length < 2 ^ (prefixWord ++ tailWord_3799915).sum := by decide
  have hdescent : baseEnd_3799915 < baseStart_3799915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799926 : List Nat := [5, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3799926 : Nat := 118140960795 + 3799926 * 2 ^ 59
def prefixEnd_3799926 : Nat := 4983230072969 + 3 ^ 40 * 3799926 * 2
def baseEnd_3799926 : Nat := 1951188489516805005749465

theorem tailTrace_3799926 : CollatzResearch.WordTrace tailWord_3799926 prefixEnd_3799926 1951188489516805005749465 := by
  unfold tailWord_3799926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8662167951970284533644727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92396458154349701692210421 8662167951970284533644727)
  ·
    refine ⟨12993251927955426800467091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8662167951970284533644727 12993251927955426800467091)
    ·
      refine ⟨19489877891933140200700637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12993251927955426800467091 19489877891933140200700637)
      ·
        refine ⟨7308704209474927575262739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19489877891933140200700637 7308704209474927575262739)
        ·
          refine ⟨10963056314212391362894109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7308704209474927575262739 10963056314212391362894109)
          ·
            refine ⟨4111146117829646761085291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10963056314212391362894109 4111146117829646761085291)
            ·
              refine ⟨6166719176744470141627937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111146117829646761085291 6166719176744470141627937)
              ·
                refine ⟨4625039382558352606220953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6166719176744470141627937 4625039382558352606220953)
                ·
                  refine ⟨3468779536918764454665715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4625039382558352606220953 3468779536918764454665715)
                  ·
                    refine ⟨5203169305378146681998573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3468779536918764454665715 5203169305378146681998573)
                    ·
                      refine ⟨1951188489516805005749465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5203169305378146681998573 1951188489516805005749465)
                      ·
                        rfl

theorem cell23_3799926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3799926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799926 prefixEnd_3799926 := by exact prefixLift 3799926
  have htrace : WordTrace (prefixWord ++ tailWord_3799926) baseStart_3799926 baseEnd_3799926 := by
    simpa [prefixWord, tailWord_3799926, baseEnd_3799926] using wordTrace_append hprefix tailTrace_3799926
  have hstable : (prefixWord ++ tailWord_3799926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799926).length < 2 ^ (prefixWord ++ tailWord_3799926).sum := by decide
  have hdescent : baseEnd_3799926 < baseStart_3799926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799968 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 1, 7]
def baseStart_3799968 : Nat := 118140960795 + 3799968 * 2 ^ 59
def prefixEnd_3799968 : Nat := 4983230072969 + 3 ^ 40 * 3799968 * 2
def baseEnd_3799968 : Nat := 650403351901431280474757

theorem tailTrace_3799968 : CollatzResearch.WordTrace tailWord_3799968 prefixEnd_3799968 650403351901431280474757 := by
  unfold tailWord_3799968
  simp only [CollatzResearch.WordTrace]
  refine ⟨69298109548686196855672279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92397479398248262474229705 69298109548686196855672279)
  ·
    refine ⟨103947164323029295283508419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69298109548686196855672279 103947164323029295283508419)
    ·
      refine ⟨155920746484543942925262629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103947164323029295283508419 155920746484543942925262629)
      ·
        refine ⟨29235139965851989298486743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155920746484543942925262629 29235139965851989298486743)
        ·
          refine ⟨43852709948777983947730115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29235139965851989298486743 43852709948777983947730115)
          ·
            refine ⟨65779064923166975921595173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43852709948777983947730115 65779064923166975921595173)
            ·
              refine ⟨12333574673093807985299095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65779064923166975921595173 12333574673093807985299095)
              ·
                refine ⟨18500362009640711977948643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12333574673093807985299095 18500362009640711977948643)
                ·
                  refine ⟨27750543014461067966922965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18500362009640711977948643 27750543014461067966922965)
                  ·
                    refine ⟨650403351901431280474757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27750543014461067966922965 650403351901431280474757)
                    ·
                      rfl

theorem cell23_3799968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_3799968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3799968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3799968 prefixEnd_3799968 := by exact prefixLift 3799968
  have htrace : WordTrace (prefixWord ++ tailWord_3799968) baseStart_3799968 baseEnd_3799968 := by
    simpa [prefixWord, tailWord_3799968, baseEnd_3799968] using wordTrace_append hprefix tailTrace_3799968
  have hstable : (prefixWord ++ tailWord_3799968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799968).length < 2 ^ (prefixWord ++ tailWord_3799968).sum := by decide
  have hdescent : baseEnd_3799968 < baseStart_3799968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800005 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 6, 4, 2]
def baseStart_3800005 : Nat := 118140960795 + 3800005 * 2 ^ 59
def prefixEnd_3800005 : Nat := 4983230072969 + 3 ^ 40 * 3800005 * 2
def baseEnd_3800005 : Nat := 1951229054488510196661601

theorem tailTrace_3800005 : CollatzResearch.WordTrace tailWord_3800005 prefixEnd_3800005 1951229054488510196661601 := by
  unfold tailWord_3800005
  simp only [CollatzResearch.WordTrace]
  refine ⟨138597568598238349030441469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92398379065492232686960979 138597568598238349030441469)
  ·
    refine ⟨51974088224339380886415551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138597568598238349030441469 51974088224339380886415551)
    ·
      refine ⟨77961132336509071329623327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51974088224339380886415551 77961132336509071329623327)
      ·
        refine ⟨116941698504763606994434991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77961132336509071329623327 116941698504763606994434991)
        ·
          refine ⟨175412547757145410491652487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116941698504763606994434991 175412547757145410491652487)
          ·
            refine ⟨263118821635718115737478731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175412547757145410491652487 263118821635718115737478731)
            ·
              refine ⟨394678232453577173606218097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263118821635718115737478731 394678232453577173606218097)
              ·
                refine ⟨296008674340182880204663573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394678232453577173606218097 296008674340182880204663573)
                ·
                  refine ⟨13875406609696072509593605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 296008674340182880204663573 13875406609696072509593605)
                  ·
                    refine ⟨2601638739318013595548801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13875406609696072509593605 2601638739318013595548801)
                    ·
                      refine ⟨1951229054488510196661601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2601638739318013595548801 1951229054488510196661601)
                      ·
                        rfl

theorem cell23_3800005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 4, 2].length) (baseStart_3800005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800005 prefixEnd_3800005 := by exact prefixLift 3800005
  have htrace : WordTrace (prefixWord ++ tailWord_3800005) baseStart_3800005 baseEnd_3800005 := by
    simpa [prefixWord, tailWord_3800005, baseEnd_3800005] using wordTrace_append hprefix tailTrace_3800005
  have hstable : (prefixWord ++ tailWord_3800005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800005).length < 2 ^ (prefixWord ++ tailWord_3800005).sum := by decide
  have hdescent : baseEnd_3800005 < baseStart_3800005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800042 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_3800042 : Nat := 118140960795 + 3800042 * 2 ^ 59
def prefixEnd_3800042 : Nat := 4983230072969 + 3 ^ 40 * 3800042 * 2
def baseEnd_3800042 : Nat := 1951248053272726551898931

theorem tailTrace_3800042 : CollatzResearch.WordTrace tailWord_3800042 prefixEnd_3800042 1951248053272726551898931 := by
  unfold tailWord_3800042
  simp only [CollatzResearch.WordTrace]
  refine ⟨34649729524776076087384595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92399278732736202899692253 34649729524776076087384595)
  ·
    refine ⟨51974594287164114131076893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34649729524776076087384595 51974594287164114131076893)
    ·
      refine ⟨19490472857686542799153835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51974594287164114131076893 19490472857686542799153835)
      ·
        refine ⟨29235709286529814198730753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19490472857686542799153835 29235709286529814198730753)
        ·
          refine ⟨21926781964897360649048065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29235709286529814198730753 21926781964897360649048065)
          ·
            refine ⟨16445086473673020486786049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21926781964897360649048065 16445086473673020486786049)
            ·
              refine ⟨12333814855254765365089537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16445086473673020486786049 12333814855254765365089537)
              ·
                refine ⟨9250361141441074023817153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12333814855254765365089537 9250361141441074023817153)
                ·
                  refine ⟨6937770856080805517862865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9250361141441074023817153 6937770856080805517862865)
                  ·
                    refine ⟨5203328142060604138397149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6937770856080805517862865 5203328142060604138397149)
                    ·
                      refine ⟨1951248053272726551898931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5203328142060604138397149 1951248053272726551898931)
                      ·
                        rfl

theorem cell23_3800042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_3800042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800042 prefixEnd_3800042 := by exact prefixLift 3800042
  have htrace : WordTrace (prefixWord ++ tailWord_3800042) baseStart_3800042 baseEnd_3800042 := by
    simpa [prefixWord, tailWord_3800042, baseEnd_3800042] using wordTrace_append hprefix tailTrace_3800042
  have hstable : (prefixWord ++ tailWord_3800042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800042).length < 2 ^ (prefixWord ++ tailWord_3800042).sum := by decide
  have hdescent : baseEnd_3800042 < baseStart_3800042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800048 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 6]
def baseStart_3800048 : Nat := 118140960795 + 3800048 * 2 ^ 59
def prefixEnd_3800048 : Nat := 4983230072969 + 3 ^ 40 * 3800048 * 2
def baseEnd_3800048 : Nat := 1951251134156653528423903

theorem tailTrace_3800048 : CollatzResearch.WordTrace tailWord_3800048 prefixEnd_3800048 1951251134156653528423903 := by
  unfold tailWord_3800048
  simp only [CollatzResearch.WordTrace]
  refine ⟨69299568468541283687128399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92399424624721711582837865 69299568468541283687128399)
  ·
    refine ⟨103949352702811925530692599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69299568468541283687128399 103949352702811925530692599)
    ·
      refine ⟨155924029054217888296038899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103949352702811925530692599 155924029054217888296038899)
      ·
        refine ⟨233886043581326832444058349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155924029054217888296038899 233886043581326832444058349)
        ·
          refine ⟨87707266342997562166521881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233886043581326832444058349 87707266342997562166521881)
          ·
            refine ⟨65780449757248171624891411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87707266342997562166521881 65780449757248171624891411)
            ·
              refine ⟨98670674635872257437337117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65780449757248171624891411 98670674635872257437337117)
              ·
                refine ⟨37001502988452096539001419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98670674635872257437337117 37001502988452096539001419)
                ·
                  refine ⟨55502254482678144808502129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37001502988452096539001419 55502254482678144808502129)
                  ·
                    refine ⟨41626690862008608606376597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55502254482678144808502129 41626690862008608606376597)
                    ·
                      refine ⟨1951251134156653528423903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41626690862008608606376597 1951251134156653528423903)
                      ·
                        rfl

theorem cell23_3800048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_3800048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800048 prefixEnd_3800048 := by exact prefixLift 3800048
  have htrace : WordTrace (prefixWord ++ tailWord_3800048) baseStart_3800048 baseEnd_3800048 := by
    simpa [prefixWord, tailWord_3800048, baseEnd_3800048] using wordTrace_append hprefix tailTrace_3800048
  have hstable : (prefixWord ++ tailWord_3800048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800048).length < 2 ^ (prefixWord ++ tailWord_3800048).sum := by decide
  have hdescent : baseEnd_3800048 < baseStart_3800048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800049 : List Nat := [1, 2, 2, 2, 4, 2, 1, 4, 1, 4]
def baseStart_3800049 : Nat := 118140960795 + 3800049 * 2 ^ 59
def prefixEnd_3800049 : Nat := 4983230072969 + 3 ^ 40 * 3800049 * 2
def baseEnd_3800049 : Nat := 650417215879102674837133

theorem tailTrace_3800049 : CollatzResearch.WordTrace tailWord_3800049 prefixEnd_3800049 650417215879102674837133 := by
  unfold tailWord_3800049
  simp only [CollatzResearch.WordTrace]
  refine ⟨138599173410078944545043201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92399448940052629696695467 138599173410078944545043201)
  ·
    refine ⟨103949380057559208408782401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138599173410078944545043201 103949380057559208408782401)
    ·
      refine ⟨77962035043169406306586801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103949380057559208408782401 77962035043169406306586801)
      ·
        refine ⟨58471526282377054729940101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77962035043169406306586801 58471526282377054729940101)
        ·
          refine ⟨10963411177945697761863769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58471526282377054729940101 10963411177945697761863769)
          ·
            refine ⟨8222558383459273321397827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10963411177945697761863769 8222558383459273321397827)
            ·
              refine ⟨12333837575188909982096741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8222558383459273321397827 12333837575188909982096741)
              ·
                refine ⟨2312594545347920621643139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12333837575188909982096741 2312594545347920621643139)
                ·
                  refine ⟨3468891818021880932464709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312594545347920621643139 3468891818021880932464709)
                  ·
                    refine ⟨650417215879102674837133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3468891818021880932464709 650417215879102674837133)
                    ·
                      rfl

theorem cell23_3800049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_3800049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800049 prefixEnd_3800049 := by exact prefixLift 3800049
  have htrace : WordTrace (prefixWord ++ tailWord_3800049) baseStart_3800049 baseEnd_3800049 := by
    simpa [prefixWord, tailWord_3800049, baseEnd_3800049] using wordTrace_append hprefix tailTrace_3800049
  have hstable : (prefixWord ++ tailWord_3800049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800049).length < 2 ^ (prefixWord ++ tailWord_3800049).sum := by decide
  have hdescent : baseEnd_3800049 < baseStart_3800049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800066 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_3800066 : Nat := 118140960795 + 3800066 * 2 ^ 59
def prefixEnd_3800066 : Nat := 4983230072969 + 3 ^ 40 * 3800066 * 2
def baseEnd_3800066 : Nat := 650420125602811485999607

theorem tailTrace_3800066 : CollatzResearch.WordTrace tailWord_3800066 prefixEnd_3800066 650420125602811485999607 := by
  unfold tailWord_3800066
  simp only [CollatzResearch.WordTrace]
  refine ⟨34649948362754339112103013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92399862300678237632274701 34649948362754339112103013)
  ·
    refine ⟨6496865318016438583519315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34649948362754339112103013 6496865318016438583519315)
    ·
      refine ⟨9745297977024657875278973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6496865318016438583519315 9745297977024657875278973)
      ·
        refine ⟨3654486741384246703229615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9745297977024657875278973 3654486741384246703229615)
        ·
          refine ⟨5481730112076370054844423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654486741384246703229615 5481730112076370054844423)
          ·
            refine ⟨8222595168114555082266635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5481730112076370054844423 8222595168114555082266635)
            ·
              refine ⟨12333892752171832623399953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8222595168114555082266635 12333892752171832623399953)
              ·
                refine ⟨9250419564128874467549965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12333892752171832623399953 9250419564128874467549965)
                ·
                  refine ⟨3468907336548327925331237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9250419564128874467549965 3468907336548327925331237)
                  ·
                    refine ⟨650420125602811485999607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3468907336548327925331237 650420125602811485999607)
                    ·
                      rfl

theorem cell23_3800066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_3800066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800066 prefixEnd_3800066 := by exact prefixLift 3800066
  have htrace : WordTrace (prefixWord ++ tailWord_3800066) baseStart_3800066 baseEnd_3800066 := by
    simpa [prefixWord, tailWord_3800066, baseEnd_3800066] using wordTrace_append hprefix tailTrace_3800066
  have hstable : (prefixWord ++ tailWord_3800066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800066).length < 2 ^ (prefixWord ++ tailWord_3800066).sum := by decide
  have hdescent : baseEnd_3800066 < baseStart_3800066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800072 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_3800072 : Nat := 118140960795 + 3800072 * 2 ^ 59
def prefixEnd_3800072 : Nat := 4983230072969 + 3 ^ 40 * 3800072 * 2
def baseEnd_3800072 : Nat := 1951263457692361434523793

theorem tailTrace_3800072 : CollatzResearch.WordTrace tailWord_3800072 prefixEnd_3800072 1951263457692361434523793 := by
  unfold tailWord_3800072
  simp only [CollatzResearch.WordTrace]
  refine ⟨69300006144497809736565235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92400008192663746315420313 69300006144497809736565235)
  ·
    refine ⟨103950009216746714604847853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69300006144497809736565235 103950009216746714604847853)
    ·
      refine ⟨38981253456280017976817945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103950009216746714604847853 38981253456280017976817945)
      ·
        refine ⟨29235940092210013482613459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38981253456280017976817945 29235940092210013482613459)
        ·
          refine ⟨43853910138315020223920189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29235940092210013482613459 43853910138315020223920189)
          ·
            refine ⟨16445216301868132583970071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43853910138315020223920189 16445216301868132583970071)
            ·
              refine ⟨24667824452802198875955107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16445216301868132583970071 24667824452802198875955107)
              ·
                refine ⟨37001736679203298313932661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24667824452802198875955107 37001736679203298313932661)
                ·
                  refine ⟨3468912813675309216931187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37001736679203298313932661 3468912813675309216931187)
                  ·
                    refine ⟨5203369220512963825396781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3468912813675309216931187 5203369220512963825396781)
                    ·
                      refine ⟨1951263457692361434523793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5203369220512963825396781 1951263457692361434523793)
                      ·
                        rfl

theorem cell23_3800072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_3800072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800072 prefixEnd_3800072 := by exact prefixLift 3800072
  have htrace : WordTrace (prefixWord ++ tailWord_3800072) baseStart_3800072 baseEnd_3800072 := by
    simpa [prefixWord, tailWord_3800072, baseEnd_3800072] using wordTrace_append hprefix tailTrace_3800072
  have hstable : (prefixWord ++ tailWord_3800072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800072).length < 2 ^ (prefixWord ++ tailWord_3800072).sum := by decide
  have hdescent : baseEnd_3800072 < baseStart_3800072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800075 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 3, 5]
def baseStart_3800075 : Nat := 118140960795 + 3800075 * 2 ^ 59
def prefixEnd_3800075 : Nat := 4983230072969 + 3 ^ 40 * 3800075 * 2
def baseEnd_3800075 : Nat := 650421666044774974262093

theorem tailTrace_3800075 : CollatzResearch.WordTrace tailWord_3800075 prefixEnd_3800075 650421666044774974262093 := by
  unfold tailWord_3800075
  simp only [CollatzResearch.WordTrace]
  refine ⟨138600121707984750985489679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92400081138656500656993119 138600121707984750985489679)
  ·
    refine ⟨207900182561977126478234519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138600121707984750985489679 207900182561977126478234519)
    ·
      refine ⟨311850273842965689717351779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207900182561977126478234519 311850273842965689717351779)
      ·
        refine ⟨467775410764448534576027669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311850273842965689717351779 467775410764448534576027669)
        ·
          refine ⟨21926972379583525058251297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 467775410764448534576027669 21926972379583525058251297)
          ·
            refine ⟨16445229284687643793688473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21926972379583525058251297 16445229284687643793688473)
            ·
              refine ⟨12333921963515732845266355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16445229284687643793688473 12333921963515732845266355)
              ·
                refine ⟨18500882945273599267899533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12333921963515732845266355 18500882945273599267899533)
                ·
                  refine ⟨6937831104477599725462325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18500882945273599267899533 6937831104477599725462325)
                  ·
                    refine ⟨650421666044774974262093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6937831104477599725462325 650421666044774974262093)
                    ·
                      rfl

theorem cell23_3800075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 5].length) (baseStart_3800075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800075 prefixEnd_3800075 := by exact prefixLift 3800075
  have htrace : WordTrace (prefixWord ++ tailWord_3800075) baseStart_3800075 baseEnd_3800075 := by
    simpa [prefixWord, tailWord_3800075, baseEnd_3800075] using wordTrace_append hprefix tailTrace_3800075
  have hstable : (prefixWord ++ tailWord_3800075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800075).length < 2 ^ (prefixWord ++ tailWord_3800075).sum := by decide
  have hdescent : baseEnd_3800075 < baseStart_3800075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800089 : List Nat := [1, 2, 1, 2, 1, 1, 5, 5, 1, 1, 3]
def baseStart_3800089 : Nat := 118140960795 + 3800089 * 2 ^ 59
def prefixEnd_3800089 : Nat := 4983230072969 + 3 ^ 40 * 3800089 * 2
def baseEnd_3800089 : Nat := 1951272186863487868011215

theorem tailTrace_3800089 : CollatzResearch.WordTrace tailWord_3800089 prefixEnd_3800089 1951272186863487868011215 := by
  unfold tailWord_3800089
  simp only [CollatzResearch.WordTrace]
  refine ⟨138600632329934031376499321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92400421553289354250999547 138600632329934031376499321)
  ·
    refine ⟨103950474247450523532374491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138600632329934031376499321 103950474247450523532374491)
    ·
      refine ⟨155925711371175785298561737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103950474247450523532374491 155925711371175785298561737)
      ·
        refine ⟨116944283528381838973921303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155925711371175785298561737 116944283528381838973921303)
        ·
          refine ⟨175416425292572758460881955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116944283528381838973921303 175416425292572758460881955)
          ·
            refine ⟨263124637938859137691322933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175416425292572758460881955 263124637938859137691322933)
            ·
              refine ⟨24667934806768044158561525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263124637938859137691322933 24667934806768044158561525)
              ·
                refine ⟨2312618888134504139865143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24667934806768044158561525 2312618888134504139865143)
                ·
                  refine ⟨3468928332201756209797715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312618888134504139865143 3468928332201756209797715)
                  ·
                    refine ⟨5203392498302634314696573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3468928332201756209797715 5203392498302634314696573)
                    ·
                      refine ⟨1951272186863487868011215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5203392498302634314696573 1951272186863487868011215)
                      ·
                        rfl

theorem cell23_3800089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 1, 1, 3].length) (baseStart_3800089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800089 prefixEnd_3800089 := by exact prefixLift 3800089
  have htrace : WordTrace (prefixWord ++ tailWord_3800089) baseStart_3800089 baseEnd_3800089 := by
    simpa [prefixWord, tailWord_3800089, baseEnd_3800089] using wordTrace_append hprefix tailTrace_3800089
  have hstable : (prefixWord ++ tailWord_3800089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800089).length < 2 ^ (prefixWord ++ tailWord_3800089).sum := by decide
  have hdescent : baseEnd_3800089 < baseStart_3800089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800096 : List Nat := [2, 1, 1, 7, 2, 1, 1, 2, 6]
def baseStart_3800096 : Nat := 118140960795 + 3800096 * 2 ^ 59
def prefixEnd_3800096 : Nat := 4983230072969 + 3 ^ 40 * 3800096 * 2
def baseEnd_3800096 : Nat := 216808420136452148958187

theorem tailTrace_3800096 : CollatzResearch.WordTrace tailWord_3800096 prefixEnd_3800096 216808420136452148958187 := by
  unfold tailWord_3800096
  simp only [CollatzResearch.WordTrace]
  refine ⟨69300443820454335786002071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92400591760605781048002761 69300443820454335786002071)
  ·
    refine ⟨103950665730681503679003107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69300443820454335786002071 103950665730681503679003107)
    ·
      refine ⟨155925998596022255518504661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103950665730681503679003107 155925998596022255518504661)
      ·
        refine ⟨3654515592094271613714953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 155925998596022255518504661 3654515592094271613714953)
        ·
          refine ⟨2740886694070703710286215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3654515592094271613714953 2740886694070703710286215)
          ·
            refine ⟨4111330041106055565429323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2740886694070703710286215 4111330041106055565429323)
            ·
              refine ⟨6166995061659083348143985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111330041106055565429323 6166995061659083348143985)
              ·
                refine ⟨4625246296244312511107989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6166995061659083348143985 4625246296244312511107989)
                ·
                  refine ⟨216808420136452148958187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4625246296244312511107989 216808420136452148958187)
                  ·
                    rfl

theorem cell23_3800096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 6].length) (baseStart_3800096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800096 prefixEnd_3800096 := by exact prefixLift 3800096
  have htrace : WordTrace (prefixWord ++ tailWord_3800096) baseStart_3800096 baseEnd_3800096 := by
    simpa [prefixWord, tailWord_3800096, baseEnd_3800096] using wordTrace_append hprefix tailTrace_3800096
  have hstable : (prefixWord ++ tailWord_3800096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800096).length < 2 ^ (prefixWord ++ tailWord_3800096).sum := by decide
  have hdescent : baseEnd_3800096 < baseStart_3800096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800106 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_3800106 : Nat := 118140960795 + 3800106 * 2 ^ 59
def prefixEnd_3800106 : Nat := 4983230072969 + 3 ^ 40 * 3800106 * 2
def baseEnd_3800106 : Nat := 1951280916034614301498637

theorem tailTrace_3800106 : CollatzResearch.WordTrace tailWord_3800106 prefixEnd_3800106 1951280916034614301498637 := by
  unfold tailWord_3800106
  simp only [CollatzResearch.WordTrace]
  refine ⟨34650313092718110819967043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92400834913914962186578781 34650313092718110819967043)
  ·
    refine ⟨51975469639077166229950565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34650313092718110819967043 51975469639077166229950565)
    ·
      refine ⟨9745400557326968668115731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51975469639077166229950565 9745400557326968668115731)
      ·
        refine ⟨14618100835990453002173597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9745400557326968668115731 14618100835990453002173597)
        ·
          refine ⟨5481787813496419875815099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14618100835990453002173597 5481787813496419875815099)
          ·
            refine ⟨8222681720244629813722649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5481787813496419875815099 8222681720244629813722649)
            ·
              refine ⟨6167011290183472360291987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8222681720244629813722649 6167011290183472360291987)
              ·
                refine ⟨9250516935275208540437981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167011290183472360291987 9250516935275208540437981)
                ·
                  refine ⟨3468943850728203202664243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9250516935275208540437981 3468943850728203202664243)
                  ·
                    refine ⟨5203415776092304803996365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3468943850728203202664243 5203415776092304803996365)
                    ·
                      refine ⟨1951280916034614301498637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5203415776092304803996365 1951280916034614301498637)
                      ·
                        rfl

theorem cell23_3800106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_3800106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800106 prefixEnd_3800106 := by exact prefixLift 3800106
  have htrace : WordTrace (prefixWord ++ tailWord_3800106) baseStart_3800106 baseEnd_3800106 := by
    simpa [prefixWord, tailWord_3800106, baseEnd_3800106] using wordTrace_append hprefix tailTrace_3800106
  have hstable : (prefixWord ++ tailWord_3800106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800106).length < 2 ^ (prefixWord ++ tailWord_3800106).sum := by decide
  have hdescent : baseEnd_3800106 < baseStart_3800106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800122 : List Nat := [3, 1, 1, 1, 3, 1, 2, 5, 2, 4]
def baseStart_3800122 : Nat := 118140960795 + 3800122 * 2 ^ 59
def prefixEnd_3800122 : Nat := 4983230072969 + 3 ^ 40 * 3800122 * 2
def baseEnd_3800122 : Nat := 650429710575028746299521

theorem tailTrace_3800122 : CollatzResearch.WordTrace tailWord_3800122 prefixEnd_3800122 650429710575028746299521 := by
  unfold tailWord_3800122
  simp only [CollatzResearch.WordTrace]
  refine ⟨34650458984703619503112655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92401223959209652008300413 34650458984703619503112655)
  ·
    refine ⟨51975688477055429254668983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34650458984703619503112655 51975688477055429254668983)
    ·
      refine ⟨77963532715583143882003475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51975688477055429254668983 77963532715583143882003475)
      ·
        refine ⟨116945299073374715823005213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77963532715583143882003475 116945299073374715823005213)
        ·
          refine ⟨43854487152515518433626955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116945299073374715823005213 43854487152515518433626955)
          ·
            refine ⟨65781730728773277650440433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43854487152515518433626955 65781730728773277650440433)
            ·
              refine ⟨49336298046579958237830325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65781730728773277650440433 49336298046579958237830325)
              ·
                refine ⟨4625277941866871084796593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49336298046579958237830325 4625277941866871084796593)
                ·
                  refine ⟨3468958456400153313597445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4625277941866871084796593 3468958456400153313597445)
                  ·
                    refine ⟨650429710575028746299521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3468958456400153313597445 650429710575028746299521)
                    ·
                      rfl

theorem cell23_3800122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_3800122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800122 prefixEnd_3800122 := by exact prefixLift 3800122
  have htrace : WordTrace (prefixWord ++ tailWord_3800122) baseStart_3800122 baseEnd_3800122 := by
    simpa [prefixWord, tailWord_3800122, baseEnd_3800122] using wordTrace_append hprefix tailTrace_3800122
  have hstable : (prefixWord ++ tailWord_3800122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800122).length < 2 ^ (prefixWord ++ tailWord_3800122).sum := by decide
  have hdescent : baseEnd_3800122 < baseStart_3800122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800135 : List Nat := [1, 1, 4, 1, 3, 3, 1, 9]
def baseStart_3800135 : Nat := 118140960795 + 3800135 * 2 ^ 59
def prefixEnd_3800135 : Nat := 4983230072969 + 3 ^ 40 * 3800135 * 2
def baseEnd_3800135 : Nat := 72270215073096099556889

theorem tailTrace_3800135 : CollatzResearch.WordTrace tailWord_3800135 prefixEnd_3800135 72270215073096099556889 := by
  unfold tailWord_3800135
  simp only [CollatzResearch.WordTrace]
  refine ⟨138602310087767381232673859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92401540058511587488449239 138602310087767381232673859)
  ·
    refine ⟨207903465131651071849010789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138602310087767381232673859 207903465131651071849010789)
    ·
      refine ⟨38981899712184575971689523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207903465131651071849010789 38981899712184575971689523)
      ·
        refine ⟨58472849568276863957534285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38981899712184575971689523 58472849568276863957534285)
        ·
          refine ⟨21927318588103823984075357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58472849568276863957534285 21927318588103823984075357)
          ·
            refine ⟨8222744470538933994028259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21927318588103823984075357 8222744470538933994028259)
            ·
              refine ⟨12334116705808400991042389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8222744470538933994028259 12334116705808400991042389)
              ·
                refine ⟨72270215073096099556889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12334116705808400991042389 72270215073096099556889)
                ·
                  rfl

theorem cell23_3800135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 9].length) (baseStart_3800135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800135 prefixEnd_3800135 := by exact prefixLift 3800135
  have htrace : WordTrace (prefixWord ++ tailWord_3800135) baseStart_3800135 baseEnd_3800135 := by
    simpa [prefixWord, tailWord_3800135, baseEnd_3800135] using wordTrace_append hprefix tailTrace_3800135
  have hstable : (prefixWord ++ tailWord_3800135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800135).length < 2 ^ (prefixWord ++ tailWord_3800135).sum := by decide
  have hdescent : baseEnd_3800135 < baseStart_3800135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800165 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 2, 7]
def baseStart_3800165 : Nat := 118140960795 + 3800165 * 2 ^ 59
def prefixEnd_3800165 : Nat := 4983230072969 + 3 ^ 40 * 3800165 * 2
def baseEnd_3800165 : Nat := 650437070464409856886955

theorem tailTrace_3800165 : CollatzResearch.WordTrace tailWord_3800165 prefixEnd_3800165 650437070464409856886955 := by
  unfold tailWord_3800165
  simp only [CollatzResearch.WordTrace]
  refine ⟨138603404277658696356265949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92402269518439130904177299 138603404277658696356265949)
  ·
    refine ⟨51976276604122011133599731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138603404277658696356265949 51976276604122011133599731)
    ·
      refine ⟨77964414906183016700399597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51976276604122011133599731 77964414906183016700399597)
      ·
        refine ⟨29236655589818631262649849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77964414906183016700399597 29236655589818631262649849)
        ·
          refine ⟨21927491692363973446987387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29236655589818631262649849 21927491692363973446987387)
          ·
            refine ⟨32891237538545960170481081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21927491692363973446987387 32891237538545960170481081)
            ·
              refine ⟨24668428153909470127860811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32891237538545960170481081 24668428153909470127860811)
              ·
                refine ⟨37002642230864205191791217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24668428153909470127860811 37002642230864205191791217)
                ·
                  refine ⟨27751981673148153893843413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37002642230864205191791217 27751981673148153893843413)
                  ·
                    refine ⟨650437070464409856886955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27751981673148153893843413 650437070464409856886955)
                    ·
                      rfl

theorem cell23_3800165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_3800165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800165 prefixEnd_3800165 := by exact prefixLift 3800165
  have htrace : WordTrace (prefixWord ++ tailWord_3800165) baseStart_3800165 baseEnd_3800165 := by
    simpa [prefixWord, tailWord_3800165, baseEnd_3800165] using wordTrace_append hprefix tailTrace_3800165
  have hstable : (prefixWord ++ tailWord_3800165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800165).length < 2 ^ (prefixWord ++ tailWord_3800165).sum := by decide
  have hdescent : baseEnd_3800165 < baseStart_3800165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800189 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 3, 3, 2]
def baseStart_3800189 : Nat := 118140960795 + 3800189 * 2 ^ 59
def prefixEnd_3800189 : Nat := 4983230072969 + 3 ^ 40 * 3800189 * 2
def baseEnd_3800189 : Nat := 1951323534928937476760755

theorem tailTrace_3800189 : CollatzResearch.WordTrace tailWord_3800189 prefixEnd_3800189 1951323534928937476760755 := by
  unfold tailWord_3800189
  simp only [CollatzResearch.WordTrace]
  refine ⟨138604279629571748455139621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92402853086381165636759747 138604279629571748455139621)
  ·
    refine ⟨25988302430544702835338679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138604279629571748455139621 25988302430544702835338679)
    ·
      refine ⟨38982453645817054253008019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25988302430544702835338679 38982453645817054253008019)
      ·
        refine ⟨58473680468725581379512029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38982453645817054253008019 58473680468725581379512029)
        ·
          refine ⟨21927630175772093017317011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58473680468725581379512029 21927630175772093017317011)
          ·
            refine ⟨32891445263658139525975517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21927630175772093017317011 32891445263658139525975517)
            ·
              refine ⟨12334291973871802322240819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32891445263658139525975517 12334291973871802322240819)
              ·
                refine ⟨18501437960807703483361229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12334291973871802322240819 18501437960807703483361229)
                ·
                  refine ⟨6938039235302888806260461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18501437960807703483361229 6938039235302888806260461)
                  ·
                    refine ⟨2601764713238583302347673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6938039235302888806260461 2601764713238583302347673)
                    ·
                      refine ⟨1951323534928937476760755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2601764713238583302347673 1951323534928937476760755)
                      ·
                        rfl

theorem cell23_3800189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_3800189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800189 prefixEnd_3800189 := by exact prefixLift 3800189
  have htrace : WordTrace (prefixWord ++ tailWord_3800189) baseStart_3800189 baseEnd_3800189 := by
    simpa [prefixWord, tailWord_3800189, baseEnd_3800189] using wordTrace_append hprefix tailTrace_3800189
  have hstable : (prefixWord ++ tailWord_3800189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800189).length < 2 ^ (prefixWord ++ tailWord_3800189).sum := by decide
  have hdescent : baseEnd_3800189 < baseStart_3800189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800242 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 7]
def baseStart_3800242 : Nat := 118140960795 + 3800242 * 2 ^ 59
def prefixEnd_3800242 : Nat := 4983230072969 + 3 ^ 40 * 3800242 * 2
def baseEnd_3800242 : Nat := 216816749933736196599779

theorem tailTrace_3800242 : CollatzResearch.WordTrace tailWord_3800242 prefixEnd_3800242 216816749933736196599779 := by
  unfold tailWord_3800242
  simp only [CollatzResearch.WordTrace]
  refine ⟨34651553174594934626704745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92404141798919825671212653 34651553174594934626704745)
  ·
    refine ⟨25988664880946200970028559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34651553174594934626704745 25988664880946200970028559)
    ·
      refine ⟨38982997321419301455042839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25988664880946200970028559 38982997321419301455042839)
      ·
        refine ⟨58474495982128952182564259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38982997321419301455042839 58474495982128952182564259)
        ·
          refine ⟨87711743973193428273846389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58474495982128952182564259 87711743973193428273846389)
          ·
            refine ⟨8222975997486883900673099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87711743973193428273846389 8222975997486883900673099)
            ·
              refine ⟨12334463996230325851009649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8222975997486883900673099 12334463996230325851009649)
              ·
                refine ⟨9250847997172744388257237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12334463996230325851009649 9250847997172744388257237)
                ·
                  refine ⟨216816749933736196599779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9250847997172744388257237 216816749933736196599779)
                  ·
                    rfl

theorem cell23_3800242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_3800242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800242 prefixEnd_3800242 := by exact prefixLift 3800242
  have htrace : WordTrace (prefixWord ++ tailWord_3800242) baseStart_3800242 baseEnd_3800242 := by
    simpa [prefixWord, tailWord_3800242, baseEnd_3800242] using wordTrace_append hprefix tailTrace_3800242
  have hstable : (prefixWord ++ tailWord_3800242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800242).length < 2 ^ (prefixWord ++ tailWord_3800242).sum := by decide
  have hdescent : baseEnd_3800242 < baseStart_3800242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800270 : List Nat := [4, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2]
def baseStart_3800270 : Nat := 118140960795 + 3800270 * 2 ^ 59
def prefixEnd_3800270 : Nat := 4983230072969 + 3 ^ 40 * 3800270 * 2
def baseEnd_3800270 : Nat := 1951365126861951659847883

theorem tailTrace_3800270 : CollatzResearch.WordTrace tailWord_3800270 prefixEnd_3800270 1951365126861951659847883 := by
  unfold tailWord_3800270
  simp only [CollatzResearch.WordTrace]
  refine ⟨17325904242784787411104783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92404822628185532859225509 17325904242784787411104783)
  ·
    refine ⟨25988856364177181116657175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17325904242784787411104783 25988856364177181116657175)
    ·
      refine ⟨38983284546265771674985763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25988856364177181116657175 38983284546265771674985763)
      ·
        refine ⟨58474926819398657512478645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38983284546265771674985763 58474926819398657512478645)
        ·
          refine ⟨5482024389318624141794873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58474926819398657512478645 5482024389318624141794873)
          ·
            refine ⟨4111518291988968106346155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5482024389318624141794873 4111518291988968106346155)
            ·
              refine ⟨6167277437983452159519233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111518291988968106346155 6167277437983452159519233)
              ·
                refine ⟨4625458078487589119639425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6167277437983452159519233 4625458078487589119639425)
                ·
                  refine ⟨3469093558865691839729569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4625458078487589119639425 3469093558865691839729569)
                  ·
                    refine ⟨2601820169149268879797177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3469093558865691839729569 2601820169149268879797177)
                    ·
                      refine ⟨1951365126861951659847883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2601820169149268879797177 1951365126861951659847883)
                      ·
                        rfl

theorem cell23_3800270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_3800270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800270 prefixEnd_3800270 := by exact prefixLift 3800270
  have htrace : WordTrace (prefixWord ++ tailWord_3800270) baseStart_3800270 baseEnd_3800270 := by
    simpa [prefixWord, tailWord_3800270, baseEnd_3800270] using wordTrace_append hprefix tailTrace_3800270
  have hstable : (prefixWord ++ tailWord_3800270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800270).length < 2 ^ (prefixWord ++ tailWord_3800270).sum := by decide
  have hdescent : baseEnd_3800270 < baseStart_3800270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800276 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 7]
def baseStart_3800276 : Nat := 118140960795 + 3800276 * 2 ^ 59
def prefixEnd_3800276 : Nat := 4983230072969 + 3 ^ 40 * 3800276 * 2
def baseEnd_3800276 : Nat := 216818689749542070708095

theorem tailTrace_3800276 : CollatzResearch.WordTrace tailWord_3800276 prefixEnd_3800276 216818689749542070708095 := by
  unfold tailWord_3800276
  simp only [CollatzResearch.WordTrace]
  refine ⟨69303726390128281156778341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92404968520171041542371121 69303726390128281156778341)
  ·
    refine ⟨12994448698149052716895939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69303726390128281156778341 12994448698149052716895939)
    ·
      refine ⟨19491673047223579075343909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12994448698149052716895939 19491673047223579075343909)
      ·
        refine ⟨3654688696354421076626983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19491673047223579075343909 3654688696354421076626983)
        ·
          refine ⟨5482033044531631614940475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654688696354421076626983 5482033044531631614940475)
          ·
            refine ⟨8223049566797447422410713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5482033044531631614940475 8223049566797447422410713)
            ·
              refine ⟨6167287175098085566808035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8223049566797447422410713 6167287175098085566808035)
              ·
                refine ⟨9250930762647128350212053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167287175098085566808035 9250930762647128350212053)
                ·
                  refine ⟨216818689749542070708095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9250930762647128350212053 216818689749542070708095)
                  ·
                    rfl

theorem cell23_3800276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_3800276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800276 prefixEnd_3800276 := by exact prefixLift 3800276
  have htrace : WordTrace (prefixWord ++ tailWord_3800276) baseStart_3800276 baseEnd_3800276 := by
    simpa [prefixWord, tailWord_3800276, baseEnd_3800276] using wordTrace_append hprefix tailTrace_3800276
  have hstable : (prefixWord ++ tailWord_3800276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800276).length < 2 ^ (prefixWord ++ tailWord_3800276).sum := by decide
  have hdescent : baseEnd_3800276 < baseStart_3800276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800292 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_3800292 : Nat := 118140960795 + 3800292 * 2 ^ 59
def prefixEnd_3800292 : Nat := 4983230072969 + 3 ^ 40 * 3800292 * 2
def baseEnd_3800292 : Nat := 1951376423436350573772781

theorem tailTrace_3800292 : CollatzResearch.WordTrace tailWord_3800292 prefixEnd_3800292 1951376423436350573772781 := by
  unfold tailWord_3800292
  simp only [CollatzResearch.WordTrace]
  refine ⟨69304018174099298523069565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92405357565465731364092753 69304018174099298523069565)
  ·
    refine ⟨25989006815287236946151087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69304018174099298523069565 25989006815287236946151087)
    ·
      refine ⟨38983510222930855419226631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25989006815287236946151087 38983510222930855419226631)
      ·
        refine ⟨58475265334396283128839947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38983510222930855419226631 58475265334396283128839947)
        ·
          refine ⟨87712898001594424693259921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58475265334396283128839947 87712898001594424693259921)
          ·
            refine ⟨65784673501195818519944941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87712898001594424693259921 65784673501195818519944941)
            ·
              refine ⟨24669252562948431944979353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65784673501195818519944941 24669252562948431944979353)
              ·
                refine ⟨18501939422211323958734515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24669252562948431944979353 18501939422211323958734515)
                ·
                  refine ⟨27752909133316985938101773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18501939422211323958734515 27752909133316985938101773)
                  ·
                    refine ⟨10407340924993869726788165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27752909133316985938101773 10407340924993869726788165)
                    ·
                      refine ⟨1951376423436350573772781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10407340924993869726788165 1951376423436350573772781)
                      ·
                        rfl

theorem cell23_3800292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_3800292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800292 prefixEnd_3800292 := by exact prefixLift 3800292
  have htrace : WordTrace (prefixWord ++ tailWord_3800292) baseStart_3800292 baseEnd_3800292 := by
    simpa [prefixWord, tailWord_3800292, baseEnd_3800292] using wordTrace_append hprefix tailTrace_3800292
  have hstable : (prefixWord ++ tailWord_3800292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800292).length < 2 ^ (prefixWord ++ tailWord_3800292).sum := by decide
  have hdescent : baseEnd_3800292 < baseStart_3800292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800329 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 2, 2, 3]
def baseStart_3800329 : Nat := 118140960795 + 3800329 * 2 ^ 59
def prefixEnd_3800329 : Nat := 4983230072969 + 3 ^ 40 * 3800329 * 2
def baseEnd_3800329 : Nat := 1951395422220566929010111

theorem tailTrace_3800329 : CollatzResearch.WordTrace tailWord_3800329 prefixEnd_3800329 1951395422220566929010111 := by
  unfold tailWord_3800329
  simp only [CollatzResearch.WordTrace]
  refine ⟨138609385849064552365236041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92406257232709701576824027 138609385849064552365236041)
  ·
    refine ⟨103957039386798414273927031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138609385849064552365236041 103957039386798414273927031)
    ·
      refine ⟨155935559080197621410890547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103957039386798414273927031 155935559080197621410890547)
      ·
        refine ⟨233903338620296432116335821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155935559080197621410890547 233903338620296432116335821)
        ·
          refine ⟨87713751982611162043625933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233903338620296432116335821 87713751982611162043625933)
          ·
            refine ⟨32892656993479185766359725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87713751982611162043625933 32892656993479185766359725)
            ·
              refine ⟨12334746372554694662384897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32892656993479185766359725 12334746372554694662384897)
              ·
                refine ⟨9251059779416020996788673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12334746372554694662384897 9251059779416020996788673)
                ·
                  refine ⟨6938294834562015747591505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9251059779416020996788673 6938294834562015747591505)
                  ·
                    refine ⟨5203721125921511810693629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6938294834562015747591505 5203721125921511810693629)
                    ·
                      refine ⟨1951395422220566929010111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5203721125921511810693629 1951395422220566929010111)
                      ·
                        rfl

theorem cell23_3800329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 2, 3].length) (baseStart_3800329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800329 prefixEnd_3800329 := by exact prefixLift 3800329
  have htrace : WordTrace (prefixWord ++ tailWord_3800329) baseStart_3800329 baseEnd_3800329 := by
    simpa [prefixWord, tailWord_3800329, baseEnd_3800329] using wordTrace_append hprefix tailTrace_3800329
  have hstable : (prefixWord ++ tailWord_3800329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800329).length < 2 ^ (prefixWord ++ tailWord_3800329).sum := by decide
  have hdescent : baseEnd_3800329 < baseStart_3800329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800332 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 8]
def baseStart_3800332 : Nat := 118140960795 + 3800332 * 2 ^ 59
def prefixEnd_3800332 : Nat := 4983230072969 + 3 ^ 40 * 3800332 * 2
def baseEnd_3800332 : Nat := 216821884740281157474733

theorem tailTrace_3800332 : CollatzResearch.WordTrace tailWord_3800332 prefixEnd_3800332 216821884740281157474733 := by
  unfold tailWord_3800332
  simp only [CollatzResearch.WordTrace]
  refine ⟨69304747634026841938797625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92406330178702455918396833 69304747634026841938797625)
  ·
    refine ⟨51978560725520131454098219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69304747634026841938797625 51978560725520131454098219)
    ·
      refine ⟨77967841088280197181147329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51978560725520131454098219 77967841088280197181147329)
      ·
        refine ⟨58475880816210147885860497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77967841088280197181147329 58475880816210147885860497)
        ·
          refine ⟨43856910612157610914395373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58475880816210147885860497 43856910612157610914395373)
          ·
            refine ⟨16446341479559104092898265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43856910612157610914395373 16446341479559104092898265)
            ·
              refine ⟨12334756109669328069673699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16446341479559104092898265 12334756109669328069673699)
              ·
                refine ⟨18502134164503992104510549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12334756109669328069673699 18502134164503992104510549)
                ·
                  refine ⟨216821884740281157474733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18502134164503992104510549 216821884740281157474733)
                  ·
                    rfl

theorem cell23_3800332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_3800332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800332 prefixEnd_3800332 := by exact prefixLift 3800332
  have htrace : WordTrace (prefixWord ++ tailWord_3800332) baseStart_3800332 baseEnd_3800332 := by
    simpa [prefixWord, tailWord_3800332, baseEnd_3800332] using wordTrace_append hprefix tailTrace_3800332
  have hstable : (prefixWord ++ tailWord_3800332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800332).length < 2 ^ (prefixWord ++ tailWord_3800332).sum := by decide
  have hdescent : baseEnd_3800332 < baseStart_3800332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800392 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 5, 6]
def baseStart_3800392 : Nat := 118140960795 + 3800392 * 2 ^ 59
def prefixEnd_3800392 : Nat := 4983230072969 + 3 ^ 40 * 3800392 * 2
def baseEnd_3800392 : Nat := 650475923833933394174107

theorem tailTrace_3800392 : CollatzResearch.WordTrace tailWord_3800392 prefixEnd_3800392 650475923833933394174107 := by
  unfold tailWord_3800392
  simp only [CollatzResearch.WordTrace]
  refine ⟨69305841823918157062389715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92407789098557542749852953 69305841823918157062389715)
  ·
    refine ⟨103958762735877235593584573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69305841823918157062389715 103958762735877235593584573)
    ·
      refine ⟨38984536025953963347594215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103958762735877235593584573 38984536025953963347594215)
      ·
        refine ⟨58476804038930945021391323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38984536025953963347594215 58476804038930945021391323)
        ·
          refine ⟨87715206058396417532086985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58476804038930945021391323 87715206058396417532086985)
          ·
            refine ⟨65786404543797313149065239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87715206058396417532086985 65786404543797313149065239)
            ·
              refine ⟨98679606815695969723597859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65786404543797313149065239 98679606815695969723597859)
              ·
                refine ⟨148019410223543954585396789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98679606815695969723597859 148019410223543954585396789)
                ·
                  refine ⟨13876819708457245742380949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148019410223543954585396789 13876819708457245742380949)
                  ·
                    refine ⟨650475923833933394174107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13876819708457245742380949 650475923833933394174107)
                    ·
                      rfl

theorem cell23_3800392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_3800392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800392 prefixEnd_3800392 := by exact prefixLift 3800392
  have htrace : WordTrace (prefixWord ++ tailWord_3800392) baseStart_3800392 baseEnd_3800392 := by
    simpa [prefixWord, tailWord_3800392, baseEnd_3800392] using wordTrace_append hprefix tailTrace_3800392
  have hstable : (prefixWord ++ tailWord_3800392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800392).length < 2 ^ (prefixWord ++ tailWord_3800392).sum := by decide
  have hdescent : baseEnd_3800392 < baseStart_3800392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800479 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3800479 : Nat := 118140960795 + 3800479 * 2 ^ 59
def prefixEnd_3800479 : Nat := 4983230072969 + 3 ^ 40 * 3800479 * 2
def baseEnd_3800479 : Nat := 1951472444318741342134421

theorem tailTrace_3800479 : CollatzResearch.WordTrace tailWord_3800479 prefixEnd_3800479 1951472444318741342134421 := by
  unfold tailWord_3800479
  simp only [CollatzResearch.WordTrace]
  refine ⟨138614856798521127983196491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92409904532347418655464327 138614856798521127983196491)
  ·
    refine ⟨207922285197781691974794737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138614856798521127983196491 207922285197781691974794737)
    ·
      refine ⟨155941713898336268981096053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207922285197781691974794737 155941713898336268981096053)
      ·
        refine ⟨14619535677969025216977755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155941713898336268981096053 14619535677969025216977755)
        ·
          refine ⟨21929303516953537825466633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14619535677969025216977755 21929303516953537825466633)
          ·
            refine ⟨16446977637715153369099975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21929303516953537825466633 16446977637715153369099975)
            ·
              refine ⟨24670466456572730053649963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16446977637715153369099975 24670466456572730053649963)
              ·
                refine ⟨37005699684859095080474945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24670466456572730053649963 37005699684859095080474945)
                ·
                  refine ⟨27754274763644321310356209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37005699684859095080474945 27754274763644321310356209)
                  ·
                    refine ⟨20815706072733240982767157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27754274763644321310356209 20815706072733240982767157)
                    ·
                      refine ⟨1951472444318741342134421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20815706072733240982767157 1951472444318741342134421)
                      ·
                        rfl

theorem cell23_3800479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3800479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800479 prefixEnd_3800479 := by exact prefixLift 3800479
  have htrace : WordTrace (prefixWord ++ tailWord_3800479) baseStart_3800479 baseEnd_3800479 := by
    simpa [prefixWord, tailWord_3800479, baseEnd_3800479] using wordTrace_append hprefix tailTrace_3800479
  have hstable : (prefixWord ++ tailWord_3800479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800479).length < 2 ^ (prefixWord ++ tailWord_3800479).sum := by decide
  have hdescent : baseEnd_3800479 < baseStart_3800479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800509 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3800509 : Nat := 118140960795 + 3800509 * 2 ^ 59
def prefixEnd_3800509 : Nat := 4983230072969 + 3 ^ 40 * 3800509 * 2
def baseEnd_3800509 : Nat := 1951487848738376224759283

theorem tailTrace_3800509 : CollatzResearch.WordTrace tailWord_3800509 prefixEnd_3800509 1951487848738376224759283 := by
  unfold tailWord_3800509
  simp only [CollatzResearch.WordTrace]
  refine ⟨138615950988412443106788581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92410633992274962071192387 138615950988412443106788581)
  ·
    refine ⟨25990490810327333082522859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138615950988412443106788581 25990490810327333082522859)
    ·
      refine ⟨38985736215490999623784289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25990490810327333082522859 38985736215490999623784289)
      ·
        refine ⟨29239302161618249717838217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38985736215490999623784289 29239302161618249717838217)
        ·
          refine ⟨21929476621213687288378663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29239302161618249717838217 21929476621213687288378663)
          ·
            refine ⟨32894214931820530932567995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21929476621213687288378663 32894214931820530932567995)
            ·
              refine ⟨49341322397730796398851993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32894214931820530932567995 49341322397730796398851993)
              ·
                refine ⟨37005991798298097299138995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49341322397730796398851993 37005991798298097299138995)
                ·
                  refine ⟨55508987697447145948708493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37005991798298097299138995 55508987697447145948708493)
                  ·
                    refine ⟨20815870386542679730765685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55508987697447145948708493 20815870386542679730765685)
                    ·
                      refine ⟨1951487848738376224759283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20815870386542679730765685 1951487848738376224759283)
                      ·
                        rfl

theorem cell23_3800509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3800509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800509 prefixEnd_3800509 := by exact prefixLift 3800509
  have htrace : WordTrace (prefixWord ++ tailWord_3800509) baseStart_3800509 baseEnd_3800509 := by
    simpa [prefixWord, tailWord_3800509, baseEnd_3800509] using wordTrace_append hprefix tailTrace_3800509
  have hstable : (prefixWord ++ tailWord_3800509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800509).length < 2 ^ (prefixWord ++ tailWord_3800509).sum := by decide
  have hdescent : baseEnd_3800509 < baseStart_3800509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800519 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_3800519 : Nat := 118140960795 + 3800519 * 2 ^ 59
def prefixEnd_3800519 : Nat := 4983230072969 + 3 ^ 40 * 3800519 * 2
def baseEnd_3800519 : Nat := 1951492983544921185634237

theorem tailTrace_3800519 : CollatzResearch.WordTrace tailWord_3800519 prefixEnd_3800519 1951492983544921185634237 := by
  unfold tailWord_3800519
  simp only [CollatzResearch.WordTrace]
  refine ⟨138616315718376214814652611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92410877145584143209768407 138616315718376214814652611)
  ·
    refine ⟨207924473577564322221978917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138616315718376214814652611 207924473577564322221978917)
    ·
      refine ⟨38985838795793310416621047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207924473577564322221978917 38985838795793310416621047)
      ·
        refine ⟨58478758193689965624931571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38985838795793310416621047 58478758193689965624931571)
        ·
          refine ⟨87718137290534948437397357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58478758193689965624931571 87718137290534948437397357)
          ·
            refine ⟨32894301483950605664024009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87718137290534948437397357 32894301483950605664024009)
            ·
              refine ⟨24670726112962954248018007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32894301483950605664024009 24670726112962954248018007)
              ·
                refine ⟨37006089169444431372027011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24670726112962954248018007 37006089169444431372027011)
                ·
                  refine ⟨55509133754166647058040517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37006089169444431372027011 55509133754166647058040517)
                  ·
                    refine ⟨10407962578906246323382597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55509133754166647058040517 10407962578906246323382597)
                    ·
                      refine ⟨1951492983544921185634237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10407962578906246323382597 1951492983544921185634237)
                      ·
                        rfl

theorem cell23_3800519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_3800519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800519 prefixEnd_3800519 := by exact prefixLift 3800519
  have htrace : WordTrace (prefixWord ++ tailWord_3800519) baseStart_3800519 baseEnd_3800519 := by
    simpa [prefixWord, tailWord_3800519, baseEnd_3800519] using wordTrace_append hprefix tailTrace_3800519
  have hstable : (prefixWord ++ tailWord_3800519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800519).length < 2 ^ (prefixWord ++ tailWord_3800519).sum := by decide
  have hdescent : baseEnd_3800519 < baseStart_3800519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800649 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 2, 9]
def baseStart_3800649 : Nat := 118140960795 + 3800649 * 2 ^ 59
def prefixEnd_3800649 : Nat := 4983230072969 + 3 ^ 40 * 3800649 * 2
def baseEnd_3800649 : Nat := 650519912010001892336213

theorem tailTrace_3800649 : CollatzResearch.WordTrace tailWord_3800649 prefixEnd_3800649 650519912010001892336213 := by
  unfold tailWord_3800649
  simp only [CollatzResearch.WordTrace]
  refine ⟨138621057207905247016885001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92414038138603498011256667 138621057207905247016885001)
  ·
    refine ⟨103965792905928935262663751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138621057207905247016885001 103965792905928935262663751)
    ·
      refine ⟨155948689358893402893995627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103965792905928935262663751 155948689358893402893995627)
      ·
        refine ⟨233923034038340104340993441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155948689358893402893995627 233923034038340104340993441)
        ·
          refine ⟨175442275528755078255745081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233923034038340104340993441 175442275528755078255745081)
          ·
            refine ⟨131581706646566308691808811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175442275528755078255745081 131581706646566308691808811)
            ·
              refine ⟨197372559969849463037713217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131581706646566308691808811 197372559969849463037713217)
              ·
                refine ⟨148029419977387097278284913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197372559969849463037713217 148029419977387097278284913)
                ·
                  refine ⟨111022064983040322958713685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148029419977387097278284913 111022064983040322958713685)
                  ·
                    refine ⟨650519912010001892336213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 111022064983040322958713685 650519912010001892336213)
                    ·
                      rfl

theorem cell23_3800649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_3800649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800649 prefixEnd_3800649 := by exact prefixLift 3800649
  have htrace : WordTrace (prefixWord ++ tailWord_3800649) baseStart_3800649 baseEnd_3800649 := by
    simpa [prefixWord, tailWord_3800649, baseEnd_3800649] using wordTrace_append hprefix tailTrace_3800649
  have hstable : (prefixWord ++ tailWord_3800649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800649).length < 2 ^ (prefixWord ++ tailWord_3800649).sum := by decide
  have hdescent : baseEnd_3800649 < baseStart_3800649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800659 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 7]
def baseStart_3800659 : Nat := 118140960795 + 3800659 * 2 ^ 59
def prefixEnd_3800659 : Nat := 4983230072969 + 3 ^ 40 * 3800659 * 2
def baseEnd_3800659 : Nat := 1951564870836550637883593

theorem tailTrace_3800659 : CollatzResearch.WordTrace tailWord_3800659 prefixEnd_3800659 1951564870836550637883593 := by
  unfold tailWord_3800659
  simp only [CollatzResearch.WordTrace]
  refine ⟨138621421937869018724749031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92414281291912679149832687 138621421937869018724749031)
  ·
    refine ⟨207932132906803528087123547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138621421937869018724749031 207932132906803528087123547)
    ·
      refine ⟨311898199360205292130685321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207932132906803528087123547 311898199360205292130685321)
      ·
        refine ⟨233923649520153969098013991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311898199360205292130685321 233923649520153969098013991)
        ·
          refine ⟨350885474280230953647020987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233923649520153969098013991 350885474280230953647020987)
          ·
            refine ⟨526328211420346430470531481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350885474280230953647020987 526328211420346430470531481)
            ·
              refine ⟨394746158565259822852898611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526328211420346430470531481 394746158565259822852898611)
              ·
                refine ⟨592119237847889734279347917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394746158565259822852898611 592119237847889734279347917)
                ·
                  refine ⟨222044714192958650354755469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592119237847889734279347917 222044714192958650354755469)
                  ·
                    refine ⟨83266767822359493883033301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 222044714192958650354755469 83266767822359493883033301)
                    ·
                      refine ⟨1951564870836550637883593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83266767822359493883033301 1951564870836550637883593)
                      ·
                        rfl

theorem cell23_3800659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_3800659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800659 prefixEnd_3800659 := by exact prefixLift 3800659
  have htrace : WordTrace (prefixWord ++ tailWord_3800659) baseStart_3800659 baseEnd_3800659 := by
    simpa [prefixWord, tailWord_3800659, baseEnd_3800659] using wordTrace_append hprefix tailTrace_3800659
  have hstable : (prefixWord ++ tailWord_3800659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800659).length < 2 ^ (prefixWord ++ tailWord_3800659).sum := by decide
  have hdescent : baseEnd_3800659 < baseStart_3800659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800816 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 9]
def baseStart_3800816 : Nat := 118140960795 + 3800816 * 2 ^ 59
def prefixEnd_3800816 : Nat := 4983230072969 + 3 ^ 40 * 3800816 * 2
def baseEnd_3800816 : Nat := 216849498588811835957819

theorem tailTrace_3800816 : CollatzResearch.WordTrace tailWord_3800816 prefixEnd_3800816 216849498588811835957819 := by
  unfold tailWord_3800816
  simp only [CollatzResearch.WordTrace]
  refine ⟨69313574099150117269107151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92418098798866823025476201 69313574099150117269107151)
  ·
    refine ⟨103970361148725175903660727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69313574099150117269107151 103970361148725175903660727)
    ·
      refine ⟨155955541723087763855491091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103970361148725175903660727 155955541723087763855491091)
      ·
        refine ⟨233933312584631645783236637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155955541723087763855491091 233933312584631645783236637)
        ·
          refine ⟨87724992219236867168713739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233933312584631645783236637 87724992219236867168713739)
          ·
            refine ⟨131587488328855300753070609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87724992219236867168713739 131587488328855300753070609)
            ·
              refine ⟨98690616246641475564802957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131587488328855300753070609 98690616246641475564802957)
              ·
                refine ⟨37008981092490553336801109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98690616246641475564802957 37008981092490553336801109)
                ·
                  refine ⟨216849498588811835957819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37008981092490553336801109 216849498588811835957819)
                  ·
                    rfl

theorem cell23_3800816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 9].length) (baseStart_3800816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800816 prefixEnd_3800816 := by exact prefixLift 3800816
  have htrace : WordTrace (prefixWord ++ tailWord_3800816) baseStart_3800816 baseEnd_3800816 := by
    simpa [prefixWord, tailWord_3800816, baseEnd_3800816] using wordTrace_append hprefix tailTrace_3800816
  have hstable : (prefixWord ++ tailWord_3800816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800816).length < 2 ^ (prefixWord ++ tailWord_3800816).sum := by decide
  have hdescent : baseEnd_3800816 < baseStart_3800816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800843 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 3]
def baseStart_3800843 : Nat := 118140960795 + 3800843 * 2 ^ 59
def prefixEnd_3800843 : Nat := 4983230072969 + 3 ^ 40 * 3800843 * 2
def baseEnd_3800843 : Nat := 1951659351276977917982747

theorem tailTrace_3800843 : CollatzResearch.WordTrace tailWord_3800843 prefixEnd_3800843 1951659351276977917982747 := by
  unfold tailWord_3800843
  simp only [CollatzResearch.WordTrace]
  refine ⟨138628132969202418149447183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92418755312801612099631455 138628132969202418149447183)
  ·
    refine ⟨207942199453803627224170775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138628132969202418149447183 207942199453803627224170775)
    ·
      refine ⟨311913299180705440836256163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207942199453803627224170775 311913299180705440836256163)
      ·
        refine ⟨467869948771058161254384245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311913299180705440836256163 467869948771058161254384245)
        ·
          refine ⟨43862807697286702617598523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 467869948771058161254384245 43862807697286702617598523)
          ·
            refine ⟨65794211545930053926397785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43862807697286702617598523 65794211545930053926397785)
            ·
              refine ⟨49345658659447540444798339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65794211545930053926397785 49345658659447540444798339)
              ·
                refine ⟨74018487989171310667197509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49345658659447540444798339 74018487989171310667197509)
                ·
                  refine ⟨13878466497969620750099533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74018487989171310667197509 13878466497969620750099533)
                  ·
                    refine ⟨5204424936738607781287325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13878466497969620750099533 5204424936738607781287325)
                    ·
                      refine ⟨1951659351276977917982747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5204424936738607781287325 1951659351276977917982747)
                      ·
                        rfl

theorem cell23_3800843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 3].length) (baseStart_3800843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800843 prefixEnd_3800843 := by exact prefixLift 3800843
  have htrace : WordTrace (prefixWord ++ tailWord_3800843) baseStart_3800843 baseEnd_3800843 := by
    simpa [prefixWord, tailWord_3800843, baseEnd_3800843] using wordTrace_append hprefix tailTrace_3800843
  have hstable : (prefixWord ++ tailWord_3800843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800843).length < 2 ^ (prefixWord ++ tailWord_3800843).sum := by decide
  have hdescent : baseEnd_3800843 < baseStart_3800843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800863 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 4, 5]
def baseStart_3800863 : Nat := 118140960795 + 3800863 * 2 ^ 59
def prefixEnd_3800863 : Nat := 4983230072969 + 3 ^ 40 * 3800863 * 2
def baseEnd_3800863 : Nat := 650556540296689279910885

theorem tailTrace_3800863 : CollatzResearch.WordTrace tailWord_3800863 prefixEnd_3800863 650556540296689279910885 := by
  unfold tailWord_3800863
  simp only [CollatzResearch.WordTrace]
  refine ⟨138628862429129961565175243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92419241619419974376783495 138628862429129961565175243)
  ·
    refine ⟨207943293643694942347762865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138628862429129961565175243 207943293643694942347762865)
    ·
      refine ⟨155957470232771206760822149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207943293643694942347762865 155957470232771206760822149)
      ·
        refine ⟨29242025668644601267654153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155957470232771206760822149 29242025668644601267654153)
        ·
          refine ⟨21931519251483450950740615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29242025668644601267654153 21931519251483450950740615)
          ·
            refine ⟨32897278877225176426110923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21931519251483450950740615 32897278877225176426110923)
            ·
              refine ⟨49345918315837764639166385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32897278877225176426110923 49345918315837764639166385)
              ·
                refine ⟨37009438736878323479374789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49345918315837764639166385 37009438736878323479374789)
                ·
                  refine ⟨6939269763164685652382773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37009438736878323479374789 6939269763164685652382773)
                  ·
                    refine ⟨650556540296689279910885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6939269763164685652382773 650556540296689279910885)
                    ·
                      rfl

theorem cell23_3800863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 5].length) (baseStart_3800863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800863 prefixEnd_3800863 := by exact prefixLift 3800863
  have htrace : WordTrace (prefixWord ++ tailWord_3800863) baseStart_3800863 baseEnd_3800863 := by
    simpa [prefixWord, tailWord_3800863, baseEnd_3800863] using wordTrace_append hprefix tailTrace_3800863
  have hstable : (prefixWord ++ tailWord_3800863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800863).length < 2 ^ (prefixWord ++ tailWord_3800863).sum := by decide
  have hdescent : baseEnd_3800863 < baseStart_3800863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800917 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 2, 4, 2]
def baseStart_3800917 : Nat := 118140960795 + 3800917 * 2 ^ 59
def prefixEnd_3800917 : Nat := 4983230072969 + 3 ^ 40 * 3800917 * 2
def baseEnd_3800917 : Nat := 1951697348845410628457407

theorem tailTrace_3800917 : CollatzResearch.WordTrace tailWord_3800917 prefixEnd_3800917 1951697348845410628457407 := by
  unfold tailWord_3800917
  simp only [CollatzResearch.WordTrace]
  refine ⟨138630831970934328787641005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92420554647289552525094003 138630831970934328787641005)
  ·
    refine ⟨51986561989100373295365377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138630831970934328787641005 51986561989100373295365377)
    ·
      refine ⟨38989921491825279971524033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51986561989100373295365377 38989921491825279971524033)
      ·
        refine ⟨29242441118868959978643025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38989921491825279971524033 29242441118868959978643025)
        ·
          refine ⟨21931830839151719983982269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29242441118868959978643025 21931830839151719983982269)
          ·
            refine ⟨8224436564681894993993351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21931830839151719983982269 8224436564681894993993351)
            ·
              refine ⟨12336654847022842490990027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8224436564681894993993351 12336654847022842490990027)
              ·
                refine ⟨18504982270534263736485041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12336654847022842490990027 18504982270534263736485041)
                ·
                  refine ⟨13878736702900697802363781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18504982270534263736485041 13878736702900697802363781)
                  ·
                    refine ⟨2602263131793880837943209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13878736702900697802363781 2602263131793880837943209)
                    ·
                      refine ⟨1951697348845410628457407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2602263131793880837943209 1951697348845410628457407)
                      ·
                        rfl

theorem cell23_3800917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_3800917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3800917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3800917 prefixEnd_3800917 := by exact prefixLift 3800917
  have htrace : WordTrace (prefixWord ++ tailWord_3800917) baseStart_3800917 baseEnd_3800917 := by
    simpa [prefixWord, tailWord_3800917, baseEnd_3800917] using wordTrace_append hprefix tailTrace_3800917
  have hstable : (prefixWord ++ tailWord_3800917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800917).length < 2 ^ (prefixWord ++ tailWord_3800917).sum := by decide
  have hdescent : baseEnd_3800917 < baseStart_3800917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801003 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 6]
def baseStart_3801003 : Nat := 118140960795 + 3801003 * 2 ^ 59
def prefixEnd_3801003 : Nat := 4983230072969 + 3 ^ 40 * 3801003 * 2
def baseEnd_3801003 : Nat := 1951741508181697291982011

theorem tailTrace_3801003 : CollatzResearch.WordTrace tailWord_3801003 prefixEnd_3801003 1951741508181697291982011 := by
  unfold tailWord_3801003
  simp only [CollatzResearch.WordTrace]
  refine ⟨138633968648622765475271663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92422645765748510316847775 138633968648622765475271663)
  ·
    refine ⟨207950952972934148212907495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138633968648622765475271663 207950952972934148212907495)
    ·
      refine ⟨311926429459401222319361243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207950952972934148212907495 311926429459401222319361243)
      ·
        refine ⟨467889644189101833479041865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311926429459401222319361243 467889644189101833479041865)
        ·
          refine ⟨350917233141826375109281399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467889644189101833479041865 350917233141826375109281399)
          ·
            refine ⟨526375849712739562663922099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350917233141826375109281399 526375849712739562663922099)
            ·
              refine ⟨789563774569109343995883149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526375849712739562663922099 789563774569109343995883149)
              ·
                refine ⟨296086415463416003998456181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 789563774569109343995883149 296086415463416003998456181)
                ·
                  refine ⟨27758101449695250374855267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 296086415463416003998456181 27758101449695250374855267)
                  ·
                    refine ⟨41637152174542875562282901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27758101449695250374855267 41637152174542875562282901)
                    ·
                      refine ⟨1951741508181697291982011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41637152174542875562282901 1951741508181697291982011)
                      ·
                        rfl

theorem cell23_3801003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 6].length) (baseStart_3801003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801003 prefixEnd_3801003 := by exact prefixLift 3801003
  have htrace : WordTrace (prefixWord ++ tailWord_3801003) baseStart_3801003 baseEnd_3801003 := by
    simpa [prefixWord, tailWord_3801003, baseEnd_3801003] using wordTrace_append hprefix tailTrace_3801003
  have hstable : (prefixWord ++ tailWord_3801003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801003).length < 2 ^ (prefixWord ++ tailWord_3801003).sum := by decide
  have hdescent : baseEnd_3801003 < baseStart_3801003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801017 : List Nat := [1, 2, 1, 4, 2, 1, 2, 4, 2, 4]
def baseStart_3801017 : Nat := 118140960795 + 3801017 * 2 ^ 59
def prefixEnd_3801017 : Nat := 4983230072969 + 3 ^ 40 * 3801017 * 2
def baseEnd_3801017 : Nat := 650582898970286745735649

theorem tailTrace_3801017 : CollatzResearch.WordTrace tailWord_3801017 prefixEnd_3801017 650582898970286745735649 := by
  unfold tailWord_3801017
  simp only [CollatzResearch.WordTrace]
  refine ⟨138634479270572045866281305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92422986180381363910854203 138634479270572045866281305)
  ·
    refine ⟨103975859452929034399710979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138634479270572045866281305 103975859452929034399710979)
    ·
      refine ⟨155963789179393551599566469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103975859452929034399710979 155963789179393551599566469)
      ·
        refine ⟨29243210471136290924918713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155963789179393551599566469 29243210471136290924918713)
        ·
          refine ⟨21932407853352218193689035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29243210471136290924918713 21932407853352218193689035)
          ·
            refine ⟨32898611780028327290533553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21932407853352218193689035 32898611780028327290533553)
            ·
              refine ⟨24673958835021245467900165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32898611780028327290533553 24673958835021245467900165)
              ·
                refine ⟨4626367281566483525231281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24673958835021245467900165 4626367281566483525231281)
                ·
                  refine ⟨3469775461174862643923461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4626367281566483525231281 3469775461174862643923461)
                  ·
                    refine ⟨650582898970286745735649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3469775461174862643923461 650582898970286745735649)
                    ·
                      rfl

theorem cell23_3801017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 4].length) (baseStart_3801017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801017 prefixEnd_3801017 := by exact prefixLift 3801017
  have htrace : WordTrace (prefixWord ++ tailWord_3801017) baseStart_3801017 baseEnd_3801017 := by
    simpa [prefixWord, tailWord_3801017, baseEnd_3801017] using wordTrace_append hprefix tailTrace_3801017
  have hstable : (prefixWord ++ tailWord_3801017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801017).length < 2 ^ (prefixWord ++ tailWord_3801017).sum := by decide
  have hdescent : baseEnd_3801017 < baseStart_3801017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801034 : List Nat := [3, 1, 2, 1, 2, 1, 6, 1, 2, 4]
def baseStart_3801034 : Nat := 118140960795 + 3801034 * 2 ^ 59
def prefixEnd_3801034 : Nat := 4983230072969 + 3 ^ 40 * 3801034 * 2
def baseEnd_3801034 : Nat := 650585808693995556898123

theorem tailTrace_3801034 : CollatzResearch.WordTrace tailWord_3801034 prefixEnd_3801034 650585808693995556898123 := by
  unfold tailWord_3801034
  simp only [CollatzResearch.WordTrace]
  refine ⟨34658774827877614442412539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92423399541006971846433437 34658774827877614442412539)
  ·
    refine ⟨51988162241816421663618809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34658774827877614442412539 51988162241816421663618809)
    ·
      refine ⟨38991121681362316247714107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51988162241816421663618809 38991121681362316247714107)
      ·
        refine ⟨58486682522043474371571161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38991121681362316247714107 58486682522043474371571161)
        ·
          refine ⟨43865011891532605778678371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58486682522043474371571161 43865011891532605778678371)
          ·
            refine ⟨65797517837298908668017557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43865011891532605778678371 65797517837298908668017557)
            ·
              refine ⟨3084258648623386343813323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65797517837298908668017557 3084258648623386343813323)
              ·
                refine ⟨4626387972935079515719985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3084258648623386343813323 4626387972935079515719985)
                ·
                  refine ⟨3469790979701309636789989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4626387972935079515719985 3469790979701309636789989)
                  ·
                    refine ⟨650585808693995556898123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3469790979701309636789989 650585808693995556898123)
                    ·
                      rfl

theorem cell23_3801034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_3801034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801034 prefixEnd_3801034 := by exact prefixLift 3801034
  have htrace : WordTrace (prefixWord ++ tailWord_3801034) baseStart_3801034 baseEnd_3801034 := by
    simpa [prefixWord, tailWord_3801034, baseEnd_3801034] using wordTrace_append hprefix tailTrace_3801034
  have hstable : (prefixWord ++ tailWord_3801034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801034).length < 2 ^ (prefixWord ++ tailWord_3801034).sum := by decide
  have hdescent : baseEnd_3801034 < baseStart_3801034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801057 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_3801057 : Nat := 118140960795 + 3801057 * 2 ^ 59
def prefixEnd_3801057 : Nat := 4983230072969 + 3 ^ 40 * 3801057 * 2
def baseEnd_3801057 : Nat := 1951769236137040080706763

theorem tailTrace_3801057 : CollatzResearch.WordTrace tailWord_3801057 prefixEnd_3801057 1951769236137040080706763 := by
  unfold tailWord_3801057
  simp only [CollatzResearch.WordTrace]
  refine ⟨138635938190427132697737425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92423958793618088465158283 138635938190427132697737425)
  ·
    refine ⟨103976953642820349523303069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138635938190427132697737425 103976953642820349523303069)
    ·
      refine ⟨38991357616057631071238651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103976953642820349523303069 38991357616057631071238651)
      ·
        refine ⟨58487036424086446606857977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38991357616057631071238651 58487036424086446606857977)
        ·
          refine ⟨43865277318064834955143483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58487036424086446606857977 43865277318064834955143483)
          ·
            refine ⟨65797915977097252432715225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43865277318064834955143483 65797915977097252432715225)
            ·
              refine ⟨49348436982822939324536419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65797915977097252432715225 49348436982822939324536419)
              ·
                refine ⟨74022655474234408986804629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49348436982822939324536419 74022655474234408986804629)
                ·
                  refine ⟨3469811975354737921256467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74022655474234408986804629 3469811975354737921256467)
                  ·
                    refine ⟨5204717963032106881884701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3469811975354737921256467 5204717963032106881884701)
                    ·
                      refine ⟨1951769236137040080706763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5204717963032106881884701 1951769236137040080706763)
                      ·
                        rfl

theorem cell23_3801057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_3801057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801057 prefixEnd_3801057 := by exact prefixLift 3801057
  have htrace : WordTrace (prefixWord ++ tailWord_3801057) baseStart_3801057 baseEnd_3801057 := by
    simpa [prefixWord, tailWord_3801057, baseEnd_3801057] using wordTrace_append hprefix tailTrace_3801057
  have hstable : (prefixWord ++ tailWord_3801057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801057).length < 2 ^ (prefixWord ++ tailWord_3801057).sum := by decide
  have hdescent : baseEnd_3801057 < baseStart_3801057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801058 : List Nat := [3, 3, 3, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_3801058 : Nat := 118140960795 + 3801058 * 2 ^ 59
def prefixEnd_3801058 : Nat := 4983230072969 + 3 ^ 40 * 3801058 * 2
def baseEnd_3801058 : Nat := 1951769749617694576794259

theorem tailTrace_3801058 : CollatzResearch.WordTrace tailWord_3801058 prefixEnd_3801058 1951769749617694576794259 := by
  unfold tailWord_3801058
  simp only [CollatzResearch.WordTrace]
  refine ⟨34658993665855877467130957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92423983108949006579015885 34658993665855877467130957)
  ·
    refine ⟨12997122624695954050174109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34658993665855877467130957 12997122624695954050174109)
    ·
      refine ⟨4873920984260982768815291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12997122624695954050174109 4873920984260982768815291)
      ·
        refine ⟨7310881476391474153222937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4873920984260982768815291 7310881476391474153222937)
        ·
          refine ⟨5483161107293605614917203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7310881476391474153222937 5483161107293605614917203)
          ·
            refine ⟨8224741660940408422375805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5483161107293605614917203 8224741660940408422375805)
            ·
              refine ⟨3084278122852653158390927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8224741660940408422375805 3084278122852653158390927)
              ·
                refine ⟨4626417184278979737586391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3084278122852653158390927 4626417184278979737586391)
                ·
                  refine ⟨6939625776418469606379587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626417184278979737586391 6939625776418469606379587)
                  ·
                    refine ⟨10409438664627704409569381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6939625776418469606379587 10409438664627704409569381)
                    ·
                      refine ⟨1951769749617694576794259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10409438664627704409569381 1951769749617694576794259)
                      ·
                        rfl

theorem cell23_3801058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_3801058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801058 prefixEnd_3801058 := by exact prefixLift 3801058
  have htrace : WordTrace (prefixWord ++ tailWord_3801058) baseStart_3801058 baseEnd_3801058 := by
    simpa [prefixWord, tailWord_3801058, baseEnd_3801058] using wordTrace_append hprefix tailTrace_3801058
  have hstable : (prefixWord ++ tailWord_3801058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801058).length < 2 ^ (prefixWord ++ tailWord_3801058).sum := by decide
  have hdescent : baseEnd_3801058 < baseStart_3801058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801080 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_3801080 : Nat := 118140960795 + 3801080 * 2 ^ 59
def prefixEnd_3801080 : Nat := 4983230072969 + 3 ^ 40 * 3801080 * 2
def baseEnd_3801080 : Nat := 1951781046192093490719157

theorem tailTrace_3801080 : CollatzResearch.WordTrace tailWord_3801080 prefixEnd_3801080 1951781046192093490719157 := by
  unfold tailWord_3801080
  simp only [CollatzResearch.WordTrace]
  refine ⟨69318388534671903812912347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92424518046229205083883129 69318388534671903812912347)
  ·
    refine ⟨103977582802007855719368521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69318388534671903812912347 103977582802007855719368521)
    ·
      refine ⟨77983187101505891789526391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103977582802007855719368521 77983187101505891789526391)
      ·
        refine ⟨116974780652258837684289587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77983187101505891789526391 116974780652258837684289587)
        ·
          refine ⟨175462170978388256526434381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116974780652258837684289587 175462170978388256526434381)
          ·
            refine ⟨65798314116895596197412893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175462170978388256526434381 65798314116895596197412893)
            ·
              refine ⟨24674367793835848574029835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65798314116895596197412893 24674367793835848574029835)
              ·
                refine ⟨37011551690753772861044753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24674367793835848574029835 37011551690753772861044753)
                ·
                  refine ⟨27758663768065329645783565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37011551690753772861044753 27758663768065329645783565)
                  ·
                    refine ⟨10409498913024498617168837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27758663768065329645783565 10409498913024498617168837)
                    ·
                      refine ⟨1951781046192093490719157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10409498913024498617168837 1951781046192093490719157)
                      ·
                        rfl

theorem cell23_3801080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_3801080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801080 prefixEnd_3801080 := by exact prefixLift 3801080
  have htrace : WordTrace (prefixWord ++ tailWord_3801080) baseStart_3801080 baseEnd_3801080 := by
    simpa [prefixWord, tailWord_3801080, baseEnd_3801080] using wordTrace_append hprefix tailTrace_3801080
  have hstable : (prefixWord ++ tailWord_3801080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801080).length < 2 ^ (prefixWord ++ tailWord_3801080).sum := by decide
  have hdescent : baseEnd_3801080 < baseStart_3801080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801114 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2]
def baseStart_3801114 : Nat := 118140960795 + 3801114 * 2 ^ 59
def prefixEnd_3801114 : Nat := 4983230072969 + 3 ^ 40 * 3801114 * 2
def baseEnd_3801114 : Nat := 1951798504534346357694001

theorem tailTrace_3801114 : CollatzResearch.WordTrace tailWord_3801114 prefixEnd_3801114 1951798504534346357694001 := by
  unfold tailWord_3801114
  simp only [CollatzResearch.WordTrace]
  refine ⟨34659504287805157858140599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92425344767480420955041597 34659504287805157858140599)
  ·
    refine ⟨51989256431707736787210899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34659504287805157858140599 51989256431707736787210899)
    ·
      refine ⟨77983884647561605180816349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51989256431707736787210899 77983884647561605180816349)
      ·
        refine ⟨29243956742835601942806131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77983884647561605180816349 29243956742835601942806131)
        ·
          refine ⟨43865935114253402914209197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29243956742835601942806131 43865935114253402914209197)
          ·
            refine ⟨16449725667845026092828449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43865935114253402914209197 16449725667845026092828449)
            ·
              refine ⟨12337294250883769569621337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16449725667845026092828449 12337294250883769569621337)
              ·
                refine ⟨9252970688162827177216003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12337294250883769569621337 9252970688162827177216003)
                ·
                  refine ⟨13879456032244240765824005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9252970688162827177216003 13879456032244240765824005)
                  ·
                    refine ⟨2602398006045795143592001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13879456032244240765824005 2602398006045795143592001)
                    ·
                      refine ⟨1951798504534346357694001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2602398006045795143592001 1951798504534346357694001)
                      ·
                        rfl

theorem cell23_3801114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_3801114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801114 prefixEnd_3801114 := by exact prefixLift 3801114
  have htrace : WordTrace (prefixWord ++ tailWord_3801114) baseStart_3801114 baseEnd_3801114 := by
    simpa [prefixWord, tailWord_3801114, baseEnd_3801114] using wordTrace_append hprefix tailTrace_3801114
  have hstable : (prefixWord ++ tailWord_3801114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801114).length < 2 ^ (prefixWord ++ tailWord_3801114).sum := by decide
  have hdescent : baseEnd_3801114 < baseStart_3801114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801137 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 7]
def baseStart_3801137 : Nat := 118140960795 + 3801137 * 2 ^ 59
def prefixEnd_3801137 : Nat := 4983230072969 + 3 ^ 40 * 3801137 * 2
def baseEnd_3801137 : Nat := 216867812732155529745155

theorem tailTrace_3801137 : CollatzResearch.WordTrace tailWord_3801137 prefixEnd_3801137 216867812732155529745155 := by
  unfold tailWord_3801137
  simp only [CollatzResearch.WordTrace]
  refine ⟨138638856030137306360649665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92425904020091537573766443 138638856030137306360649665)
  ·
    refine ⟨103979142022602979770487249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138638856030137306360649665 103979142022602979770487249)
    ·
      refine ⟨77984356516952234827865437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103979142022602979770487249 77984356516952234827865437)
      ·
        refine ⟨29244133693857088060449539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77984356516952234827865437 29244133693857088060449539)
        ·
          refine ⟨43866200540785632090674309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29244133693857088060449539 43866200540785632090674309)
          ·
            refine ⟨8224912601397306017001433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43866200540785632090674309 8224912601397306017001433)
            ·
              refine ⟨6168684451047979512751075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8224912601397306017001433 6168684451047979512751075)
              ·
                refine ⟨9253026676571969269126613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6168684451047979512751075 9253026676571969269126613)
                ·
                  refine ⟨216867812732155529745155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9253026676571969269126613 216867812732155529745155)
                  ·
                    rfl

theorem cell23_3801137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 7].length) (baseStart_3801137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801137 prefixEnd_3801137 := by exact prefixLift 3801137
  have htrace : WordTrace (prefixWord ++ tailWord_3801137) baseStart_3801137 baseEnd_3801137 := by
    simpa [prefixWord, tailWord_3801137, baseEnd_3801137] using wordTrace_append hprefix tailTrace_3801137
  have hstable : (prefixWord ++ tailWord_3801137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801137).length < 2 ^ (prefixWord ++ tailWord_3801137).sum := by decide
  have hdescent : baseEnd_3801137 < baseStart_3801137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801148 : List Nat := [2, 2, 2, 2, 2, 1, 5, 1, 2, 2, 2]
def baseStart_3801148 : Nat := 118140960795 + 3801148 * 2 ^ 59
def prefixEnd_3801148 : Nat := 4983230072969 + 3 ^ 40 * 3801148 * 2
def baseEnd_3801148 : Nat := 1951815962876599224668845

theorem tailTrace_3801148 : CollatzResearch.WordTrace tailWord_3801148 prefixEnd_3801148 1951815962876599224668845 := by
  unfold tailWord_3801148
  simp only [CollatzResearch.WordTrace]
  refine ⟨69319628616548727619650049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92426171488731636826200065 69319628616548727619650049)
  ·
    refine ⟨51989721462411545714737537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69319628616548727619650049 51989721462411545714737537)
    ·
      refine ⟨38992291096808659286053153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51989721462411545714737537 38992291096808659286053153)
      ·
        refine ⟨29244218322606494464539865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38992291096808659286053153 29244218322606494464539865)
        ·
          refine ⟨21933163741954870848404899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29244218322606494464539865 21933163741954870848404899)
          ·
            refine ⟨32899745612932306272607349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21933163741954870848404899 32899745612932306272607349)
            ·
              refine ⟨3084351151212403713056939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32899745612932306272607349 3084351151212403713056939)
              ·
                refine ⟨4626526726818605569585409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3084351151212403713056939 4626526726818605569585409)
                ·
                  refine ⟨3469895045113954177189057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4626526726818605569585409 3469895045113954177189057)
                  ·
                    refine ⟨2602421283835465632891793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3469895045113954177189057 2602421283835465632891793)
                    ·
                      refine ⟨1951815962876599224668845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2602421283835465632891793 1951815962876599224668845)
                      ·
                        rfl

theorem cell23_3801148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_3801148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801148 prefixEnd_3801148 := by exact prefixLift 3801148
  have htrace : WordTrace (prefixWord ++ tailWord_3801148) baseStart_3801148 baseEnd_3801148 := by
    simpa [prefixWord, tailWord_3801148, baseEnd_3801148] using wordTrace_append hprefix tailTrace_3801148
  have hstable : (prefixWord ++ tailWord_3801148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801148).length < 2 ^ (prefixWord ++ tailWord_3801148).sum := by decide
  have hdescent : baseEnd_3801148 < baseStart_3801148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801160 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_3801160 : Nat := 118140960795 + 3801160 * 2 ^ 59
def prefixEnd_3801160 : Nat := 4983230072969 + 3 ^ 40 * 3801160 * 2
def baseEnd_3801160 : Nat := 1951822124644453177718789

theorem tailTrace_3801160 : CollatzResearch.WordTrace tailWord_3801160 prefixEnd_3801160 1951822124644453177718789 := by
  unfold tailWord_3801160
  simp only [CollatzResearch.WordTrace]
  refine ⟨69319847454526990644368467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92426463272702654192491289 69319847454526990644368467)
  ·
    refine ⟨103979771181790485966552701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69319847454526990644368467 103979771181790485966552701)
    ·
      refine ⟨38992414193171432237457263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103979771181790485966552701 38992414193171432237457263)
      ·
        refine ⟨58488621289757148356185895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38992414193171432237457263 58488621289757148356185895)
        ·
          refine ⟨87732931934635722534278843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58488621289757148356185895 87732931934635722534278843)
          ·
            refine ⟨131599397901953583801418265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87732931934635722534278843 131599397901953583801418265)
            ·
              refine ⟨98699548426465187851063699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131599397901953583801418265 98699548426465187851063699)
              ·
                refine ⟨148049322639697781776595549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98699548426465187851063699 148049322639697781776595549)
                ·
                  refine ⟨55518495989886668166223331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148049322639697781776595549 55518495989886668166223331)
                  ·
                    refine ⟨83277743984830002249334997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55518495989886668166223331 83277743984830002249334997)
                    ·
                      refine ⟨1951822124644453177718789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83277743984830002249334997 1951822124644453177718789)
                      ·
                        rfl

theorem cell23_3801160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_3801160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801160 prefixEnd_3801160 := by exact prefixLift 3801160
  have htrace : WordTrace (prefixWord ++ tailWord_3801160) baseStart_3801160 baseEnd_3801160 := by
    simpa [prefixWord, tailWord_3801160, baseEnd_3801160] using wordTrace_append hprefix tailTrace_3801160
  have hstable : (prefixWord ++ tailWord_3801160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801160).length < 2 ^ (prefixWord ++ tailWord_3801160).sum := by decide
  have hdescent : baseEnd_3801160 < baseStart_3801160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801187 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 4]
def baseStart_3801187 : Nat := 118140960795 + 3801187 * 2 ^ 59
def prefixEnd_3801187 : Nat := 4983230072969 + 3 ^ 40 * 3801187 * 2
def baseEnd_3801187 : Nat := 1951835988622124572081165

theorem tailTrace_3801187 : CollatzResearch.WordTrace tailWord_3801187 prefixEnd_3801187 1951835988622124572081165 := by
  unfold tailWord_3801187
  simp only [CollatzResearch.WordTrace]
  refine ⟨138640679679956164899969815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92427119786637443266646543 138640679679956164899969815)
  ·
    refine ⟨207961019519934247349954723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138640679679956164899969815 207961019519934247349954723)
    ·
      refine ⟨311941529279901371024932085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207961019519934247349954723 311941529279901371024932085)
      ·
        refine ⟨29244518369990753533587383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311941529279901371024932085 29244518369990753533587383)
        ·
          refine ⟨43866777554986130300381075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29244518369990753533587383 43866777554986130300381075)
          ·
            refine ⟨65800166332479195450571613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43866777554986130300381075 65800166332479195450571613)
            ·
              refine ⟨24675062374679698293964355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65800166332479195450571613 24675062374679698293964355)
              ·
                refine ⟨37012593562019547440946533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24675062374679698293964355 37012593562019547440946533)
                ·
                  refine ⟨6939861292878665145177475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37012593562019547440946533 6939861292878665145177475)
                  ·
                    refine ⟨10409791939317997717766213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6939861292878665145177475 10409791939317997717766213)
                    ·
                      refine ⟨1951835988622124572081165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10409791939317997717766213 1951835988622124572081165)
                      ·
                        rfl

theorem cell23_3801187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_3801187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801187 prefixEnd_3801187 := by exact prefixLift 3801187
  have htrace : WordTrace (prefixWord ++ tailWord_3801187) baseStart_3801187 baseEnd_3801187 := by
    simpa [prefixWord, tailWord_3801187, baseEnd_3801187] using wordTrace_append hprefix tailTrace_3801187
  have hstable : (prefixWord ++ tailWord_3801187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801187).length < 2 ^ (prefixWord ++ tailWord_3801187).sum := by decide
  have hdescent : baseEnd_3801187 < baseStart_3801187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801194 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_3801194 : Nat := 118140960795 + 3801194 * 2 ^ 59
def prefixEnd_3801194 : Nat := 4983230072969 + 3 ^ 40 * 3801194 * 2
def baseEnd_3801194 : Nat := 1951839582986706044693633

theorem tailTrace_3801194 : CollatzResearch.WordTrace tailWord_3801194 prefixEnd_3801194 1951839582986706044693633 := by
  unfold tailWord_3801194
  simp only [CollatzResearch.WordTrace]
  refine ⟨34660233747732701273868659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92427289993953870063649757 34660233747732701273868659)
  ·
    refine ⟨51990350621599051910802989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34660233747732701273868659 51990350621599051910802989)
    ·
      refine ⟨19496381483099644466551121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51990350621599051910802989 19496381483099644466551121)
      ·
        refine ⟨14622286112324733349913341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19496381483099644466551121 14622286112324733349913341)
        ·
          refine ⟨5483357292121775006217503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14622286112324733349913341 5483357292121775006217503)
          ·
            refine ⟨8225035938182662509326255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5483357292121775006217503 8225035938182662509326255)
            ·
              refine ⟨12337553907273993763989383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8225035938182662509326255 12337553907273993763989383)
              ·
                refine ⟨18506330860910990645984075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12337553907273993763989383 18506330860910990645984075)
                ·
                  refine ⟨27759496291366485968976113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18506330860910990645984075 27759496291366485968976113)
                  ·
                    refine ⟨20819622218524864476732085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27759496291366485968976113 20819622218524864476732085)
                    ·
                      refine ⟨1951839582986706044693633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20819622218524864476732085 1951839582986706044693633)
                      ·
                        rfl

theorem cell23_3801194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_3801194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801194 prefixEnd_3801194 := by exact prefixLift 3801194
  have htrace : WordTrace (prefixWord ++ tailWord_3801194) baseStart_3801194 baseEnd_3801194 := by
    simpa [prefixWord, tailWord_3801194, baseEnd_3801194] using wordTrace_append hprefix tailTrace_3801194
  have hstable : (prefixWord ++ tailWord_3801194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801194).length < 2 ^ (prefixWord ++ tailWord_3801194).sum := by decide
  have hdescent : baseEnd_3801194 < baseStart_3801194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801244 : List Nat := [2, 2, 3, 2, 1, 1, 4, 2, 6]
def baseStart_3801244 : Nat := 118140960795 + 3801244 * 2 ^ 59
def prefixEnd_3801244 : Nat := 4983230072969 + 3 ^ 40 * 3801244 * 2
def baseEnd_3801244 : Nat := 216873917446603427674267

theorem tailTrace_3801244 : CollatzResearch.WordTrace tailWord_3801244 prefixEnd_3801244 216873917446603427674267 := by
  unfold tailWord_3801244
  simp only [CollatzResearch.WordTrace]
  refine ⟨69321379320374831817397393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92428505760499775756529857 69321379320374831817397393)
  ·
    refine ⟨51991034490281123863048045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69321379320374831817397393 51991034490281123863048045)
    ·
      refine ⟨19496637933855421448643017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51991034490281123863048045 19496637933855421448643017)
      ·
        refine ⟨14622478450391566086482263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19496637933855421448643017 14622478450391566086482263)
        ·
          refine ⟨21933717675587349129723395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14622478450391566086482263 21933717675587349129723395)
          ·
            refine ⟨32900576513381023694585093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21933717675587349129723395 32900576513381023694585093)
            ·
              refine ⟨6168858096258941942734705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32900576513381023694585093 6168858096258941942734705)
              ·
                refine ⟨4626643572194206457051029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6168858096258941942734705 4626643572194206457051029)
                ·
                  refine ⟨216873917446603427674267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4626643572194206457051029 216873917446603427674267)
                  ·
                    rfl

theorem cell23_3801244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_3801244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801244 prefixEnd_3801244 := by exact prefixLift 3801244
  have htrace : WordTrace (prefixWord ++ tailWord_3801244) baseStart_3801244 baseEnd_3801244 := by
    simpa [prefixWord, tailWord_3801244, baseEnd_3801244] using wordTrace_append hprefix tailTrace_3801244
  have hstable : (prefixWord ++ tailWord_3801244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801244).length < 2 ^ (prefixWord ++ tailWord_3801244).sum := by decide
  have hdescent : baseEnd_3801244 < baseStart_3801244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801248 : List Nat := [2, 1, 1, 4, 2, 2, 4, 2, 1, 4]
def baseStart_3801248 : Nat := 118140960795 + 3801248 * 2 ^ 59
def prefixEnd_3801248 : Nat := 4983230072969 + 3 ^ 40 * 3801248 * 2
def baseEnd_3801248 : Nat := 650622436980682944472795

theorem tailTrace_3801248 : CollatzResearch.WordTrace tailWord_3801248 prefixEnd_3801248 650622436980682944472795 := by
  unfold tailWord_3801248
  simp only [CollatzResearch.WordTrace]
  refine ⟨69321452266367586158970199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92428603021823448211960265 69321452266367586158970199)
  ·
    refine ⟨103982178399551379238455299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69321452266367586158970199 103982178399551379238455299)
    ·
      refine ⟨155973267599327068857682949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103982178399551379238455299 155973267599327068857682949)
      ·
        refine ⟨29244987674873825410815553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155973267599327068857682949 29244987674873825410815553)
        ·
          refine ⟨21933740756155369058111665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29244987674873825410815553 21933740756155369058111665)
          ·
            refine ⟨16450305567116526793583749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21933740756155369058111665 16450305567116526793583749)
            ·
              refine ⟨3084432293834348773796953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16450305567116526793583749 3084432293834348773796953)
              ·
                refine ⟨2313324220375761580347715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3084432293834348773796953 2313324220375761580347715)
                ·
                  refine ⟨3469986330563642370521573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2313324220375761580347715 3469986330563642370521573)
                  ·
                    refine ⟨650622436980682944472795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3469986330563642370521573 650622436980682944472795)
                    ·
                      rfl

theorem cell23_3801248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 1, 4].length) (baseStart_3801248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801248 prefixEnd_3801248 := by exact prefixLift 3801248
  have htrace : WordTrace (prefixWord ++ tailWord_3801248) baseStart_3801248 baseEnd_3801248 := by
    simpa [prefixWord, tailWord_3801248, baseEnd_3801248] using wordTrace_append hprefix tailTrace_3801248
  have hstable : (prefixWord ++ tailWord_3801248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801248).length < 2 ^ (prefixWord ++ tailWord_3801248).sum := by decide
  have hdescent : baseEnd_3801248 < baseStart_3801248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801271 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 3, 1, 3]
def baseStart_3801271 : Nat := 118140960795 + 3801271 * 2 ^ 59
def prefixEnd_3801271 : Nat := 4983230072969 + 3 ^ 40 * 3801271 * 2
def baseEnd_3801271 : Nat := 1951879120997102243430779

theorem tailTrace_3801271 : CollatzResearch.WordTrace tailWord_3801271 prefixEnd_3801271 1951879120997102243430779 := by
  unfold tailWord_3801271
  simp only [CollatzResearch.WordTrace]
  refine ⟨138643743411651847246027667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92429162274434564830685111 138643743411651847246027667)
  ·
    refine ⟨207965615117477770869041501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138643743411651847246027667 207965615117477770869041501)
    ·
      refine ⟨77987105669054164075890563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207965615117477770869041501 77987105669054164075890563)
      ·
        refine ⟨116980658503581246113835845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77987105669054164075890563 116980658503581246113835845)
        ·
          refine ⟨21933873469421483646344221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116980658503581246113835845 21933873469421483646344221)
          ·
            refine ⟨8225202551033056367379083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21933873469421483646344221 8225202551033056367379083)
            ·
              refine ⟨12337803826549584551068625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8225202551033056367379083 12337803826549584551068625)
              ·
                refine ⟨9253352869912188413301469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12337803826549584551068625 9253352869912188413301469)
                ·
                  refine ⟨3470007326217070654988051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9253352869912188413301469 3470007326217070654988051)
                  ·
                    refine ⟨5205010989325605982482077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3470007326217070654988051 5205010989325605982482077)
                    ·
                      refine ⟨1951879120997102243430779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5205010989325605982482077 1951879120997102243430779)
                      ·
                        rfl

theorem cell23_3801271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_3801271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801271 prefixEnd_3801271 := by exact prefixLift 3801271
  have htrace : WordTrace (prefixWord ++ tailWord_3801271) baseStart_3801271 baseEnd_3801271 := by
    simpa [prefixWord, tailWord_3801271, baseEnd_3801271] using wordTrace_append hprefix tailTrace_3801271
  have hstable : (prefixWord ++ tailWord_3801271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801271).length < 2 ^ (prefixWord ++ tailWord_3801271).sum := by decide
  have hdescent : baseEnd_3801271 < baseStart_3801271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801282 : List Nat := [3, 5, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_3801282 : Nat := 118140960795 + 3801282 * 2 ^ 59
def prefixEnd_3801282 : Nat := 4983230072969 + 3 ^ 40 * 3801282 * 2
def baseEnd_3801282 : Nat := 650628256428100566797743

theorem tailTrace_3801282 : CollatzResearch.WordTrace tailWord_3801282 prefixEnd_3801282 650628256428100566797743 := by
  unfold tailWord_3801282
  simp only [CollatzResearch.WordTrace]
  refine ⟨34661036153652999031169525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92429429743074664083118733 34661036153652999031169525)
  ·
    refine ⟨3249472139404968659172143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34661036153652999031169525 3249472139404968659172143)
    ·
      refine ⟨4874208209107452988758215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3249472139404968659172143 4874208209107452988758215)
      ·
        refine ⟨7311312313661179483137323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4874208209107452988758215 7311312313661179483137323)
        ·
          refine ⟨10966968470491769224705985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7311312313661179483137323 10966968470491769224705985)
          ·
            refine ⟨8225226352868826918529489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10966968470491769224705985 8225226352868826918529489)
            ·
              refine ⟨6168919764651620188897117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8225226352868826918529489 6168919764651620188897117)
              ·
                refine ⟨2313344911744357570836419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6168919764651620188897117 2313344911744357570836419)
                ·
                  refine ⟨3470017367616536356254629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2313344911744357570836419 3470017367616536356254629)
                  ·
                    refine ⟨650628256428100566797743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3470017367616536356254629 650628256428100566797743)
                    ·
                      rfl

theorem cell23_3801282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_3801282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801282 prefixEnd_3801282 := by exact prefixLift 3801282
  have htrace : WordTrace (prefixWord ++ tailWord_3801282) baseStart_3801282 baseEnd_3801282 := by
    simpa [prefixWord, tailWord_3801282, baseEnd_3801282] using wordTrace_append hprefix tailTrace_3801282
  have hstable : (prefixWord ++ tailWord_3801282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801282).length < 2 ^ (prefixWord ++ tailWord_3801282).sum := by decide
  have hdescent : baseEnd_3801282 < baseStart_3801282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801307 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 4]
def baseStart_3801307 : Nat := 118140960795 + 3801307 * 2 ^ 59
def prefixEnd_3801307 : Nat := 4983230072969 + 3 ^ 40 * 3801307 * 2
def baseEnd_3801307 : Nat := 1951897606300664102580613

theorem tailTrace_3801307 : CollatzResearch.WordTrace tailWord_3801307 prefixEnd_3801307 1951897606300664102580613 := by
  unfold tailWord_3801307
  simp only [CollatzResearch.WordTrace]
  refine ⟨138645056439521425394338175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92430037626347616929558783 138645056439521425394338175)
  ·
    refine ⟨207967584659282138091507263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138645056439521425394338175 207967584659282138091507263)
    ·
      refine ⟨311951376988923207137260895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207967584659282138091507263 311951376988923207137260895)
      ·
        refine ⟨467927065483384810705891343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311951376988923207137260895 467927065483384810705891343)
        ·
          refine ⟨701890598225077216058837015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467927065483384810705891343 701890598225077216058837015)
          ·
            refine ⟨1052835897337615824088255523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701890598225077216058837015 1052835897337615824088255523)
            ·
              refine ⟨1579253846006423736132383285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052835897337615824088255523 1579253846006423736132383285)
              ·
                refine ⟨148055048063102225262410933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1579253846006423736132383285 148055048063102225262410933)
                ·
                  refine ⟨13880160755915833618351025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148055048063102225262410933 13880160755915833618351025)
                  ·
                    refine ⟨10410120566936875213763269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13880160755915833618351025 10410120566936875213763269)
                    ·
                      refine ⟨1951897606300664102580613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10410120566936875213763269 1951897606300664102580613)
                      ·
                        rfl

theorem cell23_3801307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 4].length) (baseStart_3801307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801307 prefixEnd_3801307 := by exact prefixLift 3801307
  have htrace : WordTrace (prefixWord ++ tailWord_3801307) baseStart_3801307 baseEnd_3801307 := by
    simpa [prefixWord, tailWord_3801307, baseEnd_3801307] using wordTrace_append hprefix tailTrace_3801307
  have hstable : (prefixWord ++ tailWord_3801307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801307).length < 2 ^ (prefixWord ++ tailWord_3801307).sum := by decide
  have hdescent : baseEnd_3801307 < baseStart_3801307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801331 : List Nat := [1, 1, 1, 2, 2, 4, 4, 2, 1, 2, 3]
def baseStart_3801331 : Nat := 118140960795 + 3801331 * 2 ^ 59
def prefixEnd_3801331 : Nat := 4983230072969 + 3 ^ 40 * 3801331 * 2
def baseEnd_3801331 : Nat := 1951909929836372008680503

theorem tailTrace_3801331 : CollatzResearch.WordTrace tailWord_3801331 prefixEnd_3801331 1951909929836372008680503 := by
  unfold tailWord_3801331
  simp only [CollatzResearch.WordTrace]
  refine ⟨138645931791434477493211847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92430621194289651662141231 138645931791434477493211847)
  ·
    refine ⟨207968897687151716239817771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138645931791434477493211847 207968897687151716239817771)
    ·
      refine ⟨311953346530727574359726657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207968897687151716239817771 311953346530727574359726657)
      ·
        refine ⟨233965009898045680769794993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311953346530727574359726657 233965009898045680769794993)
        ·
          refine ⟨175473757423534260577346245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233965009898045680769794993 175473757423534260577346245)
          ·
            refine ⟨32901329516912673858252421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175473757423534260577346245 32901329516912673858252421)
            ·
              refine ⟨6168999284421126348422329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32901329516912673858252421 6168999284421126348422329)
              ·
                refine ⟨4626749463315844761316747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6168999284421126348422329 4626749463315844761316747)
                ·
                  refine ⟨6940124194973767141975121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626749463315844761316747 6940124194973767141975121)
                  ·
                    refine ⟨5205093146230325356481341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6940124194973767141975121 5205093146230325356481341)
                    ·
                      refine ⟨1951909929836372008680503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5205093146230325356481341 1951909929836372008680503)
                      ·
                        rfl

theorem cell23_3801331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 2, 3].length) (baseStart_3801331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801331 prefixEnd_3801331 := by exact prefixLift 3801331
  have htrace : WordTrace (prefixWord ++ tailWord_3801331) baseStart_3801331 baseEnd_3801331 := by
    simpa [prefixWord, tailWord_3801331, baseEnd_3801331] using wordTrace_append hprefix tailTrace_3801331
  have hstable : (prefixWord ++ tailWord_3801331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801331).length < 2 ^ (prefixWord ++ tailWord_3801331).sum := by decide
  have hdescent : baseEnd_3801331 < baseStart_3801331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801344 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 3]
def baseStart_3801344 : Nat := 118140960795 + 3801344 * 2 ^ 59
def prefixEnd_3801344 : Nat := 4983230072969 + 3 ^ 40 * 3801344 * 2
def baseEnd_3801344 : Nat := 1951916605084880457817943

theorem tailTrace_3801344 : CollatzResearch.WordTrace tailWord_3801344 prefixEnd_3801344 1951916605084880457817943 := by
  unfold tailWord_3801344
  simp only [CollatzResearch.WordTrace]
  refine ⟨69323202970193690356717543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92430937293591587142290057 69323202970193690356717543)
  ·
    refine ⟨103984804455290535535076315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69323202970193690356717543 103984804455290535535076315)
    ·
      refine ⟨155977206682935803302614473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103984804455290535535076315 155977206682935803302614473)
      ·
        refine ⟨116982905012201852476960855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155977206682935803302614473 116982905012201852476960855)
        ·
          refine ⟨175474357518302778715441283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116982905012201852476960855 175474357518302778715441283)
          ·
            refine ⟨263211536277454168073161925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175474357518302778715441283 263211536277454168073161925)
            ·
              refine ⟨49352163052022656513717861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263211536277454168073161925 49352163052022656513717861)
              ·
                refine ⟨9253530572254248096322099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49352163052022656513717861 9253530572254248096322099)
                ·
                  refine ⟨13880295858381372144483149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9253530572254248096322099 13880295858381372144483149)
                  ·
                    refine ⟨5205110946893014554181181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13880295858381372144483149 5205110946893014554181181)
                    ·
                      refine ⟨1951916605084880457817943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5205110946893014554181181 1951916605084880457817943)
                      ·
                        rfl

theorem cell23_3801344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_3801344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801344 prefixEnd_3801344 := by exact prefixLift 3801344
  have htrace : WordTrace (prefixWord ++ tailWord_3801344) baseStart_3801344 baseEnd_3801344 := by
    simpa [prefixWord, tailWord_3801344, baseEnd_3801344] using wordTrace_append hprefix tailTrace_3801344
  have hstable : (prefixWord ++ tailWord_3801344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801344).length < 2 ^ (prefixWord ++ tailWord_3801344).sum := by decide
  have hdescent : baseEnd_3801344 < baseStart_3801344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801351 : List Nat := [1, 1, 4, 5, 1, 2, 9]
def baseStart_3801351 : Nat := 118140960795 + 3801351 * 2 ^ 59
def prefixEnd_3801351 : Nat := 4983230072969 + 3 ^ 40 * 3801351 * 2
def baseEnd_3801351 : Nat := 24097780240116813955931

theorem tailTrace_3801351 : CollatzResearch.WordTrace tailWord_3801351 prefixEnd_3801351 24097780240116813955931 := by
  unfold tailWord_3801351
  simp only [CollatzResearch.WordTrace]
  refine ⟨138646661251362020908939907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92431107500908013939293271 138646661251362020908939907)
  ·
    refine ⟨207969991877043031363409861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138646661251362020908939907 207969991877043031363409861)
    ·
      refine ⟨38994373476945568380639349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207969991877043031363409861 38994373476945568380639349)
      ·
        refine ⟨3655722513463647035684939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38994373476945568380639349 3655722513463647035684939)
        ·
          refine ⟨5483583770195470553527409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3655722513463647035684939 5483583770195470553527409)
          ·
            refine ⟨4112687827646602915145557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5483583770195470553527409 4112687827646602915145557)
            ·
              refine ⟨24097780240116813955931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4112687827646602915145557 24097780240116813955931)
              ·
                rfl

theorem cell23_3801351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 9].length) (baseStart_3801351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801351 prefixEnd_3801351 := by exact prefixLift 3801351
  have htrace : WordTrace (prefixWord ++ tailWord_3801351) baseStart_3801351 baseEnd_3801351 := by
    simpa [prefixWord, tailWord_3801351, baseEnd_3801351] using wordTrace_append hprefix tailTrace_3801351
  have hstable : (prefixWord ++ tailWord_3801351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801351).length < 2 ^ (prefixWord ++ tailWord_3801351).sum := by decide
  have hdescent : baseEnd_3801351 < baseStart_3801351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801361 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 4, 1, 3]
def baseStart_3801361 : Nat := 118140960795 + 3801361 * 2 ^ 59
def prefixEnd_3801361 : Nat := 4983230072969 + 3 ^ 40 * 3801361 * 2
def baseEnd_3801361 : Nat := 1951925334256006891305365

theorem tailTrace_3801361 : CollatzResearch.WordTrace tailWord_3801361 prefixEnd_3801361 1951925334256006891305365 := by
  unfold tailWord_3801361
  simp only [CollatzResearch.WordTrace]
  refine ⟨138647025981325792616803937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92431350654217195077869291 138647025981325792616803937)
  ·
    refine ⟨103985269485994344462602953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138647025981325792616803937 103985269485994344462602953)
    ·
      refine ⟨77988952114495758346952215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103985269485994344462602953 77988952114495758346952215)
      ·
        refine ⟨116983428171743637520428323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77988952114495758346952215 116983428171743637520428323)
        ·
          refine ⟨175475142257615456280642485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116983428171743637520428323 175475142257615456280642485)
          ·
            refine ⟨16450794586651449026310233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175475142257615456280642485 16450794586651449026310233)
            ·
              refine ⟨12338095939988586769732675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16450794586651449026310233 12338095939988586769732675)
              ·
                refine ⟨18507143909982880154599013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12338095939988586769732675 18507143909982880154599013)
                ·
                  refine ⟨3470089483121790028987315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18507143909982880154599013 3470089483121790028987315)
                  ·
                    refine ⟨5205134224682685043480973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3470089483121790028987315 5205134224682685043480973)
                    ·
                      refine ⟨1951925334256006891305365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5205134224682685043480973 1951925334256006891305365)
                      ·
                        rfl

theorem cell23_3801361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_3801361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801361 prefixEnd_3801361 := by exact prefixLift 3801361
  have htrace : WordTrace (prefixWord ++ tailWord_3801361) baseStart_3801361 baseEnd_3801361 := by
    simpa [prefixWord, tailWord_3801361, baseEnd_3801361] using wordTrace_append hprefix tailTrace_3801361
  have hstable : (prefixWord ++ tailWord_3801361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801361).length < 2 ^ (prefixWord ++ tailWord_3801361).sum := by decide
  have hdescent : baseEnd_3801361 < baseStart_3801361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801388 : List Nat := [2, 2, 1, 1, 1, 3, 5, 2, 1, 3, 2]
def baseStart_3801388 : Nat := 118140960795 + 3801388 * 2 ^ 59
def prefixEnd_3801388 : Nat := 4983230072969 + 3 ^ 40 * 3801388 * 2
def baseEnd_3801388 : Nat := 1951939198233678285667741

theorem tailTrace_3801388 : CollatzResearch.WordTrace tailWord_3801388 prefixEnd_3801388 1951939198233678285667741 := by
  unfold tailWord_3801388
  simp only [CollatzResearch.WordTrace]
  refine ⟨69324005376113988114018409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92432007168151984152024545 69324005376113988114018409)
  ·
    refine ⟨51993004032085491085513807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69324005376113988114018409 51993004032085491085513807)
    ·
      refine ⟨77989506048128236628270711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51993004032085491085513807 77989506048128236628270711)
      ·
        refine ⟨116984259072192354942406067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77989506048128236628270711 116984259072192354942406067)
        ·
          refine ⟨175476388608288532413609101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116984259072192354942406067 175476388608288532413609101)
          ·
            refine ⟨65803645728108199655103413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175476388608288532413609101 65803645728108199655103413)
            ·
              refine ⟨6169091787010143717665945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65803645728108199655103413 6169091787010143717665945)
              ·
                refine ⟨4626818840257607788249459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6169091787010143717665945 4626818840257607788249459)
                ·
                  refine ⟨6940228260386411682374189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626818840257607788249459 6940228260386411682374189)
                  ·
                    refine ⟨2602585597644904380890321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6940228260386411682374189 2602585597644904380890321)
                    ·
                      refine ⟨1951939198233678285667741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2602585597644904380890321 1951939198233678285667741)
                      ·
                        rfl

theorem cell23_3801388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 3, 2].length) (baseStart_3801388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801388 prefixEnd_3801388 := by exact prefixLift 3801388
  have htrace : WordTrace (prefixWord ++ tailWord_3801388) baseStart_3801388 baseEnd_3801388 := by
    simpa [prefixWord, tailWord_3801388, baseEnd_3801388] using wordTrace_append hprefix tailTrace_3801388
  have hstable : (prefixWord ++ tailWord_3801388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801388).length < 2 ^ (prefixWord ++ tailWord_3801388).sum := by decide
  have hdescent : baseEnd_3801388 < baseStart_3801388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801404 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_3801404 : Nat := 118140960795 + 3801404 * 2 ^ 59
def prefixEnd_3801404 : Nat := 4983230072969 + 3 ^ 40 * 3801404 * 2
def baseEnd_3801404 : Nat := 1951947413924150223067667

theorem tailTrace_3801404 : CollatzResearch.WordTrace tailWord_3801404 prefixEnd_3801404 1951947413924150223067667 := by
  unfold tailWord_3801404
  simp only [CollatzResearch.WordTrace]
  refine ⟨69324297160085005480309633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92432396213446673973746177 69324297160085005480309633)
  ·
    refine ⟨51993222870063754110232225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69324297160085005480309633 51993222870063754110232225)
    ·
      refine ⟨38994917152547815582674169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51993222870063754110232225 38994917152547815582674169)
      ·
        refine ⟨29246187864410861687005627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38994917152547815582674169 29246187864410861687005627)
        ·
          refine ⟨43869281796616292530508441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29246187864410861687005627 43869281796616292530508441)
          ·
            refine ⟨32901961347462219397881331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43869281796616292530508441 32901961347462219397881331)
            ·
              refine ⟨49352942021193329096821997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32901961347462219397881331 49352942021193329096821997)
              ·
                refine ⟨18507353257947498411308249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49352942021193329096821997 18507353257947498411308249)
                ·
                  refine ⟨13880514943460623808481187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18507353257947498411308249 13880514943460623808481187)
                  ·
                    refine ⟨20820772415190935712721781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13880514943460623808481187 20820772415190935712721781)
                    ·
                      refine ⟨1951947413924150223067667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20820772415190935712721781 1951947413924150223067667)
                      ·
                        rfl

theorem cell23_3801404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_3801404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801404 prefixEnd_3801404 := by exact prefixLift 3801404
  have htrace : WordTrace (prefixWord ++ tailWord_3801404) baseStart_3801404 baseEnd_3801404 := by
    simpa [prefixWord, tailWord_3801404, baseEnd_3801404] using wordTrace_append hprefix tailTrace_3801404
  have hstable : (prefixWord ++ tailWord_3801404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801404).length < 2 ^ (prefixWord ++ tailWord_3801404).sum := by decide
  have hdescent : baseEnd_3801404 < baseStart_3801404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801412 : List Nat := [2, 3, 4, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3801412 : Nat := 118140960795 + 3801412 * 2 ^ 59
def prefixEnd_3801412 : Nat := 4983230072969 + 3 ^ 40 * 3801412 * 2
def baseEnd_3801412 : Nat := 1951951521769386191767631

theorem tailTrace_3801412 : CollatzResearch.WordTrace tailWord_3801412 prefixEnd_3801412 1951951521769386191767631 := by
  unfold tailWord_3801412
  simp only [CollatzResearch.WordTrace]
  refine ⟨69324443052070514163455245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92432590736094018884606993 69324443052070514163455245)
  ·
    refine ⟨25996666144526442811295717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69324443052070514163455245 25996666144526442811295717)
    ·
      refine ⟨4874374902098708027117947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25996666144526442811295717 4874374902098708027117947)
      ·
        refine ⟨7311562353148062040676921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4874374902098708027117947 7311562353148062040676921)
        ·
          refine ⟨5483671764861046530507691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7311562353148062040676921 5483671764861046530507691)
          ·
            refine ⟨8225507647291569795761537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5483671764861046530507691 8225507647291569795761537)
            ·
              refine ⟨6169130735468677346821153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8225507647291569795761537 6169130735468677346821153)
              ·
                refine ⟨4626848051601508010115865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6169130735468677346821153 4626848051601508010115865)
                ·
                  refine ⟨3470136038701131007586899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4626848051601508010115865 3470136038701131007586899)
                  ·
                    refine ⟨5205204058051696511380349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3470136038701131007586899 5205204058051696511380349)
                    ·
                      refine ⟨1951951521769386191767631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5205204058051696511380349 1951951521769386191767631)
                      ·
                        rfl

theorem cell23_3801412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3801412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801412 prefixEnd_3801412 := by exact prefixLift 3801412
  have htrace : WordTrace (prefixWord ++ tailWord_3801412) baseStart_3801412 baseEnd_3801412 := by
    simpa [prefixWord, tailWord_3801412, baseEnd_3801412] using wordTrace_append hprefix tailTrace_3801412
  have hstable : (prefixWord ++ tailWord_3801412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801412).length < 2 ^ (prefixWord ++ tailWord_3801412).sum := by decide
  have hdescent : baseEnd_3801412 < baseStart_3801412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801458 : List Nat := [3, 2, 1, 2, 1, 4, 2, 3, 5]
def baseStart_3801458 : Nat := 118140960795 + 3801458 * 2 ^ 59
def prefixEnd_3801458 : Nat := 4983230072969 + 3 ^ 40 * 3801458 * 2
def baseEnd_3801458 : Nat := 216886126875499223532491

theorem tailTrace_3801458 : CollatzResearch.WordTrace tailWord_3801458 prefixEnd_3801458 216886126875499223532491 := by
  unfold tailWord_3801458
  simp only [CollatzResearch.WordTrace]
  refine ⟨34662640965493594545771257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92433709241316252122056685 34662640965493594545771257)
  ·
    refine ⟨25996980724120195909328443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34662640965493594545771257 25996980724120195909328443)
    ·
      refine ⟨38995471086180293863992665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25996980724120195909328443 38995471086180293863992665)
      ·
        refine ⟨29246603314635220397994499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38995471086180293863992665 29246603314635220397994499)
        ·
          refine ⟨43869904971952830596991749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29246603314635220397994499 43869904971952830596991749)
          ·
            refine ⟨8225607182241155736935953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43869904971952830596991749 8225607182241155736935953)
            ·
              refine ⟨6169205386680866802701965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8225607182241155736935953 6169205386680866802701965)
              ·
                refine ⟨2313452020005325051013237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6169205386680866802701965 2313452020005325051013237)
                ·
                  refine ⟨216886126875499223532491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2313452020005325051013237 216886126875499223532491)
                  ·
                    rfl

theorem cell23_3801458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_3801458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801458 prefixEnd_3801458 := by exact prefixLift 3801458
  have htrace : WordTrace (prefixWord ++ tailWord_3801458) baseStart_3801458 baseEnd_3801458 := by
    simpa [prefixWord, tailWord_3801458, baseEnd_3801458] using wordTrace_append hprefix tailTrace_3801458
  have hstable : (prefixWord ++ tailWord_3801458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801458).length < 2 ^ (prefixWord ++ tailWord_3801458).sum := by decide
  have hdescent : baseEnd_3801458 < baseStart_3801458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801548 : List Nat := [2, 2, 1, 4, 3, 1, 1, 3, 6]
def baseStart_3801548 : Nat := 118140960795 + 3801548 * 2 ^ 59
def prefixEnd_3801548 : Nat := 4983230072969 + 3 ^ 40 * 3801548 * 2
def baseEnd_3801548 : Nat := 216891261682044184407445

theorem tailTrace_3801548 : CollatzResearch.WordTrace tailWord_3801548 prefixEnd_3801548 216891261682044184407445 := by
  unfold tailWord_3801548
  simp only [CollatzResearch.WordTrace]
  refine ⟨69326923215824161776930649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92435897621098882369240865 69326923215824161776930649)
  ·
    refine ⟨51995192411868121332697987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69326923215824161776930649 51995192411868121332697987)
    ·
      refine ⟨77992788617802181999046981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51995192411868121332697987 77992788617802181999046981)
      ·
        refine ⟨14623647865837909124821309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77992788617802181999046981 14623647865837909124821309)
        ·
          refine ⟨5483867949689215921807991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14623647865837909124821309 5483867949689215921807991)
          ·
            refine ⟨8225801924533823882711987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5483867949689215921807991 8225801924533823882711987)
            ·
              refine ⟨12338702886800735824067981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8225801924533823882711987 12338702886800735824067981)
              ·
                refine ⟨4627013582550275934025493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12338702886800735824067981 4627013582550275934025493)
                ·
                  refine ⟨216891261682044184407445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4627013582550275934025493 216891261682044184407445)
                  ·
                    rfl

theorem cell23_3801548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_3801548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801548 prefixEnd_3801548 := by exact prefixLift 3801548
  have htrace : WordTrace (prefixWord ++ tailWord_3801548) baseStart_3801548 baseEnd_3801548 := by
    simpa [prefixWord, tailWord_3801548, baseEnd_3801548] using wordTrace_append hprefix tailTrace_3801548
  have hstable : (prefixWord ++ tailWord_3801548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801548).length < 2 ^ (prefixWord ++ tailWord_3801548).sum := by decide
  have hdescent : baseEnd_3801548 < baseStart_3801548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801561 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 3, 5]
def baseStart_3801561 : Nat := 118140960795 + 3801561 * 2 ^ 59
def prefixEnd_3801561 : Nat := 4983230072969 + 3 ^ 40 * 3801561 * 2
def baseEnd_3801561 : Nat := 650676010128968702934815

theorem tailTrace_3801561 : CollatzResearch.WordTrace tailWord_3801561 prefixEnd_3801561 650676010128968702934815 := by
  unfold tailWord_3801561
  simp only [CollatzResearch.WordTrace]
  refine ⟨138654320580601226774084537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92436213720400817849389691 138654320580601226774084537)
  ·
    refine ⟨103990740435450920080563403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138654320580601226774084537 103990740435450920080563403)
    ·
      refine ⟨155986110653176380120845105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103990740435450920080563403 155986110653176380120845105)
      ·
        refine ⟨116989582989882285090633829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155986110653176380120845105 116989582989882285090633829)
        ·
          refine ⟨21935546810602928454493843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116989582989882285090633829 21935546810602928454493843)
          ·
            refine ⟨32903320215904392681740765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21935546810602928454493843 32903320215904392681740765)
            ·
              refine ⟨12338745080964147255652787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32903320215904392681740765 12338745080964147255652787)
              ·
                refine ⟨18508117621446220883479181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12338745080964147255652787 18508117621446220883479181)
                ·
                  refine ⟨6940544108042332831304693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18508117621446220883479181 6940544108042332831304693)
                  ·
                    refine ⟨650676010128968702934815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6940544108042332831304693 650676010128968702934815)
                    ·
                      rfl

theorem cell23_3801561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 5].length) (baseStart_3801561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801561 prefixEnd_3801561 := by exact prefixLift 3801561
  have htrace : WordTrace (prefixWord ++ tailWord_3801561) baseStart_3801561 baseEnd_3801561 := by
    simpa [prefixWord, tailWord_3801561, baseEnd_3801561] using wordTrace_append hprefix tailTrace_3801561
  have hstable : (prefixWord ++ tailWord_3801561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801561).length < 2 ^ (prefixWord ++ tailWord_3801561).sum := by decide
  have hdescent : baseEnd_3801561 < baseStart_3801561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801586 : List Nat := [3, 2, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_3801586 : Nat := 118140960795 + 3801586 * 2 ^ 59
def prefixEnd_3801586 : Nat := 4983230072969 + 3 ^ 40 * 3801586 * 2
def baseEnd_3801586 : Nat := 650680289134422836997277

theorem tailTrace_3801586 : CollatzResearch.WordTrace tailWord_3801586 prefixEnd_3801586 650680289134422836997277 := by
  unfold tailWord_3801586
  simp only [CollatzResearch.WordTrace]
  refine ⟨34663808101377664010936153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92436821603673770695829741 34663808101377664010936153)
  ·
    refine ⟨25997856076033248008202115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34663808101377664010936153 25997856076033248008202115)
    ·
      refine ⟨38996784114049872012303173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25997856076033248008202115 38996784114049872012303173)
      ·
        refine ⟨7311897021384351002306845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38996784114049872012303173 7311897021384351002306845)
        ·
          refine ⟨2741961383019131625865067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7311897021384351002306845 2741961383019131625865067)
          ·
            refine ⟨4112942074528697438797601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741961383019131625865067 4112942074528697438797601)
            ·
              refine ⟨3084706555896523079098201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4112942074528697438797601 3084706555896523079098201)
              ·
                refine ⟨2313529916922392309323651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3084706555896523079098201 2313529916922392309323651)
                ·
                  refine ⟨3470294875383588463985477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2313529916922392309323651 3470294875383588463985477)
                  ·
                    refine ⟨650680289134422836997277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3470294875383588463985477 650680289134422836997277)
                    ·
                      rfl

theorem cell23_3801586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_3801586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801586 prefixEnd_3801586 := by exact prefixLift 3801586
  have htrace : WordTrace (prefixWord ++ tailWord_3801586) baseStart_3801586 baseEnd_3801586 := by
    simpa [prefixWord, tailWord_3801586, baseEnd_3801586] using wordTrace_append hprefix tailTrace_3801586
  have hstable : (prefixWord ++ tailWord_3801586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801586).length < 2 ^ (prefixWord ++ tailWord_3801586).sum := by decide
  have hdescent : baseEnd_3801586 < baseStart_3801586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801591 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 8, 4]
def baseStart_3801591 : Nat := 118140960795 + 3801591 * 2 ^ 59
def prefixEnd_3801591 : Nat := 4983230072969 + 3 ^ 40 * 3801591 * 2
def baseEnd_3801591 : Nat := 650681144935513663809769

theorem tailTrace_3801591 : CollatzResearch.WordTrace tailWord_3801591 prefixEnd_3801591 650681144935513663809769 := by
  unfold tailWord_3801591
  simp only [CollatzResearch.WordTrace]
  refine ⟨138655414770492541897676627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92436943180328361265117751 138655414770492541897676627)
  ·
    refine ⟨207983122155738812846514941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138655414770492541897676627 207983122155738812846514941)
    ·
      refine ⟨77993670808402054817443103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207983122155738812846514941 77993670808402054817443103)
      ·
        refine ⟨116990506212603082226164655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77993670808402054817443103 116990506212603082226164655)
        ·
          refine ⟨175485759318904623339246983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116990506212603082226164655 175485759318904623339246983)
          ·
            refine ⟨263228638978356935008870475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175485759318904623339246983 263228638978356935008870475)
            ·
              refine ⟨394842958467535402513305713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263228638978356935008870475 394842958467535402513305713)
              ·
                refine ⟨296132218850651551884979285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394842958467535402513305713 296132218850651551884979285)
                ·
                  refine ⟨3470299439656072873652101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 296132218850651551884979285 3470299439656072873652101)
                  ·
                    refine ⟨650681144935513663809769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3470299439656072873652101 650681144935513663809769)
                    ·
                      rfl

theorem cell23_3801591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_3801591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801591 prefixEnd_3801591 := by exact prefixLift 3801591
  have htrace : WordTrace (prefixWord ++ tailWord_3801591) baseStart_3801591 baseEnd_3801591 := by
    simpa [prefixWord, tailWord_3801591, baseEnd_3801591] using wordTrace_append hprefix tailTrace_3801591
  have hstable : (prefixWord ++ tailWord_3801591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801591).length < 2 ^ (prefixWord ++ tailWord_3801591).sum := by decide
  have hdescent : baseEnd_3801591 < baseStart_3801591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801628 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3801628 : Nat := 118140960795 + 3801628 * 2 ^ 59
def prefixEnd_3801628 : Nat := 4983230072969 + 3 ^ 40 * 3801628 * 2
def baseEnd_3801628 : Nat := 1952062433590757346666637

theorem tailTrace_3801628 : CollatzResearch.WordTrace tailWord_3801628 prefixEnd_3801628 1952062433590757346666637 := by
  unfold tailWord_3801628
  simp only [CollatzResearch.WordTrace]
  refine ⟨69328382135679248608386769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92437842847572331477849025 69328382135679248608386769)
  ·
    refine ⟨51996286601759436456290077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69328382135679248608386769 51996286601759436456290077)
    ·
      refine ⟨19498607475659788671108779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51996286601759436456290077 19498607475659788671108779)
      ·
        refine ⟨29247911213489683006663169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19498607475659788671108779 29247911213489683006663169)
        ·
          refine ⟨21935933410117262254997377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29247911213489683006663169 21935933410117262254997377)
          ·
            refine ⟨16451950057587946691248033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21935933410117262254997377 16451950057587946691248033)
            ·
              refine ⟨12338962543190960018436025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16451950057587946691248033 12338962543190960018436025)
              ·
                refine ⟨9254221907393220013827019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12338962543190960018436025 9254221907393220013827019)
                ·
                  refine ⟨13881332861089830020740529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9254221907393220013827019 13881332861089830020740529)
                  ·
                    refine ⟨10410999645817372515555397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13881332861089830020740529 10410999645817372515555397)
                    ·
                      refine ⟨1952062433590757346666637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10410999645817372515555397 1952062433590757346666637)
                      ·
                        rfl

theorem cell23_3801628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3801628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801628 prefixEnd_3801628 := by exact prefixLift 3801628
  have htrace : WordTrace (prefixWord ++ tailWord_3801628) baseStart_3801628 baseEnd_3801628 := by
    simpa [prefixWord, tailWord_3801628, baseEnd_3801628] using wordTrace_append hprefix tailTrace_3801628
  have hstable : (prefixWord ++ tailWord_3801628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801628).length < 2 ^ (prefixWord ++ tailWord_3801628).sum := by decide
  have hdescent : baseEnd_3801628 < baseStart_3801628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801635 : List Nat := [1, 1, 1, 4, 4, 2, 1, 3, 1, 2, 3]
def baseStart_3801635 : Nat := 118140960795 + 3801635 * 2 ^ 59
def prefixEnd_3801635 : Nat := 4983230072969 + 3 ^ 40 * 3801635 * 2
def baseEnd_3801635 : Nat := 1952066027955338819279105

theorem tailTrace_3801635 : CollatzResearch.WordTrace tailWord_3801635 prefixEnd_3801635 1952066027955338819279105 := by
  unfold tailWord_3801635
  simp only [CollatzResearch.WordTrace]
  refine ⟨138657019582333137412278359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92438013054888758274852239 138657019582333137412278359)
  ·
    refine ⟨207985529373499706118417539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138657019582333137412278359 207985529373499706118417539)
    ·
      refine ⟨311978294060249559177626309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207985529373499706118417539 311978294060249559177626309)
      ·
        refine ⟨58495930136296792345804933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311978294060249559177626309 58495930136296792345804933)
        ·
          refine ⟨10967986900555648564838425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58495930136296792345804933 10967986900555648564838425)
          ·
            refine ⟨8225990175416736423628819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10967986900555648564838425 8225990175416736423628819)
            ·
              refine ⟨12338985263125104635443229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8225990175416736423628819 12338985263125104635443229)
              ·
                refine ⟨4627119473671914238291211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12338985263125104635443229 4627119473671914238291211)
                ·
                  refine ⟨6940679210507871357436817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4627119473671914238291211 6940679210507871357436817)
                  ·
                    refine ⟨5205509407880903518077613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6940679210507871357436817 5205509407880903518077613)
                    ·
                      refine ⟨1952066027955338819279105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5205509407880903518077613 1952066027955338819279105)
                      ·
                        rfl

theorem cell23_3801635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_3801635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801635 prefixEnd_3801635 := by exact prefixLift 3801635
  have htrace : WordTrace (prefixWord ++ tailWord_3801635) baseStart_3801635 baseEnd_3801635 := by
    simpa [prefixWord, tailWord_3801635, baseEnd_3801635] using wordTrace_append hprefix tailTrace_3801635
  have hstable : (prefixWord ++ tailWord_3801635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801635).length < 2 ^ (prefixWord ++ tailWord_3801635).sum := by decide
  have hdescent : baseEnd_3801635 < baseStart_3801635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801642 : List Nat := [3, 1, 4, 1, 1, 4, 1, 2, 2, 4]
def baseStart_3801642 : Nat := 118140960795 + 3801642 * 2 ^ 59
def prefixEnd_3801642 : Nat := 4983230072969 + 3 ^ 40 * 3801642 * 2
def baseEnd_3801642 : Nat := 650689874106640097297191

theorem tailTrace_3801642 : CollatzResearch.WordTrace tailWord_3801642 prefixEnd_3801642 650689874106640097297191 := by
  unfold tailWord_3801642
  simp only [CollatzResearch.WordTrace]
  refine ⟨34664318723326944401945795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92438183262205185071855453 34664318723326944401945795)
  ·
    refine ⟨51996478084990416602918693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34664318723326944401945795 51996478084990416602918693)
    ·
      refine ⟨9749339640935703113047255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51996478084990416602918693 9749339640935703113047255)
      ·
        refine ⟨14624009461403554669570883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9749339640935703113047255 14624009461403554669570883)
        ·
          refine ⟨21936014192105332004356325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14624009461403554669570883 21936014192105332004356325)
          ·
            refine ⟨4113002661019749750816811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21936014192105332004356325 4113002661019749750816811)
            ·
              refine ⟨6169503991529624626225217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4113002661019749750816811 6169503991529624626225217)
              ·
                refine ⟨4627127993647218469668913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6169503991529624626225217 4627127993647218469668913)
                ·
                  refine ⟨3470345995235413852251685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4627127993647218469668913 3470345995235413852251685)
                  ·
                    refine ⟨650689874106640097297191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3470345995235413852251685 650689874106640097297191)
                    ·
                      rfl

theorem cell23_3801642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_3801642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801642 prefixEnd_3801642 := by exact prefixLift 3801642
  have htrace : WordTrace (prefixWord ++ tailWord_3801642) baseStart_3801642 baseEnd_3801642 := by
    simpa [prefixWord, tailWord_3801642, baseEnd_3801642] using wordTrace_append hprefix tailTrace_3801642
  have hstable : (prefixWord ++ tailWord_3801642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801642).length < 2 ^ (prefixWord ++ tailWord_3801642).sum := by decide
  have hdescent : baseEnd_3801642 < baseStart_3801642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801652 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3801652 : Nat := 118140960795 + 3801652 * 2 ^ 59
def prefixEnd_3801652 : Nat := 4983230072969 + 3 ^ 40 * 3801652 * 2
def baseEnd_3801652 : Nat := 1952074757126465252766527

theorem tailTrace_3801652 : CollatzResearch.WordTrace tailWord_3801652 prefixEnd_3801652 1952074757126465252766527 := by
  unfold tailWord_3801652
  simp only [CollatzResearch.WordTrace]
  refine ⟨69328819811635774657823605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92438426415514366210431473 69328819811635774657823605)
  ·
    refine ⟨6499576857340853874170963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69328819811635774657823605 6499576857340853874170963)
    ·
      refine ⟨9749365286011280811256445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6499576857340853874170963 9749365286011280811256445)
      ·
        refine ⟨3656011982254230304221167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9749365286011280811256445 3656011982254230304221167)
        ·
          refine ⟨5484017973381345456331751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3656011982254230304221167 5484017973381345456331751)
          ·
            refine ⟨8226026960072018184497627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5484017973381345456331751 8226026960072018184497627)
            ·
              refine ⟨12339040440108027276746441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8226026960072018184497627 12339040440108027276746441)
              ·
                refine ⟨9254280330081020457559831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12339040440108027276746441 9254280330081020457559831)
                ·
                  refine ⟨13881420495121530686339747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9254280330081020457559831 13881420495121530686339747)
                  ·
                    refine ⟨20822130742682296029509621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13881420495121530686339747 20822130742682296029509621)
                    ·
                      refine ⟨1952074757126465252766527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20822130742682296029509621 1952074757126465252766527)
                      ·
                        rfl

theorem cell23_3801652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3801652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801652 prefixEnd_3801652 := by exact prefixLift 3801652
  have htrace : WordTrace (prefixWord ++ tailWord_3801652) baseStart_3801652 baseEnd_3801652 := by
    simpa [prefixWord, tailWord_3801652, baseEnd_3801652] using wordTrace_append hprefix tailTrace_3801652
  have hstable : (prefixWord ++ tailWord_3801652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801652).length < 2 ^ (prefixWord ++ tailWord_3801652).sum := by decide
  have hdescent : baseEnd_3801652 < baseStart_3801652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801665 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_3801665 : Nat := 118140960795 + 3801665 * 2 ^ 59
def prefixEnd_3801665 : Nat := 4983230072969 + 3 ^ 40 * 3801665 * 2
def baseEnd_3801665 : Nat := 1952081432374973701903967

theorem tailTrace_3801665 : CollatzResearch.WordTrace tailWord_3801665 prefixEnd_3801665 1952081432374973701903967 := by
  unfold tailWord_3801665
  simp only [CollatzResearch.WordTrace]
  refine ⟨138658113772224452535870449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92438742514816301690580299 138658113772224452535870449)
  ·
    refine ⟨103993585329168339401902837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138658113772224452535870449 103993585329168339401902837)
    ·
      refine ⟨9749398624609531818928391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103993585329168339401902837 9749398624609531818928391)
      ·
        refine ⟨14624097936914297728392587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9749398624609531818928391 14624097936914297728392587)
        ·
          refine ⟨21936146905371446592588881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14624097936914297728392587 21936146905371446592588881)
          ·
            refine ⟨16452110179028584944441661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21936146905371446592588881 16452110179028584944441661)
            ·
              refine ⟨6169541317135719354165623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16452110179028584944441661 6169541317135719354165623)
              ·
                refine ⟨9254311975703579031248435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6169541317135719354165623 9254311975703579031248435)
                ·
                  refine ⟨13881467963555368546872653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9254311975703579031248435 13881467963555368546872653)
                  ·
                    refine ⟨5205550486333263205077245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13881467963555368546872653 5205550486333263205077245)
                    ·
                      refine ⟨1952081432374973701903967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5205550486333263205077245 1952081432374973701903967)
                      ·
                        rfl

theorem cell23_3801665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_3801665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801665 prefixEnd_3801665 := by exact prefixLift 3801665
  have htrace : WordTrace (prefixWord ++ tailWord_3801665) baseStart_3801665 baseEnd_3801665 := by
    simpa [prefixWord, tailWord_3801665, baseEnd_3801665] using wordTrace_append hprefix tailTrace_3801665
  have hstable : (prefixWord ++ tailWord_3801665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801665).length < 2 ^ (prefixWord ++ tailWord_3801665).sum := by decide
  have hdescent : baseEnd_3801665 < baseStart_3801665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801675 : List Nat := [1, 1, 1, 1, 3, 1, 5, 4, 1, 3, 2]
def baseStart_3801675 : Nat := 118140960795 + 3801675 * 2 ^ 59
def prefixEnd_3801675 : Nat := 4983230072969 + 3 ^ 40 * 3801675 * 2
def baseEnd_3801675 : Nat := 1952086567181518662778921

theorem tailTrace_3801675 : CollatzResearch.WordTrace tailWord_3801675 prefixEnd_3801675 1952086567181518662778921 := by
  unfold tailWord_3801675
  simp only [CollatzResearch.WordTrace]
  refine ⟨138658478502188224243734479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92438985668125482829156319 138658478502188224243734479)
  ·
    refine ⟨207987717753282336365601719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138658478502188224243734479 207987717753282336365601719)
    ·
      refine ⟨311981576629923504548402579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207987717753282336365601719 311981576629923504548402579)
      ·
        refine ⟨467972364944885256822603869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311981576629923504548402579 467972364944885256822603869)
        ·
          refine ⟨175489636854331971308476451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467972364944885256822603869 175489636854331971308476451)
          ·
            refine ⟨263234455281497956962714677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175489636854331971308476451 263234455281497956962714677)
            ·
              refine ⟨24678230182640433465254501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263234455281497956962714677 24678230182640433465254501)
              ·
                refine ⟨4627168159245081274735219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24678230182640433465254501 4627168159245081274735219)
                ·
                  refine ⟨6940752238867621912102829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4627168159245081274735219 6940752238867621912102829)
                  ·
                    refine ⟨2602782089575358217038561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6940752238867621912102829 2602782089575358217038561)
                    ·
                      refine ⟨1952086567181518662778921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2602782089575358217038561 1952086567181518662778921)
                      ·
                        rfl

theorem cell23_3801675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 3, 2].length) (baseStart_3801675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801675 prefixEnd_3801675 := by exact prefixLift 3801675
  have htrace : WordTrace (prefixWord ++ tailWord_3801675) baseStart_3801675 baseEnd_3801675 := by
    simpa [prefixWord, tailWord_3801675, baseEnd_3801675] using wordTrace_append hprefix tailTrace_3801675
  have hstable : (prefixWord ++ tailWord_3801675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801675).length < 2 ^ (prefixWord ++ tailWord_3801675).sum := by decide
  have hdescent : baseEnd_3801675 < baseStart_3801675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801778 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_3801778 : Nat := 118140960795 + 3801778 * 2 ^ 59
def prefixEnd_3801778 : Nat := 4983230072969 + 3 ^ 40 * 3801778 * 2
def baseEnd_3801778 : Nat := 1952139455688931759790947

theorem tailTrace_3801778 : CollatzResearch.WordTrace tailWord_3801778 prefixEnd_3801778 1952139455688931759790947 := by
  unfold tailWord_3801778
  simp only [CollatzResearch.WordTrace]
  refine ⟨34665558805203768208683497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92441490147210048556489325 34665558805203768208683497)
  ·
    refine ⟨25999169103902826156512623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34665558805203768208683497 25999169103902826156512623)
    ·
      refine ⟨38998753655854239234768935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25999169103902826156512623 38998753655854239234768935)
      ·
        refine ⟨58498130483781358852153403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38998753655854239234768935 58498130483781358852153403)
        ·
          refine ⟨87747195725672038278230105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58498130483781358852153403 87747195725672038278230105)
          ·
            refine ⟨65810396794254028708672579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87747195725672038278230105 65810396794254028708672579)
            ·
              refine ⟨98715595191381043063008869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65810396794254028708672579 98715595191381043063008869)
              ·
                refine ⟨18509174098383945574314163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98715595191381043063008869 18509174098383945574314163)
                ·
                  refine ⟨27763761147575918361471245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18509174098383945574314163 27763761147575918361471245)
                  ·
                    refine ⟨10411410430340969385551717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27763761147575918361471245 10411410430340969385551717)
                    ·
                      refine ⟨1952139455688931759790947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10411410430340969385551717 1952139455688931759790947)
                      ·
                        rfl

theorem cell23_3801778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_3801778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801778 prefixEnd_3801778 := by exact prefixLift 3801778
  have htrace : WordTrace (prefixWord ++ tailWord_3801778) baseStart_3801778 baseEnd_3801778 := by
    simpa [prefixWord, tailWord_3801778, baseEnd_3801778] using wordTrace_append hprefix tailTrace_3801778
  have hstable : (prefixWord ++ tailWord_3801778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801778).length < 2 ^ (prefixWord ++ tailWord_3801778).sum := by decide
  have hdescent : baseEnd_3801778 < baseStart_3801778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801818 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 8]
def baseStart_3801818 : Nat := 118140960795 + 3801818 * 2 ^ 59
def prefixEnd_3801818 : Nat := 4983230072969 + 3 ^ 40 * 3801818 * 2
def baseEnd_3801818 : Nat := 216906666101679067032307

theorem tailTrace_3801818 : CollatzResearch.WordTrace tailWord_3801818 prefixEnd_3801818 216906666101679067032307 := by
  unfold tailWord_3801818
  simp only [CollatzResearch.WordTrace]
  refine ⟨34665923535167539916547527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92442462760446773110793405 34665923535167539916547527)
  ·
    refine ⟨51998885302751309874821291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34665923535167539916547527 51998885302751309874821291)
    ·
      refine ⟨77998327954126964812231937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51998885302751309874821291 77998327954126964812231937)
      ·
        refine ⟨58498745965595223609173953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77998327954126964812231937 58498745965595223609173953)
        ·
          refine ⟨43874059474196417706880465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58498745965595223609173953 43874059474196417706880465)
          ·
            refine ⟨32905544605647313280160349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43874059474196417706880465 32905544605647313280160349)
            ·
              refine ⟨12339579227117742480060131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32905544605647313280160349 12339579227117742480060131)
              ·
                refine ⟨18509368840676613720090197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12339579227117742480060131 18509368840676613720090197)
                ·
                  refine ⟨216906666101679067032307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18509368840676613720090197 216906666101679067032307)
                  ·
                    rfl

theorem cell23_3801818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_3801818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801818 prefixEnd_3801818 := by exact prefixLift 3801818
  have htrace : WordTrace (prefixWord ++ tailWord_3801818) baseStart_3801818 baseEnd_3801818 := by
    simpa [prefixWord, tailWord_3801818, baseEnd_3801818] using wordTrace_append hprefix tailTrace_3801818
  have hstable : (prefixWord ++ tailWord_3801818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801818).length < 2 ^ (prefixWord ++ tailWord_3801818).sum := by decide
  have hdescent : baseEnd_3801818 < baseStart_3801818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801865 : List Nat := [1, 2, 1, 1, 3, 2, 4, 3, 1, 5]
def baseStart_3801865 : Nat := 118140960795 + 3801865 * 2 ^ 59
def prefixEnd_3801865 : Nat := 4983230072969 + 3 ^ 40 * 3801865 * 2
def baseEnd_3801865 : Nat := 650728042835290973134349

theorem tailTrace_3801865 : CollatzResearch.WordTrace tailWord_3801865 prefixEnd_3801865 650728042835290973134349 := by
  unfold tailWord_3801865
  simp only [CollatzResearch.WordTrace]
  refine ⟨138665408371499886693151049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92443605580999924462100699 138665408371499886693151049)
  ·
    refine ⟨103999056278624915019863287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138665408371499886693151049 103999056278624915019863287)
    ·
      refine ⟨155998584417937372529794931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103999056278624915019863287 155998584417937372529794931)
      ·
        refine ⟨233997876626906058794692397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155998584417937372529794931 233997876626906058794692397)
        ·
          refine ⟨87749203735089772048009649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233997876626906058794692397 87749203735089772048009649)
          ·
            refine ⟨65811902801317329036007237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87749203735089772048009649 65811902801317329036007237)
            ·
              refine ⟨12339731775246999194251357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65811902801317329036007237 12339731775246999194251357)
              ·
                refine ⟨4627399415717624697844259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12339731775246999194251357 4627399415717624697844259)
                ·
                  refine ⟨6941099123576437046766389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4627399415717624697844259 6941099123576437046766389)
                  ·
                    refine ⟨650728042835290973134349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6941099123576437046766389 650728042835290973134349)
                    ·
                      rfl

theorem cell23_3801865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 5].length) (baseStart_3801865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801865 prefixEnd_3801865 := by exact prefixLift 3801865
  have htrace : WordTrace (prefixWord ++ tailWord_3801865) baseStart_3801865 baseEnd_3801865 := by
    simpa [prefixWord, tailWord_3801865, baseEnd_3801865] using wordTrace_append hprefix tailTrace_3801865
  have hstable : (prefixWord ++ tailWord_3801865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801865).length < 2 ^ (prefixWord ++ tailWord_3801865).sum := by decide
  have hdescent : baseEnd_3801865 < baseStart_3801865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801919 : List Nat := [1, 1, 2, 2, 5, 2, 3, 1, 1, 1, 4]
def baseStart_3801919 : Nat := 118140960795 + 3801919 * 2 ^ 59
def prefixEnd_3801919 : Nat := 4983230072969 + 3 ^ 40 * 3801919 * 2
def baseEnd_3801919 : Nat := 1952211856461215708127799

theorem tailTrace_3801919 : CollatzResearch.WordTrace tailWord_3801919 prefixEnd_3801919 1952211856461215708127799 := by
  unfold tailWord_3801919
  simp only [CollatzResearch.WordTrace]
  refine ⟨138667377913304253915616811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92444918608869502610411207 138667377913304253915616811)
  ·
    refine ⟨208001066869956380873425217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138667377913304253915616811 208001066869956380873425217)
    ·
      refine ⟨156000800152467285655068913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208001066869956380873425217 156000800152467285655068913)
      ·
        refine ⟨117000600114350464241301685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156000800152467285655068913 117000600114350464241301685)
        ·
          refine ⟨10968806260720356022622033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117000600114350464241301685 10968806260720356022622033)
          ·
            refine ⟨8226604695540267016966525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10968806260720356022622033 8226604695540267016966525)
            ·
              refine ⟨3084976760827600131362447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8226604695540267016966525 3084976760827600131362447)
              ·
                refine ⟨4627465141241400197043671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3084976760827600131362447 4627465141241400197043671)
                ·
                  refine ⟨6941197711862100295565507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4627465141241400197043671 6941197711862100295565507)
                  ·
                    refine ⟨10411796567793150443348261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6941197711862100295565507 10411796567793150443348261)
                    ·
                      refine ⟨1952211856461215708127799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10411796567793150443348261 1952211856461215708127799)
                      ·
                        rfl

theorem cell23_3801919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 1, 1, 4].length) (baseStart_3801919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801919 prefixEnd_3801919 := by exact prefixLift 3801919
  have htrace : WordTrace (prefixWord ++ tailWord_3801919) baseStart_3801919 baseEnd_3801919 := by
    simpa [prefixWord, tailWord_3801919, baseEnd_3801919] using wordTrace_append hprefix tailTrace_3801919
  have hstable : (prefixWord ++ tailWord_3801919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801919).length < 2 ^ (prefixWord ++ tailWord_3801919).sum := by decide
  have hdescent : baseEnd_3801919 < baseStart_3801919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801952 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 3]
def baseStart_3801952 : Nat := 118140960795 + 3801952 * 2 ^ 59
def prefixEnd_3801952 : Nat := 4983230072969 + 3 ^ 40 * 3801952 * 2
def baseEnd_3801952 : Nat := 1952228801322814079015147

theorem tailTrace_3801952 : CollatzResearch.WordTrace tailWord_3801952 prefixEnd_3801952 1952228801322814079015147 := by
  unfold tailWord_3801952
  simp only [CollatzResearch.WordTrace]
  refine ⟨69334290761092350275784055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92445721014789800367712073 69334290761092350275784055)
  ·
    refine ⟨104001436141638525413676083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69334290761092350275784055 104001436141638525413676083)
    ·
      refine ⟨156002154212457788120514125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104001436141638525413676083 156002154212457788120514125)
      ·
        refine ⟨58500807829671670545192797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156002154212457788120514125 58500807829671670545192797)
        ·
          refine ⟨21937802936126876454447299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58500807829671670545192797 21937802936126876454447299)
          ·
            refine ⟨32906704404190314681670949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21937802936126876454447299 32906704404190314681670949)
            ·
              refine ⟨6170007075785684002813303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32906704404190314681670949 6170007075785684002813303)
              ·
                refine ⟨9255010613678526004219955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6170007075785684002813303 9255010613678526004219955)
                ·
                  refine ⟨13882515920517789006329933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9255010613678526004219955 13882515920517789006329933)
                  ·
                    refine ⟨5205943470194170877373725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13882515920517789006329933 5205943470194170877373725)
                    ·
                      refine ⟨1952228801322814079015147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5205943470194170877373725 1952228801322814079015147)
                      ·
                        rfl

theorem cell23_3801952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_3801952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801952 prefixEnd_3801952 := by exact prefixLift 3801952
  have htrace : WordTrace (prefixWord ++ tailWord_3801952) baseStart_3801952 baseEnd_3801952 := by
    simpa [prefixWord, tailWord_3801952, baseEnd_3801952] using wordTrace_append hprefix tailTrace_3801952
  have hstable : (prefixWord ++ tailWord_3801952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801952).length < 2 ^ (prefixWord ++ tailWord_3801952).sum := by decide
  have hdescent : baseEnd_3801952 < baseStart_3801952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801965 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_3801965 : Nat := 118140960795 + 3801965 * 2 ^ 59
def prefixEnd_3801965 : Nat := 4983230072969 + 3 ^ 40 * 3801965 * 2
def baseEnd_3801965 : Nat := 1952235476571322528152587

theorem tailTrace_3801965 : CollatzResearch.WordTrace tailWord_3801965 prefixEnd_3801965 1952235476571322528152587 := by
  unfold tailWord_3801965
  simp only [CollatzResearch.WordTrace]
  refine ⟨138669055671137603771791349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92446037114091735847860899 138669055671137603771791349)
  ·
    refine ⟨13000223969169150353605439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138669055671137603771791349 13000223969169150353605439)
    ·
      refine ⟨19500335953753725530408159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13000223969169150353605439 19500335953753725530408159)
      ·
        refine ⟨29250503930630588295612239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19500335953753725530408159 29250503930630588295612239)
        ·
          refine ⟨43875755895945882443418359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29250503930630588295612239 43875755895945882443418359)
          ·
            refine ⟨65813633843918823665127539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43875755895945882443418359 65813633843918823665127539)
            ·
              refine ⟨98720450765878235497691309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65813633843918823665127539 98720450765878235497691309)
              ·
                refine ⟨37020169037204338311634241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98720450765878235497691309 37020169037204338311634241)
                ·
                  refine ⟨27765126777903253733725681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37020169037204338311634241 27765126777903253733725681)
                  ·
                    refine ⟨20823845083427440300294261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27765126777903253733725681 20823845083427440300294261)
                    ·
                      refine ⟨1952235476571322528152587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20823845083427440300294261 1952235476571322528152587)
                      ·
                        rfl

theorem cell23_3801965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_3801965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801965 prefixEnd_3801965 := by exact prefixLift 3801965
  have htrace : WordTrace (prefixWord ++ tailWord_3801965) baseStart_3801965 baseEnd_3801965 := by
    simpa [prefixWord, tailWord_3801965, baseEnd_3801965] using wordTrace_append hprefix tailTrace_3801965
  have hstable : (prefixWord ++ tailWord_3801965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801965).length < 2 ^ (prefixWord ++ tailWord_3801965).sum := by decide
  have hdescent : baseEnd_3801965 < baseStart_3801965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801995 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 3]
def baseStart_3801995 : Nat := 118140960795 + 3801995 * 2 ^ 59
def prefixEnd_3801995 : Nat := 4983230072969 + 3 ^ 40 * 3801995 * 2
def baseEnd_3801995 : Nat := 1952250880990957410777449

theorem tailTrace_3801995 : CollatzResearch.WordTrace tailWord_3801995 prefixEnd_3801995 1952250880990957410777449 := by
  unfold tailWord_3801995
  simp only [CollatzResearch.WordTrace]
  refine ⟨138670149861028918895383439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92446766574019279263588959 138670149861028918895383439)
  ·
    refine ⟨208005224791543378343075159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138670149861028918895383439 208005224791543378343075159)
    ·
      refine ⟨312007837187315067514612739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208005224791543378343075159 312007837187315067514612739)
      ·
        refine ⟨468011755780972601271919109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312007837187315067514612739 468011755780972601271919109)
        ·
          refine ⟨87752204208932362738484833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 468011755780972601271919109 87752204208932362738484833)
          ·
            refine ⟨65814153156699272053863625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87752204208932362738484833 65814153156699272053863625)
            ·
              refine ⟨49360614867524454040397719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65814153156699272053863625 49360614867524454040397719)
              ·
                refine ⟨74040922301286681060596579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49360614867524454040397719 74040922301286681060596579)
                ·
                  refine ⟨111061383451930021590894869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74040922301286681060596579 111061383451930021590894869)
                  ·
                    refine ⟨5206002349309219762073197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111061383451930021590894869 5206002349309219762073197)
                    ·
                      refine ⟨1952250880990957410777449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5206002349309219762073197 1952250880990957410777449)
                      ·
                        rfl

theorem cell23_3801995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 3].length) (baseStart_3801995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3801995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3801995 prefixEnd_3801995 := by exact prefixLift 3801995
  have htrace : WordTrace (prefixWord ++ tailWord_3801995) baseStart_3801995 baseEnd_3801995 := by
    simpa [prefixWord, tailWord_3801995, baseEnd_3801995] using wordTrace_append hprefix tailTrace_3801995
  have hstable : (prefixWord ++ tailWord_3801995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801995).length < 2 ^ (prefixWord ++ tailWord_3801995).sum := by decide
  have hdescent : baseEnd_3801995 < baseStart_3801995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802055 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_3802055 : Nat := 118140960795 + 3802055 * 2 ^ 59
def prefixEnd_3802055 : Nat := 4983230072969 + 3 ^ 40 * 3802055 * 2
def baseEnd_3802055 : Nat := 1952281689830227176027173

theorem tailTrace_3802055 : CollatzResearch.WordTrace tailWord_3802055 prefixEnd_3802055 1952281689830227176027173 := by
  unfold tailWord_3802055
  simp only [CollatzResearch.WordTrace]
  refine ⟨138672338240811549142567619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92448225493874366095045079 138672338240811549142567619)
  ·
    refine ⟨208008507361217323713851429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138672338240811549142567619 208008507361217323713851429)
    ·
      refine ⟨39001595130228248196347143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208008507361217323713851429 39001595130228248196347143)
      ·
        refine ⟨58502392695342372294520715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39001595130228248196347143 58502392695342372294520715)
        ·
          refine ⟨87753589043013558441781073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58502392695342372294520715 87753589043013558441781073)
          ·
            refine ⟨65815191782260168831335805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87753589043013558441781073 65815191782260168831335805)
            ·
              refine ⟨24680696918347563311750927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65815191782260168831335805 24680696918347563311750927)
              ·
                refine ⟨37021045377521344967626391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24680696918347563311750927 37021045377521344967626391)
                ·
                  refine ⟨55531568066282017451439587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37021045377521344967626391 55531568066282017451439587)
                  ·
                    refine ⟨83297352099423026177159381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55531568066282017451439587 83297352099423026177159381)
                    ·
                      refine ⟨1952281689830227176027173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83297352099423026177159381 1952281689830227176027173)
                      ·
                        rfl

theorem cell23_3802055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_3802055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802055 prefixEnd_3802055 := by exact prefixLift 3802055
  have htrace : WordTrace (prefixWord ++ tailWord_3802055) baseStart_3802055 baseEnd_3802055 := by
    simpa [prefixWord, tailWord_3802055, baseEnd_3802055] using wordTrace_append hprefix tailTrace_3802055
  have hstable : (prefixWord ++ tailWord_3802055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802055).length < 2 ^ (prefixWord ++ tailWord_3802055).sum := by decide
  have hdescent : baseEnd_3802055 < baseStart_3802055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802079 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 2, 5]
def baseStart_3802079 : Nat := 118140960795 + 3802079 * 2 ^ 59
def prefixEnd_3802079 : Nat := 4983230072969 + 3 ^ 40 * 3802079 * 2
def baseEnd_3802079 : Nat := 650764671121978360709021

theorem tailTrace_3802079 : CollatzResearch.WordTrace tailWord_3802079 prefixEnd_3802079 650764671121978360709021 := by
  unfold tailWord_3802079
  simp only [CollatzResearch.WordTrace]
  refine ⟨138673213592724601241441291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92448809061816400827627527 138673213592724601241441291)
  ·
    refine ⟨208009820389086901862161937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138673213592724601241441291 208009820389086901862161937)
    ·
      refine ⟨156007365291815176396621453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208009820389086901862161937 156007365291815176396621453)
      ·
        refine ⟨58502761984430691148733045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156007365291815176396621453 58502761984430691148733045)
        ·
          refine ⟨5484633936040377295193723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58502761984430691148733045 5484633936040377295193723)
          ·
            refine ⟨8226950904060565942790585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5484633936040377295193723 8226950904060565942790585)
            ·
              refine ⟨6170213178045424457092939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8226950904060565942790585 6170213178045424457092939)
              ·
                refine ⟨9255319767068136685639409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6170213178045424457092939 9255319767068136685639409)
                ·
                  refine ⟨6941489825301102514229557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9255319767068136685639409 6941489825301102514229557)
                  ·
                    refine ⟨650764671121978360709021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6941489825301102514229557 650764671121978360709021)
                    ·
                      rfl

theorem cell23_3802079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 5].length) (baseStart_3802079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802079 prefixEnd_3802079 := by exact prefixLift 3802079
  have htrace : WordTrace (prefixWord ++ tailWord_3802079) baseStart_3802079 baseEnd_3802079 := by
    simpa [prefixWord, tailWord_3802079, baseEnd_3802079] using wordTrace_append hprefix tailTrace_3802079
  have hstable : (prefixWord ++ tailWord_3802079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802079).length < 2 ^ (prefixWord ++ tailWord_3802079).sum := by decide
  have hdescent : baseEnd_3802079 < baseStart_3802079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802130 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3802130 : Nat := 118140960795 + 3802130 * 2 ^ 59
def prefixEnd_3802130 : Nat := 4983230072969 + 3 ^ 40 * 3802130 * 2
def baseEnd_3802130 : Nat := 650773400293104794196443

theorem tailTrace_3802130 : CollatzResearch.WordTrace tailWord_3802130 prefixEnd_3802130 650773400293104794196443 := by
  unfold tailWord_3802130
  simp only [CollatzResearch.WordTrace]
  refine ⟨34668768428884959237886961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92450049143693224634365229 34668768428884959237886961)
  ·
    refine ⟨26001576321663719428415221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34668768428884959237886961 26001576321663719428415221)
    ·
      refine ⟨2437647780155973696413927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26001576321663719428415221 2437647780155973696413927)
      ·
        refine ⟨3656471670233960544620891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2437647780155973696413927 3656471670233960544620891)
        ·
          refine ⟨5484707505350940816931337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3656471670233960544620891 5484707505350940816931337)
          ·
            refine ⟨4113530629013205612698503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5484707505350940816931337 4113530629013205612698503)
            ·
              refine ⟨6170295943519808419047755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4113530629013205612698503 6170295943519808419047755)
              ·
                refine ⟨9255443915279712628571633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6170295943519808419047755 9255443915279712628571633)
                ·
                  refine ⟨6941582936459784471428725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9255443915279712628571633 6941582936459784471428725)
                  ·
                    refine ⟨650773400293104794196443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6941582936459784471428725 650773400293104794196443)
                    ·
                      rfl

theorem cell23_3802130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3802130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802130 prefixEnd_3802130 := by exact prefixLift 3802130
  have htrace : WordTrace (prefixWord ++ tailWord_3802130) baseStart_3802130 baseEnd_3802130 := by
    simpa [prefixWord, tailWord_3802130, baseEnd_3802130] using wordTrace_append hprefix tailTrace_3802130
  have hstable : (prefixWord ++ tailWord_3802130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802130).length < 2 ^ (prefixWord ++ tailWord_3802130).sum := by decide
  have hdescent : baseEnd_3802130 < baseStart_3802130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802136 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 2, 2, 3]
def baseStart_3802136 : Nat := 118140960795 + 3802136 * 2 ^ 59
def prefixEnd_3802136 : Nat := 4983230072969 + 3 ^ 40 * 3802136 * 2
def baseEnd_3802136 : Nat := 1952323281763241359114301

theorem tailTrace_3802136 : CollatzResearch.WordTrace tailWord_3802136 prefixEnd_3802136 1952323281763241359114301 := by
  unfold tailWord_3802136
  simp only [CollatzResearch.WordTrace]
  refine ⟨69337646276759049988133131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92450195035678733317510841 69337646276759049988133131)
  ·
    refine ⟨104006469415138574982199697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69337646276759049988133131 104006469415138574982199697)
    ·
      refine ⟨78004852061353931236649773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104006469415138574982199697 78004852061353931236649773)
      ·
        refine ⟨29251819523007724213743665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78004852061353931236649773 29251819523007724213743665)
        ·
          refine ⟨21938864642255793160307749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29251819523007724213743665 21938864642255793160307749)
          ·
            refine ⟨4113537120422961217557703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21938864642255793160307749 4113537120422961217557703)
            ·
              refine ⟨6170305680634441826336555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4113537120422961217557703 6170305680634441826336555)
              ·
                refine ⟨9255458520951662739504833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6170305680634441826336555 9255458520951662739504833)
                ·
                  refine ⟨6941593890713747054628625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9255458520951662739504833 6941593890713747054628625)
                  ·
                    refine ⟨5206195418035310290971469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6941593890713747054628625 5206195418035310290971469)
                    ·
                      refine ⟨1952323281763241359114301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5206195418035310290971469 1952323281763241359114301)
                      ·
                        rfl

theorem cell23_3802136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_3802136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802136 prefixEnd_3802136 := by exact prefixLift 3802136
  have htrace : WordTrace (prefixWord ++ tailWord_3802136) baseStart_3802136 baseEnd_3802136 := by
    simpa [prefixWord, tailWord_3802136, baseEnd_3802136] using wordTrace_append hprefix tailTrace_3802136
  have hstable : (prefixWord ++ tailWord_3802136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802136).length < 2 ^ (prefixWord ++ tailWord_3802136).sum := by decide
  have hdescent : baseEnd_3802136 < baseStart_3802136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802149 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 5, 1, 3]
def baseStart_3802149 : Nat := 118140960795 + 3802149 * 2 ^ 59
def prefixEnd_3802149 : Nat := 4983230072969 + 3 ^ 40 * 3802149 * 2
def baseEnd_3802149 : Nat := 1952329957011749808251741

theorem tailTrace_3802149 : CollatzResearch.WordTrace tailWord_3802149 prefixEnd_3802149 1952329957011749808251741 := by
  unfold tailWord_3802149
  simp only [CollatzResearch.WordTrace]
  refine ⟨138675766702471003196489501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92450511134980668797659667 138675766702471003196489501)
  ·
    refine ⟨52003412513426626198683563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138675766702471003196489501 52003412513426626198683563)
    ·
      refine ⟨78005118770139939298025345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52003412513426626198683563 78005118770139939298025345)
      ·
        refine ⟨58503839077604954473519009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78005118770139939298025345 58503839077604954473519009)
        ·
          refine ⟨43877879308203715855139257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58503839077604954473519009 43877879308203715855139257)
          ·
            refine ⟨32908409481152786891354443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43877879308203715855139257 32908409481152786891354443)
            ·
              refine ⟨49362614221729180337031665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32908409481152786891354443 49362614221729180337031665)
              ·
                refine ⟨37021960666296885252773749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49362614221729180337031665 37021960666296885252773749)
                ·
                  refine ⟨3470808812465332992447539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37021960666296885252773749 3470808812465332992447539)
                  ·
                    refine ⟨5206213218697999488671309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3470808812465332992447539 5206213218697999488671309)
                    ·
                      refine ⟨1952329957011749808251741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5206213218697999488671309 1952329957011749808251741)
                      ·
                        rfl

theorem cell23_3802149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_3802149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802149 prefixEnd_3802149 := by exact prefixLift 3802149
  have htrace : WordTrace (prefixWord ++ tailWord_3802149) baseStart_3802149 baseEnd_3802149 := by
    simpa [prefixWord, tailWord_3802149, baseEnd_3802149] using wordTrace_append hprefix tailTrace_3802149
  have hstable : (prefixWord ++ tailWord_3802149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802149).length < 2 ^ (prefixWord ++ tailWord_3802149).sum := by decide
  have hdescent : baseEnd_3802149 < baseStart_3802149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802192 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 3]
def baseStart_3802192 : Nat := 118140960795 + 3802192 * 2 ^ 59
def prefixEnd_3802192 : Nat := 4983230072969 + 3 ^ 40 * 3802192 * 2
def baseEnd_3802192 : Nat := 1952352036679893140014043

theorem tailTrace_3802192 : CollatzResearch.WordTrace tailWord_3802192 prefixEnd_3802192 1952352036679893140014043 := by
  unfold tailWord_3802192
  simp only [CollatzResearch.WordTrace]
  refine ⟨69338667520657610770152415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92451556694210147693536553 69338667520657610770152415)
  ·
    refine ⟨104008001280986416155228623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69338667520657610770152415 104008001280986416155228623)
    ·
      refine ⟨156012001921479624232842935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104008001280986416155228623 156012001921479624232842935)
      ·
        refine ⟨234018002882219436349264403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156012001921479624232842935 234018002882219436349264403)
        ·
          refine ⟨351027004323329154523896605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234018002882219436349264403 351027004323329154523896605)
          ·
            refine ⟨131635126621248432946461227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351027004323329154523896605 131635126621248432946461227)
            ·
              refine ⟨197452689931872649419691841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131635126621248432946461227 197452689931872649419691841)
              ·
                refine ⟨148089517448904487064768881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197452689931872649419691841 148089517448904487064768881)
                ·
                  refine ⟨111067138086678365298576661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148089517448904487064768881 111067138086678365298576661)
                  ·
                    refine ⟨5206272097813048373370781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111067138086678365298576661 5206272097813048373370781)
                    ·
                      refine ⟨1952352036679893140014043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5206272097813048373370781 1952352036679893140014043)
                      ·
                        rfl

theorem cell23_3802192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 3].length) (baseStart_3802192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802192 prefixEnd_3802192 := by exact prefixLift 3802192
  have htrace : WordTrace (prefixWord ++ tailWord_3802192) baseStart_3802192 baseEnd_3802192 := by
    simpa [prefixWord, tailWord_3802192, baseEnd_3802192] using wordTrace_append hprefix tailTrace_3802192
  have hstable : (prefixWord ++ tailWord_3802192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802192).length < 2 ^ (prefixWord ++ tailWord_3802192).sum := by decide
  have hdescent : baseEnd_3802192 < baseStart_3802192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802252 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_3802252 : Nat := 118140960795 + 3802252 * 2 ^ 59
def prefixEnd_3802252 : Nat := 4983230072969 + 3 ^ 40 * 3802252 * 2
def baseEnd_3802252 : Nat := 1952382845519162905263767

theorem tailTrace_3802252 : CollatzResearch.WordTrace tailWord_3802252 prefixEnd_3802252 1952382845519162905263767 := by
  unfold tailWord_3802252
  simp only [CollatzResearch.WordTrace]
  refine ⟨69339761710548925893744505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92453015614065234524992673 69339761710548925893744505)
  ·
    refine ⟨52004821282911694420308379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69339761710548925893744505 52004821282911694420308379)
    ·
      refine ⟨78007231924367541630462569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52004821282911694420308379 78007231924367541630462569)
      ·
        refine ⟨58505423943275656222846927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78007231924367541630462569 58505423943275656222846927)
        ·
          refine ⟨87758135914913484334270391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58505423943275656222846927 87758135914913484334270391)
          ·
            refine ⟨131637203872370226501405587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87758135914913484334270391 131637203872370226501405587)
            ·
              refine ⟨197455805808555339752108381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131637203872370226501405587 197455805808555339752108381)
              ·
                refine ⟨74045927178208252407040643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197455805808555339752108381 74045927178208252407040643)
                ·
                  refine ⟨111068890767312378610560965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74045927178208252407040643 111068890767312378610560965)
                  ·
                    refine ⟨20825417018871070989480181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111068890767312378610560965 20825417018871070989480181)
                    ·
                      refine ⟨1952382845519162905263767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20825417018871070989480181 1952382845519162905263767)
                      ·
                        rfl

theorem cell23_3802252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_3802252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802252 prefixEnd_3802252 := by exact prefixLift 3802252
  have htrace : WordTrace (prefixWord ++ tailWord_3802252) baseStart_3802252 baseEnd_3802252 := by
    simpa [prefixWord, tailWord_3802252, baseEnd_3802252] using wordTrace_append hprefix tailTrace_3802252
  have hstable : (prefixWord ++ tailWord_3802252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802252).length < 2 ^ (prefixWord ++ tailWord_3802252).sum := by decide
  have hdescent : baseEnd_3802252 < baseStart_3802252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802273 : List Nat := [1, 2, 3, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_3802273 : Nat := 118140960795 + 3802273 * 2 ^ 59
def prefixEnd_3802273 : Nat := 4983230072969 + 3 ^ 40 * 3802273 * 2
def baseEnd_3802273 : Nat := 1952393628612907323101171

theorem tailTrace_3802273 : CollatzResearch.WordTrace tailWord_3802273 prefixEnd_3802273 1952393628612907323101171 := by
  unfold tailWord_3802273
  simp only [CollatzResearch.WordTrace]
  refine ⟨138680289354021772374003473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92453526236014514916002315 138680289354021772374003473)
  ·
    refine ⟨104010217015516329280502605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138680289354021772374003473 104010217015516329280502605)
    ·
      refine ⟨39003831380818623480188477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104010217015516329280502605 39003831380818623480188477)
      ·
        refine ⟨14626436767806983805070679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39003831380818623480188477 14626436767806983805070679)
        ·
          refine ⟨21939655151710475707606019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14626436767806983805070679 21939655151710475707606019)
          ·
            refine ⟨32909482727565713561409029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21939655151710475707606019 32909482727565713561409029)
            ·
              refine ⟨6170528011418571292764193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32909482727565713561409029 6170528011418571292764193)
              ·
                refine ⟨4627896008563928469573145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6170528011418571292764193 4627896008563928469573145)
                ·
                  refine ⟨3470922006422946352179859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4627896008563928469573145 3470922006422946352179859)
                  ·
                    refine ⟨5206383009634419528269789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3470922006422946352179859 5206383009634419528269789)
                    ·
                      refine ⟨1952393628612907323101171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5206383009634419528269789 1952393628612907323101171)
                      ·
                        rfl

theorem cell23_3802273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_3802273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802273 prefixEnd_3802273 := by exact prefixLift 3802273
  have htrace : WordTrace (prefixWord ++ tailWord_3802273) baseStart_3802273 baseEnd_3802273 := by
    simpa [prefixWord, tailWord_3802273, baseEnd_3802273] using wordTrace_append hprefix tailTrace_3802273
  have hstable : (prefixWord ++ tailWord_3802273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802273).length < 2 ^ (prefixWord ++ tailWord_3802273).sum := by decide
  have hdescent : baseEnd_3802273 < baseStart_3802273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802289 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 1, 8]
def baseStart_3802289 : Nat := 118140960795 + 3802289 * 2 ^ 59
def prefixEnd_3802289 : Nat := 4983230072969 + 3 ^ 40 * 3802289 * 2
def baseEnd_3802289 : Nat := 650800614767793086833699

theorem tailTrace_3802289 : CollatzResearch.WordTrace tailWord_3802289 prefixEnd_3802289 650800614767793086833699 := by
  unfold tailWord_3802289
  simp only [CollatzResearch.WordTrace]
  refine ⟨138680872921963807106585921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92453915281309204737723947 138680872921963807106585921)
  ·
    refine ⟨104010654691472855329939441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138680872921963807106585921 104010654691472855329939441)
    ·
      refine ⟨78007991018604641497454581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104010654691472855329939441 78007991018604641497454581)
      ·
        refine ⟨7313249157994185140386367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78007991018604641497454581 7313249157994185140386367)
        ·
          refine ⟨10969873736991277710579551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7313249157994185140386367 10969873736991277710579551)
          ·
            refine ⟨16454810605486916565869327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10969873736991277710579551 16454810605486916565869327)
            ·
              refine ⟨24682215908230374848803991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16454810605486916565869327 24682215908230374848803991)
              ·
                refine ⟨37023323862345562273205987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24682215908230374848803991 37023323862345562273205987)
                ·
                  refine ⟨55534985793518343409808981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37023323862345562273205987 55534985793518343409808981)
                  ·
                    refine ⟨650800614767793086833699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55534985793518343409808981 650800614767793086833699)
                    ·
                      rfl

theorem cell23_3802289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_3802289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802289 prefixEnd_3802289 := by exact prefixLift 3802289
  have htrace : WordTrace (prefixWord ++ tailWord_3802289) baseStart_3802289 baseEnd_3802289 := by
    simpa [prefixWord, tailWord_3802289, baseEnd_3802289] using wordTrace_append hprefix tailTrace_3802289
  have hstable : (prefixWord ++ tailWord_3802289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802289).length < 2 ^ (prefixWord ++ tailWord_3802289).sum := by decide
  have hdescent : baseEnd_3802289 < baseStart_3802289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802324 : List Nat := [2, 4, 1, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3802324 : Nat := 118140960795 + 3802324 * 2 ^ 59
def prefixEnd_3802324 : Nat := 4983230072969 + 3 ^ 40 * 3802324 * 2
def baseEnd_3802324 : Nat := 1952419816126286623563437

theorem tailTrace_3802324 : CollatzResearch.WordTrace tailWord_3802324 prefixEnd_3802324 1952419816126286623563437 := by
  unfold tailWord_3802324
  simp only [CollatzResearch.WordTrace]
  refine ⟨69341074738418504042055013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92454766317891338722740017 69341074738418504042055013)
  ·
    refine ⟨13001451513453469507885315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69341074738418504042055013 13001451513453469507885315)
    ·
      refine ⟨19502177270180204261827973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13001451513453469507885315 19502177270180204261827973)
      ·
        refine ⟨3656658238158788299092745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19502177270180204261827973 3656658238158788299092745)
        ·
          refine ⟨2742493678619091224319559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3656658238158788299092745 2742493678619091224319559)
          ·
            refine ⟨4113740517928636836479339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742493678619091224319559 4113740517928636836479339)
            ·
              refine ⟨6170610776892955254719009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4113740517928636836479339 6170610776892955254719009)
              ·
                refine ⟨4627958082669716441039257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6170610776892955254719009 4627958082669716441039257)
                ·
                  refine ⟨3470968562002287330779443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4627958082669716441039257 3470968562002287330779443)
                  ·
                    refine ⟨5206452843003430996169165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3470968562002287330779443 5206452843003430996169165)
                    ·
                      refine ⟨1952419816126286623563437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5206452843003430996169165 1952419816126286623563437)
                      ·
                        rfl

theorem cell23_3802324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3802324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802324 prefixEnd_3802324 := by exact prefixLift 3802324
  have htrace : WordTrace (prefixWord ++ tailWord_3802324) baseStart_3802324 baseEnd_3802324 := by
    simpa [prefixWord, tailWord_3802324, baseEnd_3802324] using wordTrace_append hprefix tailTrace_3802324
  have hstable : (prefixWord ++ tailWord_3802324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802324).length < 2 ^ (prefixWord ++ tailWord_3802324).sum := by decide
  have hdescent : baseEnd_3802324 < baseStart_3802324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802336 : List Nat := [2, 1, 1, 3, 1, 4, 2, 4, 5]
def baseStart_3802336 : Nat := 118140960795 + 3802336 * 2 ^ 59
def prefixEnd_3802336 : Nat := 4983230072969 + 3 ^ 40 * 3802336 * 2
def baseEnd_3802336 : Nat := 216936219766015619623709

theorem tailTrace_3802336 : CollatzResearch.WordTrace tailWord_3802336 prefixEnd_3802336 216936219766015619623709 := by
  unfold tailWord_3802336
  simp only [CollatzResearch.WordTrace]
  refine ⟨69341293576396767066773431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92455058101862356089031241 69341293576396767066773431)
  ·
    refine ⟨104011940364595150600160147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69341293576396767066773431 104011940364595150600160147)
    ·
      refine ⟨156017910546892725900240221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104011940364595150600160147 156017910546892725900240221)
      ·
        refine ⟨58506716455084772212590083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156017910546892725900240221 58506716455084772212590083)
        ·
          refine ⟨87760074682627158318885125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58506716455084772212590083 87760074682627158318885125)
          ·
            refine ⟨16455014002992592184790961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87760074682627158318885125 16455014002992592184790961)
            ·
              refine ⟨12341260502244444138593221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16455014002992592184790961 12341260502244444138593221)
              ·
                refine ⟨2313986344170833275986229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12341260502244444138593221 2313986344170833275986229)
                ·
                  refine ⟨216936219766015619623709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2313986344170833275986229 216936219766015619623709)
                  ·
                    rfl

theorem cell23_3802336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 5].length) (baseStart_3802336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3802336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3802336 prefixEnd_3802336 := by exact prefixLift 3802336
  have htrace : WordTrace (prefixWord ++ tailWord_3802336) baseStart_3802336 baseEnd_3802336 := by
    simpa [prefixWord, tailWord_3802336, baseEnd_3802336] using wordTrace_append hprefix tailTrace_3802336
  have hstable : (prefixWord ++ tailWord_3802336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802336).length < 2 ^ (prefixWord ++ tailWord_3802336).sum := by decide
  have hdescent : baseEnd_3802336 < baseStart_3802336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
